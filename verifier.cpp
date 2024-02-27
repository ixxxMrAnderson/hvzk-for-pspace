
struct Verifier {
    Prover* prover;
    
    u64 time_duration = 0;
    u64 time_last = 0;
    
    Array_dyn<Expr> exprs;
    Expr_free expr_free;
    s64 n_variables;
    
    Array_dyn<Assignment> assignments; // should not be modified directly, call _verifier_assignment_create
    
    struct Assertion {
        u32 assignment;
        ffe value;
    };
    Array_t<Array_dyn<Assertion>> assertions;
    Array_t<ffe> temp_assignment;
    
    Rng rng;

    enum Debug_flags: u8 {
        DEBUG_DRAW_EXPR = 1,
        DEBUG_DRAW_QBC = 2,
        DEBUG_SUMCHECK_LOG = 4,
        DEBUG_SMALL_NUMBERS = 8,
        NO_VERIFY = 16,
    };
    u8 debug_flags = 0;
};

void verifier_free(Verifier* veri) {
    array_free(&veri->exprs);
    expr_free_free(&veri->expr_free);
    for (auto& i: veri->assertions) {
        array_free(&i);
    }
    array_free(&veri->assertions);
    array_free(&veri->temp_assignment);
}

// Convert to polynomial expression
void _convert_to_poly(Verifier* veri, Array_t<Expr> exprs) {
    Array_t<u32> expr_map = array_create<u32>(exprs.size);
    defer { array_free(&expr_map); };
    
    expr_free_compute(&veri->expr_free, exprs);
    
    for (s64 i = 0; i < exprs.size; ++i) {
        Expr expr = exprs[i];
        switch (expr.type) {
        case Expr::FALSE:
        case Expr::TRUE:
        case Expr::VAR:
            array_push_back(&veri->exprs, expr);
            break;
        case Expr::BINOP: {
            expr.binop.child0 = expr_map[expr.binop.child0];
            expr.binop.child1 = expr_map[expr.binop.child1];
            array_push_back(&veri->exprs, expr);
            auto arr = veri->expr_free.get(i);
            for (s64 j = arr.size-1; j >= 0; --j) {
                Expr expr_d = Expr::make_degree(arr[j], veri->exprs.size-1);
                array_push_back(&veri->exprs, expr_d);
            }
        } break;
        case Expr::PARTIAL:
            expr.partial.child = expr_map[expr.partial.child];
            array_push_back(&veri->exprs, expr);
            break;
        case Expr::RENAME:
            expr.rename.child = expr_map[expr.rename.child];
            array_push_back(&veri->exprs, expr);
            break;
        default: assert_false;
        }
        expr_map[i] = veri->exprs.size-1;
    }

    array_resize(&veri->expr_free.expr_free, veri->exprs.size);
    
    s64 i_in = expr_map.size-1;
    for (s64 i = veri->exprs.size-1; i >= 0; --i) {
        if (i_in > 0 and expr_map[i_in-1] == i) --i_in;
        veri->expr_free.expr_free[i] = veri->expr_free.expr_free[i_in];
    }
}

// n_variables is the number of free variables in the root expression. By default, we consider only the variables that appear in the circuit, but if e.g. you model some finite-state system and the configuraion contains variables that are not used (and thus do not appear in the expression), you can pass the true number here. 
void verifier_init(Verifier* veri, Prover* prover, Array_t<Expr> exprs_qbc, s64 n_variables=-1, u8 debug_flags=0) {
    veri->prover = prover;
    veri->debug_flags = debug_flags;
    
    veri->expr_free.expr_free.size = 0;
    veri->expr_free.expr_free_data.size = 0;

    if (veri->debug_flags & Verifier::DEBUG_DRAW_QBC) {
        mkdir("out_graphs", 0775);
        expr_draw(exprs_qbc, "out_graphs/qbc.dot"_arr);
        auto _ = system("dot -Tsvg out_graphs/qbc.dot > out_graphs/qbc.svg");
    }

    _convert_to_poly(veri, exprs_qbc);
    assert(veri->assertions.data == nullptr);
    veri->assertions = array_create<Array_dyn<Verifier::Assertion>>(veri->exprs.size);

    if (veri->debug_flags & Verifier::DEBUG_DRAW_EXPR) {
        mkdir("out_graphs", 0775);
        expr_draw(veri->exprs, "out_graphs/expr.dot"_arr);
        auto _ = system("dot -Tsvg out_graphs/expr.dot > out_graphs/expr.svg");
    }

    if (n_variables == -1) {
        n_variables = veri->expr_free.get(veri->exprs.size-1).size;
    }
    assert(n_variables >= veri->expr_free.get(veri->exprs.size-1).size);
    veri->n_variables = n_variables;
    
    s64 max_var = 0;
    for (Expr expr: veri->exprs) {
        if (expr.type == Expr::VAR and max_var < expr.var.var) {
            max_var = expr.var.var;
        }
    }
    veri->temp_assignment = array_create<ffe>(max_var+1);
}

Polynomial _verifier_evaluate(Verifier* veri, u32 expr, u32 assignment) {
    veri->time_duration += os_now() - veri->time_last;
    auto result = prover_evaluate(veri->prover, expr, assignment);
    veri->time_last = os_now();
    return result;
}

u32 _verifier_assignment_create(Verifier* veri, Assignment assign) {
    array_push_back(&veri->assignments, assign);
    u32 index = veri->assignments.size-1;
    prover_assignment_set(veri->prover, index, assign);
    return index;
}

auto _verifier_duplicate_assertion_from(
    Verifier* veri,
    u32 expr_from,
    u32 expr_into,
    ffe value=ffe::make_invalid(),
    u16 set_var=0,
    ffe set_value=ffe::make_invalid()
) {
    u32 assign_old = veri->assertions[expr_from][0].assignment;
    u32 assign_new;
    if (set_var) {
        assign_new = _verifier_assignment_create(veri, {assign_old, set_var, set_value});
    } else {
        assign_new = assign_old;
    }
    array_push_back(&veri->assertions[expr_into], {assign_new, value});
    return &veri->assertions[expr_into].back();
}

// Given the equation y = op(x_0, x_1) where x_var has value x and y is given, compute the number of solutions x_{1-var} (2 for infinite). If the solution is unique, write it into out_x.
u8 _op_invert(u8 op, u8 var, ffe x, ffe y, ffe* out_x) {
    Coeff_2d coeff = expr_op_coefficients_get(op);

    // Transform the equation to a*z + b, where a,b are constants
    ffe b = ffe {coeff.c[0]}     + ffe {coeff.c[1+var]} * x;
    ffe a = ffe {coeff.c[2-var]} + ffe {coeff.c[3]}     * x;

    if (a.x == 0) return b == y ? 2 : 0;
    if (out_x) *out_x = (y - b) / a;
    return 1;
}

s64 _verifier_fail(bool verbose) {
    // NOTE: This function is mostly a breakpoint target.
    if (verbose) {
        printf("  Prover failed challenge.\n");
    }
    return -1;
}

void _assertion_print(Verifier* veri, s64 a_it, Verifier::Assertion a, Array_t<u32> freevars) {
    printf("    %lld: %16llx = [", a_it, a.value.x);
    for (s64 i = 0; i < freevars.size; ++i) {
        if (i) printf(", ");
        printf("x%u=%llx", freevars[i], assignment_get(veri->assignments, a.assignment, freevars[i]).x);
    }
    printf("]\n");
}

ffe _verifier_random(Verifier* veri) {
    if (veri->debug_flags & Verifier::DEBUG_SMALL_NUMBERS) {
        return veri->rng.u64_uni() % 11;
    } else {
        return veri->rng.u64_uni();
    }
}

s64 verifier_sumcheck(Verifier* veri) {
    bool verbose = veri->debug_flags & Verifier::DEBUG_SUMCHECK_LOG;
    
    // Let the prover calculate the result
    prover_calculate(veri->prover, veri->exprs);

    veri->time_last = os_now();
    
    // Ask the prover how many satisfying assignments for the root exist
    u32 root = veri->exprs.size - 1;
    u32 root_assign = -1;
    ffe half = ffe{2}.inv();
    for (u32 var: veri->expr_free.get(root)) {
        root_assign = _verifier_assignment_create(veri, {root_assign, var, half});
    }
    
    s64 result;
    {auto poly = _verifier_evaluate(veri, root, root_assign);
    assert(poly.is_constant());
    result = (poly.c * ffe::pow2(veri->n_variables)).x;
    array_push_back(&veri->assertions[root], {root_assign, poly.c});}
    
    // HVZK: commit to the value of variable 'result'
    if (verbose) {
        printf("Prover claims %lld satisfying assignment%s\n", result, &"s"[result == 1]);
    }

    if (veri->debug_flags & Verifier::NO_VERIFY) {
        return result; 
    }

    // Compute the evaluation order
    Array_t<u32> exprs_sorted = array_create<u32>(veri->exprs.size);
    defer { array_free(&exprs_sorted); };
    for (s64 i = 0; i < veri->exprs.size; ++i) {
        exprs_sorted[i] = i;
    }
    array_sort_counting(&exprs_sorted, [&veri](u32 expr_it) {
        auto expr = veri->exprs[expr_it];
        switch (expr.type) {
        case Expr::FALSE:
        case Expr::TRUE:
        case Expr::VAR:     return expr_it;
        case Expr::BINOP:   return std::max(expr.binop.child0, expr.binop.child1);
        case Expr::PARTIAL: return expr.partial.child;
        case Expr::DEGREE:  return expr.degree.child;
        case Expr::RENAME: return expr.rename.child;
        default: assert_false;
        }
    }, exprs_sorted.size);

    if (verbose) {
        auto root_freevars = veri->expr_free.get(root);
        printf("Add initial assertion to root %u\n", root);
        if (root_freevars.size == 0) {
            printf("  formula is closed, use empty assignment\n");
        } else {
            printf("  formula has %lld free variable%s: ", root_freevars.size, &"s"[root_freevars.size == 1]);
            printf("x%u", root_freevars[0]);
            for (u32 var: array_subarray(root_freevars, 1)) printf(", x%u", var);
            puts("");
            printf("  assign 1/2 to each free variable\n");
            printf("  scale claimed count by 1/2 for each free variable\n");
            printf("    %llx / 2**%llx = %llx\n", result, root_freevars.size, veri->assertions[root].back().value.x);
        }
    }
    
    // Now verify
    
    Array_dyn<ffe> temp_freevals;
    defer { array_free(&temp_freevals); };

    for (s64 expr_it_it = veri->exprs.size-1; expr_it_it >= 0; --expr_it_it) {
        u32 expr_it = exprs_sorted[expr_it_it];
        auto arr = veri->assertions[expr_it];
        auto freevars = veri->expr_free.get(expr_it);
        if (arr.size == 0) continue;

        if (verbose) {
            printf("\nChecking %lld assertion%s at expression ", arr.size, &"s"[arr.size == 1]);
            expr_print_one(expr_it, veri->exprs[expr_it]);
            puts("");
            for (s64 a_it = 0; a_it < arr.size; ++a_it) {
                _assertion_print(veri, a_it, arr[a_it], freevars);
            }

            if (arr.size > 1) {
                puts("  Reducing multiple assignments to one.");
            }
        }

        // Reduce checking multiple assignments to only one
        s64 first_check_var = arr.size > 1 ? 0 : freevars.size;
        for (s64 i = first_check_var; i < freevars.size; ++i) {
            u32 i_var = freevars[i];
            
            // Do the assignments differ on variable i?
            ffe val = assignment_get(veri->assignments, arr[0].assignment, i_var);
            bool different = false;
            for (s64 j = 1; j < arr.size; ++j) {
                if (assignment_get(veri->assignments, arr[j].assignment, i_var) != val) {
                    different = true;
                    break;
                }
            }
            if (not different) {
                if (verbose and arr.size > 1) {
                    printf("    assignments match on variable x%u, skip\n", i_var);
                }
                continue;
            }

            // Pick a random value
            // Technically speaking, we generate the random number only after talking to Prover, but it is deterministic anyway and this way we do not have to store the polynomials sent by Prover.
            ffe r = _verifier_random(veri);
            
            if (verbose) {
                printf("    assignments differ on variable x%u\n", i_var);
                printf("    set x%u as free variable, query the resulting univariate polynomials\n", i_var);
            }

            for (s64 j = 0; j < arr.size; ++j) {
                // variable i is a free variable
                u32 j_assign = _verifier_assignment_create(veri, {arr[j].assignment, i_var, ffe::make_invalid()});
                auto poly = _verifier_evaluate(veri, expr_it, j_assign); // HVZK: Prover should commit to this 'poly'
                if (verbose) {
                    printf("      PROVER: assertion %lld <- ", j);
                    polynomial_print(poly);
                    puts("");
                }
                
                if (not poly.is_linear()) {
                    if (verbose) printf("    polynomial is not linear\n");
                    return _verifier_fail(verbose);
                }
                ffe j_value_i = assignment_get(veri->assignments, arr[j].assignment, i_var);
                if (poly(j_value_i) != arr[j].value) { // HVZK: Verifier checks this relation via the homomorphism of commitments
                    if (verbose) {
                        printf("    polynomial does not match assertion:\n");
                        printf("    is %llx, should be %llx\n", poly(j_value_i).x, arr[j].value.x);
                    }
                    return _verifier_fail(verbose);
                }
                // HVZK: Verifier calculates the new commitment homomorphically
                arr[j].assignment = _verifier_assignment_create(veri, {arr[j].assignment, i_var, r}); // assign the random value
                arr[j].value = poly(r);
            }
            
            if (verbose) {
                printf("    re-assign x%u to %llx\n", i_var, r.x);
            }
        }

        if (verbose and arr.size > 1) {
            printf("  One assertion remains, proceed to verify expression\n");
            _assertion_print(veri, 0, arr[0], freevars);
        }
        
        Verifier::Assertion a = arr[0];
        // HVZK: Verifier checks each two commitments commit to the same value
        for (s64 j = 1; j < arr.size; ++j) {
            if (arr[j].value != a.value) {
                if (verbose) {
                    printf("    assertions are contradictory\n");
                    printf("    0 is %llx, but %lld is %llx\n", a.value.x, j, arr[j].value.x);
                }
                return _verifier_fail(verbose);
            }
        }
        
        // Check the one assignment
        auto expr = veri->exprs[expr_it];
        switch (expr.type) {
        case Expr::FALSE:
        case Expr::TRUE: { // HVZK: Verifier checks the commitment commit to value TRUE
            s64 should = expr.type == Expr::TRUE;
            if (verbose) {
                printf("  atomic expression, evaluate directly\n"); 
            }
            if (a.value.x != should) {
                return _verifier_fail(verbose);
                if (verbose) {
                    printf("  expr is constant %lld, but prover claims %llx\n", should, a.value.x);
                }
            }
        } break;
        case Expr::VAR: { // HVZK: Verifier checks the commitment commit to value of 'val'
            assert(freevars.size == 1 and freevars[0] == expr.var.var);
            if (verbose) {
                printf("  atomic expression, evaluate directly\n"); 
            }
            ffe val = assignment_get(veri->assignments, a.assignment, expr.var.var);
            if (a.value != val) {
                if (verbose) {
                    printf("  variable is assigned %llx, but value %llx is asserted\n", val.x, a.value.x);
                }
                return _verifier_fail(verbose);
            }
        } break;
            
        case Expr::PARTIAL: {
            auto e = expr.partial;
            _verifier_duplicate_assertion_from(veri, expr_it, e.child, a.value, e.var, e.val);
            if (verbose) {
                printf("  add x%d:=%llx to assignment; assert for node %u\n", e.var, e.val.x, e.child);
            }
        } break;
            
        case Expr::RENAME: {
            auto e = expr.rename;
            u32 assign = a.assignment;
            for (u16 i = 0; i < e.count; ++i) {
                ffe val = assignment_get(veri->assignments, assign, e.var_to+i);
                assign = _verifier_assignment_create(veri, {assign, (u32)(e.var_from+i), val});
            }
            array_push_back(&veri->assertions[e.child], {assign, a.value});

            if (verbose) {
                if (e.count == 1) {
                    printf("  rename variable x%u to x%u in the assignment; assert for node %u\n", e.var_to, e.var_from, e.child);
                } else {
                    printf("  rename variables x%u,...,x%u to x%u,...,x%u in the assignment; assert for node %u\n", e.var_to, e.var_to+e.count-1, e.var_from, e.var_from+e.count-1, e.child);
                }
            }
        } break;
                        
        case Expr::BINOP: {
            auto e = expr.binop;
            // First evaluate the larger child
            u8 c = e.child0 < e.child1;
            auto* aout = _verifier_duplicate_assertion_from(veri, expr_it, e.child(c));
            if (verbose) printf("  Query for argument %d (expression %u) under above assignment\n", (int)c, e.child(c));
            auto p = _verifier_evaluate(veri, e.child(c), aout->assignment);
            assert(p.is_constant());
            aout->value = p.c; // HVZK: Prover commits to the value of 'p.c'
            if (verbose) printf("    PROVER: argument %d <- %llx\n", (int)c, p.c.x);

            // Now derive the constraint for the smaller child
            
            ffe k; // HVZK: Prover commits to the value of 'k' and prove the relation in ZK (?)
            u8 count = _op_invert(e.op, c, p.c, a.value, &k);
            if (count == 0) {
                if (verbose) printf("  linear equation has no solution\n");
                return _verifier_fail(verbose);
            } else if (count == 2) {
                if (verbose) {
                    printf("  argument %d is redundant\n", 1-c);
                    printf("  add assertion to %u\n", e.child(c));
                }
            } else {
                if (verbose) {
                    printf("  argument %d must be %llx\n", 1-c, k.x);
                    printf("  add assertions to both %u and %u\n", e.child0, e.child1);
                }
                _verifier_duplicate_assertion_from(veri, expr_it, e.child(1-c), k);
            }
        } break;
            
        case Expr::DEGREE: {
            auto e = expr.degree;
            if (verbose) printf("  Set x%d as free variable in %u, query the resulting univariate polynomial\n", e.var, e.child);
            ffe e_var_value = assignment_get(veri->assignments, a.assignment, e.var);
            u32 assign = _verifier_assignment_create(veri, {a.assignment, e.var, ffe::make_invalid()});
            auto p = _verifier_evaluate(veri, e.child, assign); // HVZK: Prover commit to the value of 'p.a', 'p.b', and 'p.c'
            if (verbose) {
                printf("    PROVER: <- ");
                polynomial_print(p);
                puts("");
            }
            
            if (p.degree_reduced()(e_var_value) != a.value) { // HVZK: Prover homomorphically check whether '(p.a + p.b) * e_var_value + p.c = a.value'
                if (verbose) {
                    printf("  polynomial does not evaluate to assertion\n");
                    printf("  is %llx, should be %llx\n", p.degree_reduced()(e_var_value).x, a.value.x);
                }
                return _verifier_fail(verbose);
            }

            // HVZK: Prover homomorphically computes the commitment of 'r'
            ffe r = _verifier_random(veri); // generate random value
            if (verbose) {
                printf("  re-assign x%d to %llx, add assertion to %u\n", e.var, r.x, e.child);
            }
            _verifier_duplicate_assertion_from(veri, expr_it, e.child, p(r), e.var, r);
        } break;
            
        default: assert_false;
        }
    }

    veri->time_duration += os_now() - veri->time_last;
    return result;
}
