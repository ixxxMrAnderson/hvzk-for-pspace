#include "emp-tool/emp-tool.h"
#include "emp-zk/emp-zk-arith/emp-zk-arith.h"

struct Verifier {
    u64 time_duration = 0;
    u64 time_last = 0;
    
    Array_dyn<Expr> exprs;
    Expr_free expr_free;
    s64 n_variables;
    u8 expr_flags = 0;
    
    Array_dyn<Assignment> assignments; // should not be modified directly, call assignment_create
    
    struct Assertion {
        u32 assignment;
        Commitment* value;
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

u32 assignment_create(Verifier* veri, Prover* prover, Assignment assign) {
    array_push_back(&veri->assignments, assign);
    u32 index = veri->assignments.size-1;
    prover_assignment_set(prover, index, assign);
    return index;
}

auto duplicate_assertion_from(
    Verifier* veri,
    Prover* prover,
    u32 expr_from,
    u32 expr_into,
    Commitment* value=nullptr,
    u16 set_var=0,
    ffe set_value=ffe::make_invalid()
) {
    u32 assign_old = veri->assertions[expr_from][0].assignment;
    u32 assign_new;
    if (set_var) {
        assign_new = assignment_create(veri, prover, {assign_old, set_var, set_value});
    } else {
        assign_new = assign_old;
    }
    array_push_back(&veri->assertions[expr_into], {assign_new, value});
    return &veri->assertions[expr_into].back();
}

// Given the equation y = op(x_0, x_1) where x_var has value x and y is given, compute the number of solutions x_{1-var} (2 for infinite). If the solution is unique, write it into out_x.
u8 _op_invert(u8 op, u8 var, Commitment* x, Commitment* y, Commitment** out_x, int party, u8 type, u8 expr_flag) {
    Coeff_2d coeff = expr_op_coefficients_get(op);
    
    Commitment* b = Commit(coeff.c[0], PUBLIC, type)->add(x->mult(Commit(coeff.c[1+var], PUBLIC, type)));
    Commitment* a = Commit(coeff.c[2-var], PUBLIC, type)->add(x->mult(Commit(coeff.c[3], PUBLIC, type)));

    if (a->reveal() == 0) return b->add(y->negate())->reveal() == 0 ? 2 : 0;
    ffe k;
    if (party == ALICE) {
        ffe yf(y->revealALICE()), bf(b->revealALICE()), af(a->revealALICE());
        k = (yf - bf) / af;
        // format_print("-----------a=%d, b=%d, y=%d, k=%d--------\n", af.x, bf.x, yf.x, k.x);
    }
    *out_x = Commit(k.x, ALICE, type);
    // format_print("-----------a2=%d, b2=%d, y2=%d, k2=%d--------\n", a.reveal(), b.reveal(), y.reveal(), out_x->reveal());
    y->CommitEqual(b->add(a->mult(*out_x)));
    // printf("out op_invert\n");
    return 1;
}

bool _verifier_fail(bool verbose) {
    // NOTE: This function is mostly a breakpoint target.
    if (verbose) {
        printf("  Prover failed challenge.\n");
    }
    return 0;
}

void _assertion_print(Verifier* veri, s64 a_it, Verifier::Assertion a, Array_t<u32> freevars) {
    printf("    %lld: %16llx = [", a_it, a.value->reveal());
    for (s64 i = 0; i < freevars.size; ++i) {
        if (i) printf(", ");
        printf("x%u=%llx", freevars[i], assignment_get(veri->assignments, a.assignment, freevars[i]).x);
    }
    printf("]\n");
}

bool sumcheck(Verifier* veri, Prover* prover, BoolIO<NetIO>* io, int party, u8 type = Commitment::VOLE) {
    bool verbose = veri->debug_flags & Verifier::DEBUG_SUMCHECK_LOG;

    // veri->time_last = os_now();
    
    // Ask the prover how many satisfying assignments for the root exist

    u32 root = veri->exprs.size - 1;
    u32 root_assign = -1;
    ffe half = ffe{2}.inv();
    for (u32 var: veri->expr_free.get(root)) {
        root_assign = assignment_create(veri, prover, {root_assign, var, half});
    }
    
    Commitment* result;

    {
    // veri->time_duration += os_now() - veri->time_last;
    auto poly = prover_evaluate(prover, root, root_assign, party, type);
    // TODO: write evaluation of poly[2]
    // veri->time_last = os_now();
    // assert(poly.is_constant());

    // result = poly.c;
    // format_print("fk1\n");
    // cout << typeid(poly[2]).name() << endl;
    // result = poly[2]->mult((ffe::pow2(veri->n_variables)).x);
    // format_print("fk2\n");
    array_push_back(&veri->assertions[root], {root_assign, poly[2]});}

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
        case Expr::BINOP:   return expr.binop.child0 > expr.binop.child1? expr.binop.child0 : expr.binop.child1;
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
            // printf("    %llx / 2**%llx = %llx\n", result->reveal(), root_freevars.size, veri->assertions[root].back().value->reveal());
        }
    }
    
    // Now verify
    
    Array_dyn<ffe> temp_freevals;
    defer { array_free(&temp_freevals); };
    expr_print(veri->exprs);

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
            
            ffe r = ffe(HIGH64(io->get_hash_block()));
            
            if (verbose) {
                printf("    assignments differ on variable x%u\n", i_var);
                printf("    set x%u as free variable, query the resulting univariate polynomials\n", i_var);
            }

            for (s64 j = 0; j < arr.size; ++j) {
                // variable i is a free variable
                u32 j_assign = assignment_create(veri, prover, {arr[j].assignment, i_var, ffe::make_invalid()});
                
                // veri->time_duration += os_now() - veri->time_last;
                auto poly = prover_evaluate(prover, expr_it, j_assign, party, type);
                
                // TODO: write evaluation of poly[1] and poly[2] (?)
                // veri->time_last = os_now();
                if (verbose) {
                    printf("      PROVER: assertion %lld <- ", j);
                    CommittedPoly_print(poly);
                    puts("");
                }
                
                // if (not poly.is_linear()) {
                //     if (verbose) printf("    polynomial is not linear\n");
                //     return _verifier_fail(verbose);
                // }
                ffe j_value_i = assignment_get(veri->assignments, arr[j].assignment, i_var);
                poly[1]->mult(j_value_i.x)->add(poly[2])->CommitEqual(arr[j].value); // HVZK: Verifier checks this relation via the homomorphism of commitments
                // HVZK: Verifier calculates the new commitment homomorphically
                arr[j].assignment = assignment_create(veri, prover, {arr[j].assignment, i_var, r}); // assign the random value
                arr[j].value = poly[1]->mult(r.x)->add(poly[2]);
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
            a.value->CommitEqual(arr[j].value);
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
            a.value->CommitEqual((uint64_t)should);
        } break;
        case Expr::VAR: { // HVZK: Verifier checks the commitment commit to value of 'val'
            assert(freevars.size == 1 and freevars[0] == expr.var.var);
            if (verbose) {
                printf("  atomic expression, evaluate directly\n"); 
            }
            ffe val = assignment_get(veri->assignments, a.assignment, expr.var.var);
            a.value->CommitEqual((uint64_t)val.x);
        } break;
            
        case Expr::PARTIAL: {
            auto e = expr.partial;
            duplicate_assertion_from(veri, prover, expr_it, e.child, a.value, e.var, e.val);
            if (verbose) {
                printf("  add x%d:=%llx to assignment; assert for node %u\n", e.var, e.val.x, e.child);
            }
        } break;
            
        case Expr::RENAME: {
            auto e = expr.rename;
            u32 assign = a.assignment;
            for (u16 i = 0; i < e.count; ++i) {
                ffe val = assignment_get(veri->assignments, assign, e.var_to + i);
                assign = assignment_create(veri, prover, {assign, (u32)(e.var_from+i), val});
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
            auto* aout = duplicate_assertion_from(veri, prover, expr_it, e.child(c));
            if (verbose) printf("  Query for argument %d (expression %u) under above assignment\n", (int)c, e.child(c));
            

            // veri->time_duration += os_now() - veri->time_last;
            auto p = prover_evaluate(prover, e.child(c), aout->assignment, party, type);
            
            aout->value = p[2]; // HVZK: Prover commits to the value of 'p.c'
            if (verbose) printf("    PROVER: argument %d <- %llx\n", (int)c, p[2]->reveal());

            // Now derive the constraint for the smaller child

            Commitment* k; // HVZK: Prover commits to the value of 'k' and prove the relation in ZK (?)
            u8 count = _op_invert(e.op, c, p[2], a.value, &k, party, type, veri->expr_flags);
            Coeff_2d coeff = expr_op_coefficients_get(e.op);
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
                    printf("  argument %d must be %llx\n", 1-c, k->reveal());
                    printf("  add assertions to both %u and %u\n", e.child0, e.child1);
                }
                duplicate_assertion_from(veri, prover, expr_it, e.child(1-c), k);
            }
        } break;
            
        case Expr::DEGREE: {
            auto e = expr.degree;
            if (verbose) printf("  Set x%d as free variable in %u, query the resulting univariate polynomial\n", e.var, e.child);
            ffe e_var_value = assignment_get(veri->assignments, a.assignment, e.var);
            u32 assign = assignment_create(veri, prover, {a.assignment, e.var, ffe::make_invalid()});

            // veri->time_duration += os_now() - veri->time_last;
            auto p = prover_evaluate(prover, e.child, assign, party, type);
            // veri->time_last = os_now();
            if (verbose) {
                printf("    PROVER: <- ");
                CommittedPoly_print(p);
                puts("");
            }
            // format_print("---------------%d\n", p[0]->add(p[1])->mult(e_var_value.x)->add(p[2])->add(a.value->negate())->reveal());
            uint64_t ra=p[0]->reveal(), rb=p[1]->reveal(), rc=p[2]->reveal();
            ffe fa(p[0]->reveal()), fb(p[1]->reveal()), fc(p[2]->reveal());
            // if ((ra+rb)*e_var_value.x+rc!=a.value->reveal()) return 0;
            if ((fa+fb) * e_var_value + fc != ffe(a.value->reveal())) {
                u128 z = 1<<12;
                printf("%llu\n", z);
                printf("ffe wrong\n");
                return 0;
            }
            ((p[0]->add(p[1]))->mult(e_var_value.x)->add(p[2]))->CommitEqual(a.value);

            // HVZK: Prover homomorphically computes the commitment of 'p(r)'
            ffe r = ffe(HIGH64(io->get_hash_block()));
            if (verbose) {
                printf("  re-assign x%d to %llx, add assertion to %u\n", e.var, r.x, e.child);
            }
            duplicate_assertion_from(veri, prover, expr_it, e.child, p[0]->mult(r.x)->add(p[1])->mult(r.x)->add(p[2]), e.var, r);
        } break;

        // TODO: how to link k?
            
        default: assert_false;
        }
    }

    // veri->time_duration += os_now() - veri->time_last;
    return 1;
}


// Name    // Instance size // Solving time // Proving time // Byte sent
// TRUE10  // 9.83KB        // 21.45ms      // 618.70ms     // 3.18MB
// TRUE15  // 28.90KB       // 123.07ms     // 1.12s        // 6.21MB
// TRUE20  // 69.88KB       // 2.22s        // 9.52s        // 14.07MB
// TRUE25  // 126.63KB      // 43.53s       // 3m18s        // 27.21MB
// FALSE10 // 9.80KB        // 19.76ms      // 591.92ms     // 3.18MB
// FALSE15 // 28.93KB       // 124.99ms     // 1.09s        // 6.20MB
// FALSE20 // 69.94KB       // 2.24s        // 9.26s        // 14.12MB
// FALSE25 // 126.54KB      // 41.92s       // 3m18s        // 27.12MB