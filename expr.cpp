
struct Expr {
    enum Type: u8 {
        INVALID, FALSE, TRUE, VAR, BINOP, PARTIAL, DEGREE, RENAME
    };
    enum Type_binop: u8 {
        // the order is not arbitrary, but encodes the truth-table
        // the result of evaluating entry i on x,y is written in bit x+2*y of i
        // i.e. NIMPLY == 2 == 0b0010, so 0 NIMPLIED 1 is bit 1 of 0010, which is 1
        FALSE_OP, NOR, NIMPLY, NOT_X, NIMPLIED, NOT_Y, XOR,
        NAND, AND, XNOR, Y, IMPLIED, X, IMPLY, OR, TRUE_OP,

        NOT_X_OR_Y = IMPLY,
        X_OR_NOT_Y = IMPLIED,
        NOT_X_AND_Y = NIMPLIED,
        X_AND_NOT_Y = NIMPLY,
    };
    static constexpr char const* binop_names[] = {
        "FALSE", "NOR", "NIMPLY", "NOT X", "NIMPLIED", "NOT Y", "XOR",
        "NAND", "AND", "XNOR", "Y", "IMPLIED", "X", "IMPLY", "OR", "TRUE"
    };
    static constexpr char const* binop_names_uni[] = {
        u8"⊥", u8"⊽", u8"↛", u8"¬x", u8"↚", u8"¬y", u8"⊕",
        u8"⊼", u8"∧", u8"↔", u8"Y", u8"←", u8"X", u8"→", u8"∨", u8"⊤"
    };
    

    struct Expr_var {
        u8 type;
        u16 var; // 1-based index; 0 is invalid!
    };
    struct Expr_binop {
        u8 type, op;
        u32 child0, child1;
        u32& child(u8 c) {
            assert(c < 2);
            return c ? child1 : child0;
        }
    };
    struct Expr_partial {
        u8 type;
        u16 var;
        u32 child;
        ffe val;
    };
    struct Expr_degree {
        u8 type;
        u16 var;
        u32 child;
    };
    struct Expr_rename {
        u8 type;
        u16 var_from, var_to;
        u32 child;
        u16 count;
    };
    
    Expr(u8 type = INVALID): type{type} {}
    explicit Expr(Expr_var     var):     var    {var}     {}
    explicit Expr(Expr_binop   binop):   binop  {binop}   {}
    explicit Expr(Expr_partial partial): partial{partial} {}
    explicit Expr(Expr_degree  degree):  degree {degree}  {}
    explicit Expr(Expr_rename  rename):  rename {rename}  {}
    
    static Expr make_var(u16 var) { assert(var); return Expr {Expr_var {VAR, var}}; }
    static Expr make_binop(u8 op, u32 child0, u32 child1) { return Expr {Expr_binop {BINOP, op, child0, child1}}; }
    static Expr make_partial(u16 var, u32 child, ffe val) { assert(var); return Expr {Expr_partial {PARTIAL, var, child, val}}; }
    static Expr make_degree(u16 var, u32 child) { assert(var); return Expr {Expr_degree {DEGREE, var, child}}; }
    static Expr make_rename(u16 var_from, u16 var_to, u32 child, u16 count = 1)
        { assert(var_from and var_to); return Expr {Expr_rename {RENAME, var_from, var_to, child, count}}; }
    
    union {
        u8 type;
        Expr_var var;
        Expr_binop binop;
        Expr_partial partial;
        Expr_degree degree;
        Expr_rename rename;
    };
};
constexpr char const* Expr::binop_names[];
constexpr char const* Expr::binop_names_uni[];

struct Expr_free {
    Array_dyn<Offset<u32>> expr_free;
    Array_dyn<u32> expr_free_data;
    Array_t<u32> get(u32 expr_it) {
        return array_suboffset(expr_free_data, expr_free[expr_it]);
    }
};

void expr_free_free(Expr_free* expr_free) {
    array_free(&expr_free->expr_free);
    array_free(&expr_free->expr_free_data);
}

void expr_free_compute(Expr_free* out, Array_t<Expr> exprs) {
    for (Expr expr: array_subarray(exprs, out->expr_free.size)) {
        switch (expr.type) {
        case Expr::FALSE:
        case Expr::TRUE:
            array_push_back(&out->expr_free, {});
            break;
        case Expr::VAR:
            array_push_back(&out->expr_free_data, expr.var.var);
            array_push_back(&out->expr_free, {out->expr_free_data.size-1, 1});
            break;
        case Expr::BINOP: {
            // merge two sorted arrays
            auto off0 = out->expr_free[expr.binop.child0];
            auto off1 = out->expr_free[expr.binop.child1];
            array_reserve(&out->expr_free_data, out->expr_free_data.size + off0.size + off1.size);
            auto arr0 = array_suboffset(out->expr_free_data, off0);
            auto arr1 = array_suboffset(out->expr_free_data, off1);
            
            s64 index = out->expr_free_data.size;
            s64 i = 0, j = 0;
            while (i < arr0.size and j < arr1.size) {
                auto x = arr0[i]; auto y = arr1[j];
                if (x == y) {
                    array_push_back(&out->expr_free_data, x); ++i; ++j;
                } else if (x < y) {
                    array_push_back(&out->expr_free_data, x); ++i;
                } else {
                    array_push_back(&out->expr_free_data, y); ++j;
                }
            }
            array_append(&out->expr_free_data, array_subarray(arr0, i));
            array_append(&out->expr_free_data, array_subarray(arr1, j));
            
            auto off = array_makeoffset(out->expr_free_data, index);
            if (off.size == arr0.size) {
                off = out->expr_free[expr.binop.child0];
                out->expr_free_data.size = index;
            } else if (off.size == arr1.size) {
                off = out->expr_free[expr.binop.child1];
                out->expr_free_data.size = index;
            }
            array_push_back(&out->expr_free, off);
        } break;
            
        case Expr::PARTIAL: {
            auto off = out->expr_free[expr.partial.child];
            array_reserve(&out->expr_free_data, out->expr_free_data.size + off.size);
            auto arr = array_suboffset(out->expr_free_data, off);
            s64 index = out->expr_free_data.size;
            for (u32 x: arr) {
                if (x == expr.partial.var) continue;
                array_push_back(&out->expr_free_data, x);
            }
            array_push_back(&out->expr_free, array_makeoffset(out->expr_free_data, index));
        } break;

        case Expr::DEGREE:
            array_push_back(&out->expr_free, out->expr_free[expr.degree.child]);
            break;

        case Expr::RENAME: {
            auto off = out->expr_free[expr.rename.child];
            array_reserve(&out->expr_free_data, out->expr_free_data.size + off.size);
            auto arr = array_suboffset(out->expr_free_data, off);
            s64 index = out->expr_free_data.size;
            for (u32 x: arr) {
                s64 off = (s64)x - expr.rename.var_from;
                if (0 <= off and off < expr.rename.count) {
                    x = expr.rename.var_to + off;
                }
                array_push_back(&out->expr_free_data, x);
            }
            array_push_back(&out->expr_free, array_makeoffset(out->expr_free_data, index));
        } break;
            
        default: assert_false;
        }
    }
}

void expr_print_one(u32 expr_it, Expr expr, FILE* out = stdout) {
    fprintf(stdout, "%u: ", expr_it);
    switch (expr.type) {
    case Expr::FALSE: fprintf(stdout, " FALSE"); break;
    case Expr::TRUE:  fprintf(stdout, " TRUE" ); break;
    case Expr::VAR: fprintf(stdout, " x%d", expr.var.var); break;
    case Expr::BINOP: fprintf(stdout, " %d %s %d", expr.binop.child0, Expr::binop_names[expr.binop.op], expr.binop.child1); break;
    case Expr::PARTIAL: fprintf(stdout, " x%d:=%llx %d", expr.partial.var, expr.partial.val.x, expr.partial.child); break;
    case Expr::DEGREE: fprintf(stdout, " dx%d %d", expr.degree.var, expr.degree.child); break;
    case Expr::RENAME: fprintf(stdout, " x%d/x%d~%d %d", expr.rename.var_from, expr.rename.var_to, expr.rename.count, expr.rename.child); break;
    default: assert_false;
    }
}

void expr_print(Array_t<Expr> exprs, FILE* out = stdout) {
    for (s64 expr_it = 0; expr_it < exprs.size; ++expr_it) {
        expr_print_one(expr_it, exprs[expr_it], out);
        fprintf(stdout, "\n");
    }
}

void expr_draw(Array_t<Expr> exprs, Array_t<u8> path) {
    Array_dyn<u8> out;
    defer { array_free(&out); };
    
    array_printf(&out, "digraph G {\n");
    
    for (s64 expr_it = 0; expr_it < exprs.size; ++expr_it) {
        Expr expr = exprs[expr_it];
        
        switch (expr.type) {
        case Expr::FALSE: array_printf(&out, "%lld [label=\"%lld: F\"];\n", expr_it, expr_it); break;
        case Expr::TRUE:  array_printf(&out, "%lld [label=\"%lld: T\"];\n", expr_it, expr_it); break;
        case Expr::VAR:   array_printf(&out, "%lld [label=\"%lld: x%lld\"];\n", expr_it, expr_it, expr.var.var); break;
        case Expr::BINOP:
            assert(expr.binop.op < 16);
            array_printf(&out, "%lld [label=\"%lld: %s\"];\n", expr_it, expr_it, Expr::binop_names[expr.binop.op]);
            array_printf(&out, "%lld -> %lld;\n", expr_it, expr.binop.child0);
            array_printf(&out, "%lld -> %lld;\n", expr_it, expr.binop.child1);
            break;
        case Expr::PARTIAL:
            array_printf(&out, "%lld [label=\"%lld: x%lld:=%lld\"];\n", expr_it, expr_it, expr.partial.var, expr.partial.val.x);
            array_printf(&out, "%lld -> %lld;\n", expr_it, expr.partial.child);
            break;
        case Expr::DEGREE:
            array_printf(&out, "%lld [label=\"%lld: dx%d\"];\n", expr_it, expr_it, expr.degree.var);
            array_printf(&out, "%lld -> %lld;\n", expr_it, expr.degree.child);
            break;
        case Expr::RENAME:
            array_printf(&out, "%lld [label=\"%lld: x%d/x%d~%d\"];\n", expr_it, expr_it, expr.rename.var_from, expr.rename.var_to, expr.rename.count);
            array_printf(&out, "%lld -> %lld;\n", expr_it, expr.rename.child);
            break;
        default: assert_false;
        }

    }
    array_printf(&out, "}\n");

    array_write_to_file(path, out);
}

namespace Expr_flags {

enum Flags: u8 {
    SKIP_OUTER = 1,
    SIMPLE_QUANTIFIER = 2,
    DEBUG_CHECK_INSTANCE = 4,
};

}

u8 expr_op_flip(u8 op, u8 input) {
    if (input == 0) {
        return (op&10) >> 1 | (op&5) << 1;
    } else if (input == 1) {
        return op >> 2 | (op&3) << 2;
    } else {
        assert_false;
    }
}
Expr expr_make_binop_flip(u8 op, u32 child0, bool flip0, u32 child1, bool flip1) {
    if (flip0) op = expr_op_flip(op, 0);
    if (flip1) op = expr_op_flip(op, 1);
    return Expr::make_binop(op, child0, child1);
}

void expr_reduce(Array_dyn<Expr>* exprs, u8 op, s32* inout_id0, s32 id1) {
    if (*inout_id0 == 0x7fffffff) {
        *inout_id0 = id1;
    } else {
        if (*inout_id0 < 0) { op = expr_op_flip(op, 0); *inout_id0 = -*inout_id0; }
        if (id1        < 0) { op = expr_op_flip(op, 1); id1 = -id1; }
        array_push_back(exprs, Expr::make_binop(op, *inout_id0, id1));
        *inout_id0 = exprs->size-1;
    }
}

void expr_reduce_finalize(Array_dyn<Expr>* exprs, s32* inout_id, bool value_if_empty) {
    if (*inout_id == 0x7fffffff) {
        if (value_if_empty) {
            array_push_back(exprs, {Expr::TRUE});
            *inout_id = exprs->size-1;
        } else {
            *inout_id = 0;
        }
    } else if (*inout_id < 0) {
        array_push_back(exprs, Expr::make_binop(Expr::XNOR, 0, -*inout_id));
        *inout_id = exprs->size-1;
    }
}

u32 expr_make_quant(Array_dyn<Expr>* exprs, u8 op, u32 var, u32 expr_it) {
    u32 last = exprs->size;
    array_append(exprs, {
        Expr::make_partial(var, expr_it, 0),
        Expr::make_partial(var, expr_it, 1),
        Expr::make_binop(op, last, last+1)
    });
    return last+2;
}

void _expr_from_dimacs_simple(Array_dyn<Expr>* exprs, Dimacs dimacs, bool skip_outer) {
    array_push_back(exprs, {Expr::FALSE});
    for (s64 i = 1; i <= dimacs.n_variables; ++i) {
        array_push_back(exprs, Expr::make_var(i));
    }
    
    s32 last_clause = 0x7fffffff;
    for (s64 i = 0; i < dimacs.n_clauses; ++i) {
        s32 last_var = 0x7fffffff;
        for (s32 lit: dimacs.clause(i)) {
            expr_reduce(exprs, Expr::OR, &last_var, lit);
        }
        if (last_var == 0x7fffffff) last_var = 0;
        expr_reduce(exprs, Expr::AND, &last_clause, last_var);
    }
    expr_reduce_finalize(exprs, &last_clause, true);
    if (exprs->size > last_clause+1) exprs->size = last_clause+1;
        
    for (s64 i = dimacs.n_quantifiers-1; i >= skip_outer; --i) {
        u8 op = dimacs.quantifier_types[i] == Dimacs::EXISTS ? Expr::OR : Expr::AND;
        for (s32 var: dimacs.quantifier_vars(i)) {
            last_clause = expr_make_quant(exprs, op, var, last_clause);
        }
    }
}

s32 expr_to_formula(Array_t<Expr> exprs, Dimacs* out_dimacs) {
    s64 offset = out_dimacs->n_variables+1;
    s64 first = 1;
    for (u32 i = 1; i < exprs.size; ++i) {
        Expr e = exprs[i];
        if (e.type == Expr::VAR) {
            assert(e.var.var == i);
            assert(first == i);
            first = i+1;
            continue;
        }
        assert(e.type == Expr::BINOP);
        
        for (u8 xy = 0; xy < 4; ++xy) {
            bool x = xy & 1, y = xy & 2;
            bool z = e.binop.op >> xy & 1;
            u32 v0 = e.binop.child0 < first ? e.binop.child0 : offset + (e.binop.child0 - first);
            u32 v1 = e.binop.child1 < first ? e.binop.child1 : offset + (e.binop.child1 - first);
            u32 v2 = offset + (i - first);
            s32 l0 = x ? v0 : -(s32)v0;
            s32 l1 = y ? v1 : -(s32)v1;
            s32 l2 = z ? v2 : -(s32)v2;
            // (l0 AND l1) IMPLY l2, i.e. -l0 OR -l1 OR l2
            array_append(&out_dimacs->clause_literals, {-l0, -l1, l2});
            array_push_back(&out_dimacs->clauses, out_dimacs->clause_literals.size);
        }
    }
    out_dimacs->n_variables = offset + (exprs.size-1 - first);
    out_dimacs->n_clauses = out_dimacs->clauses.size-1;
    return out_dimacs->n_variables;
}



void _expr_debug_check_instance(Array_t<Expr> exprs, Dimacs dimacs) {
    s64 index = -1;
    for (s64 i = 0; i < exprs.size; ++i) {
        if (exprs[i].type == Expr::PARTIAL) {
            index = i; break;
        }
    }
    if (index == -1) index = exprs.size;
    auto exprs_bc = array_subarray(exprs, 0, index);

    Dimacs out;
    defer { dimacs_free(&out); };
    array_push_back(&out.clauses, 0);

    out.n_variables = dimacs.n_variables;
    s32 f1 = dimacs_to_formula(&dimacs, &out);
    s32 f2 = expr_to_formula(exprs_bc, &out);

    // f1 XOR f2
    array_append(&out.clause_literals, {f1, f2});
    array_push_back(&out.clauses, out.clause_literals.size);
    array_append(&out.clause_literals, {-f1, -f2});
    array_push_back(&out.clauses, out.clause_literals.size);
    out.n_clauses = out.clauses.size-1;

    Array_dyn<u8> out_data;
    defer { array_free(&out_data); };
    
    dimacs_write(&out, &out_data);
    array_write_to_file("check_instance.dimacs"_arr, out_data);

    os_error_panic();
    
    puts("Wrote equivalence check to check_instance.dimacs");
}

void _expr_from_dimacs_complicated(Array_dyn<Expr>* exprs, Dimacs dimacs, bool skip_outer) {
    Array_dyn<u32> clusters;
    defer { array_free(&clusters); };

    Expr_free expr_free;
    defer { expr_free_free(&expr_free); };
    
    array_push_back(exprs, {Expr::FALSE});
    for (s64 i = 1; i <= dimacs.n_variables; ++i) {
        array_push_back(exprs, Expr::make_var(i));
    }

    for (s64 i = 0; i < dimacs.n_clauses; ++i) {
        s32 last_var = 0x7fffffff;
        for (s32 lit: dimacs.clause(i)) {
            expr_reduce(exprs, Expr::OR, &last_var, lit);
        }
        expr_reduce_finalize(exprs, &last_var, false);
        array_push_back(&clusters, last_var);
    }
    
    if (not clusters.size) {
        array_push_back(exprs, {Expr::TRUE});
        return;
    }

    for (s64 i = dimacs.n_quantifiers-1; i >= skip_outer; --i) {
        bool is_e = dimacs.quantifier_types[i] == Dimacs::EXISTS;
        for (s32 var: dimacs.quantifier_vars(i)) {
            expr_free_compute(&expr_free, *exprs);
            
            // Partition the clusters w.r.t. whether they have var as free variable
            s64 end = clusters.size;
            for (s64 j = 0; j < end; ++j) {
                bool contains = false;
                for (u32 v: expr_free.get(clusters[j])) contains |= var == v;
                if (contains) {
                    simple_swap(&clusters[j], &clusters[end-1]);
                    --end;
                    --j;
                }
            }
            auto clusters_affected = array_subarray(clusters, end);
            if (clusters_affected.size == 0) continue;

            if (is_e) {
                // An existential quantifier must be applied to the conjunction of the affected clusters
                s32 conjunction = 0x7fffffff;
                for (u32 cluster: clusters_affected) {
                    expr_reduce(exprs, Expr::AND, &conjunction, cluster);
                }
                assert(conjunction != 0x7fffffff);
                u32 quant = expr_make_quant(exprs, Expr::OR, var, conjunction);

                clusters.size = end;
                array_push_back(&clusters, quant);
            } else {
                // A forall quantifier can be applied to the clusters individually;
                for (u32& cluster: clusters_affected) {
                    cluster = expr_make_quant(exprs, Expr::AND, var, cluster);
                }
            }
        }
    }

    // At the end, all remaining clusters must be ANDed
    s32 conjunction = 0x7fffffff;
    for (u32 cluster: clusters) {
        expr_reduce(exprs, Expr::AND, &conjunction, cluster);
    }
    assert(conjunction != 0x7fffffff);
    if (conjunction < exprs->size-1) {
        assert(false);
        exprs->size = conjunction + 1;
    }
}

void expr_from_dimacs_try(Array_dyn<Expr>* exprs, Dimacs dimacs, u8 flags, Status* status=nullptr) {
    if (os_status_initp(&status)) return;
    
    if (dimacs.n_variables >= 65536) {
        return os_error_printf(status, 230104001, "too many variables (is %lld, must be at most 65335)\n", dimacs.n_variables);
    }

    using namespace Expr_flags;
    if (flags & SIMPLE_QUANTIFIER) {
        _expr_from_dimacs_simple(exprs, dimacs, flags & SKIP_OUTER);
        if (flags & DEBUG_CHECK_INSTANCE) {
            _expr_debug_check_instance(*exprs, dimacs);
        }
    } else {
        _expr_from_dimacs_complicated(exprs, dimacs, flags & SKIP_OUTER);
    }
}

struct Coeff_2d {
    s8 c[4];
};
Coeff_2d expr_op_coefficients_get(u8 op) {
    Coeff_2d r = {};
    r.c[0] = op & 1;
    r.c[1] = (op >> 1 & 1) - r.c[0]; // x
    r.c[2] = (op >> 2 & 1) - r.c[0]; // y
    r.c[3] = (op >> 3 & 1) + r.c[0] - (op >> 1 & 1) - (op >> 2 & 1); // xy
    return r;
}
                
Array_t<u32> expr_order_parse_try(Array_t<u8> path, Status* status=nullptr) {
    if (os_status_initp(&status)) return {};

    Array_t<u8> data = os_read_file(path, status);
    if (status->bad()) return {};
    defer { array_free(&data); };

    Array_dyn<u32> result;
    
    u8 state = 0;
    u32 num = 0;
    u32 position = 1;
    for (s64 i = 0; i <= data.size; ++i) {
        u8 c = i < data.size ? data[i] : '\n';
        bool space = c == ' ' or c == '\t' or c == '\n';
        bool digit = '0' <= c and c <= '9';
        if (not space and not digit) {
            os_error_printf(status, 230118001, "unexpected character '%c', must be space or digit\n", c);
            array_free(&result);
            return {};
        }
        
        if (state == 0 and digit) {
            state = 1;
            num = 0;
        }
        if (digit) {
            num = 10*num + (c - '0');
        }
        if (state == 1 and space) {
            state = 0;

            if (num >= result.size) {
                if (num > 65535) {
                    os_error_printf(status, 230118002, "too many variables\n");
                    array_free(&result);
                    return {};
                }
                array_resize(&result, num+1);
            }
            if (result[num]) {
                os_error_printf(status, 230118003, "variable x%u assigned twice\n", num);
                array_free(&result);
                return {};
            }
            result[num] = position++;
        }
    }

    for (s64 i = 1; i < result.size; ++i) {
        if (result[i] == 0) {
            os_error_printf(status, 230118002, "variable x%u not mapped\n", i);
            array_free(&result);
            return {};
        }
        
        // Flip the ordering, so that the first variable listed in the file is the top level.
        // Empirically, this does not seem like the right thing to do (it makes the BDDs larger on the instances I tested), so it is commented out.
        //result[i] = result.size - result[i];
    }
    
    return result;
}

void expr_order_apply(Array_t<Expr>* exprs, Array_t<u32> order) {
    assert(order[0] == 0);

    for (Expr& expr: *exprs) {
        u16* var = nullptr;
        if (expr.type == Expr::VAR) {
            var = &expr.var.var;
        } else if (expr.type == Expr::PARTIAL) {
            var = &expr.partial.var;
        } else if (expr.type == Expr::DEGREE) {
            var = &expr.degree.var;
        } else {
            assert(expr.type == Expr::FALSE or expr.type == Expr::TRUE
                or expr.type == Expr::BINOP or expr.type == Expr::DEGREE);
            continue;
        }
        *var = *var < order.size ? order[*var] : *var;
    }
}

#if 0
void expr_parser_parse(Array_t<u8> data, Array_dyn<Expr>* out_exprs, Status* status) {
    if (os_status_initp(&status)) return;

    assert(out_exprs);
    array_push_back(out_exprs, {Expr::FALSE});

    Hashmap<u32> 
    
    s64 VARMAX = 65535;
    
    u8 state = 0;
    s64 line = 1;
    s64 number = 0, max = 0xffffffff;
    Expr current;
    for (u8 c: data) {
        bool digit = '0' <= c and c <= '9';
        if (digit) {
            number = 10*number + c;
            if (number > max)
                return os_error_printf(status, 230120001, "number to large in line %lld, must be at most %lld\n", line, max);
        }
        
        if (state == 0) {
            current = {};
            number = 0;
            state = 1;
            switch (c) {
            case 'x': current.type == Expr::VAR;     max = VARMAX; break;
            case 'b': current.type == Expr::BINOP;   max = 16;     break;
            case 'p': current.type == Expr::PARTIAL; max = VARMAX; break;
            default: return os_error_printf(status, 230120001, "unknown operation '%c' in line %lld\n", c, line);
            }
        } else if (state == 1) {
            if (digit) {
                // nothing
            } else if (c == ' ') {
                switch (current.type) {
                case Expr::VAR:     current.var.var     = number; state = TODO; break;
                case Expr::BINOP:   current.binop.op    = number; state = 2; max = line-1; break;
                case Expr::PARTIAL: current.partial.var = number; state = 3; max = line-1; break;
                default: assert(false);
                }
                number = 0;
            } else {
                return os_error_printf(status, 230120002, "unexpected character '%c' in line %lld\n", c, line);
            }
        } else if (state == 2) {
            if (digit) {
                // nothing
            } else if (c == ' ') {
        }
        
        line += c == '\n';
    }
}
#endif

struct Assignment {
    u32 parent;
    u32 change_var;
    ffe change_val;
};

ffe assignment_get(Array_t<Assignment> assignments, u32 assign_it, u32 var) {
    while (assign_it != -1) {
        auto assign = assignments[assign_it];
        if (assign.change_var == var) return assign.change_val;
        assign_it = assign.parent;
    }
    return {};
}
