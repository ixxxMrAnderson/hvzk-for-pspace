struct Bdd {
    enum Type: u8 {
        INVALID, FALSE, TRUE, NORMAL, PRODUCT, LINK
    };
    u8 type; // one of Bdd::Type
    u8 type_arg; // type of operation in a product node (see Expr::Type_binop)
    u16 var; // level of the node (if the node is a link, then level of the node that was replaced by the link)
    u32 child0, child1; // index of the children in the storage array
    
    // Will be used for the hashmap for the storage
    u64 key() {
        // works always for <1024 variables and <16 million nodes, has a very good probability of working otherwise as well.
        u64 h = (type&3) | (type_arg & 15) << 2 | (var & 1023) << 6;
        h |= (child0 & 0xffffffull) << 16 | (child1 & 0xffffffull) << 40;
        h ^= hash_u64(var >> 10 | (child0 >> 24) << 6 | (child1 >> 24) << 14);
        return h + !h;
    }

    // return a child
    u32& child(u64 which) {
        assert(which < 2);
        return which ? child1 : child0;
    }
};

struct Evaluation_cache {
    // Assignment
    Array_dyn<Assignment> assignments;
    Array_t<u64> temp_assignment_set;
    Array_t<ffe> assignment;
    s64 free_var;
    
    // High cache
    Hashmap<ffe> high_values;
    Array_dyn<u16> frontier_vars;
    Array_dyn<s64> frontier_indices;
    Array_dyn<u32> frontier_data;

    // Low cache
    Hashmap<ffe> low_values;
    s64 low_bound; // highest level cached in the low caceh

    // Temporary buffers
    struct Linear {
        ffe a,b;
        Polynomial operator* (Linear o) const {
            return {a*o.a, a*o.b + b*o.a, b*o.b};
        }
    };
    Hashmap<Linear> middle_values;
    Array_dyn<u32> low_stack;
    Hashmap<Polynomial> old_evaluate;
};

void _evaluation_cache_free(Evaluation_cache* ec) {
    array_free(&ec->assignments);
    array_free(&ec->temp_assignment_set);
    array_free(&ec->assignment);
    hashmap_free(&ec->high_values);
    array_free(&ec->frontier_vars);
    array_free(&ec->frontier_indices);
    array_free(&ec->frontier_data);
    hashmap_free(&ec->low_values);
    hashmap_free(&ec->middle_values);
    array_free(&ec->low_stack);
}

struct Bdd_store {
    Array_dyn<Expr> exprs;
    Expr_free expr_free;
    
    s64 n_vars;

    // Result of an expression
    struct Expr_result {
        u32 bdd; // the root node of the eBDD
        s64 log; // the length of the undo-log at the time of the result (i.e. all entries after this must be applied to get the correct result)
    };
    Array_dyn<Expr_result> expr_results;
    
    Array_dyn<Bdd> bdds;
    Hashmap<u32> bdd_lookup;
    Array_dyn<u32> bdd_free; // list of slots that can be re-used

    // Logs that a node has been modified
    struct Log_entry {
        u32 node_it; // id of the modified node
        bool referenced; // at time of replacement, does any other node point to the referenced node?
        Bdd node; // contents of the node prior to modification
    };
    Array_dyn<Log_entry> bdd_log; // undo log; store modifications to be able to revert them

    Evaluation_cache evaluation_cache;
    
    Array_dyn<u32> temp;
    Hashmap<u32> temp_map;

    enum Debug_flags: u8 {
        DEBUG_FINAL_FRONTIER = 1,
        DEBUG_EVALUATION_CACHE = 2,
        DEBUG_DRAW_RESULTS = 4,
        DEBUG_CHECK_EVAL = 8,
        DEBUG_CHECK_FREE = 16,
    };
    u8 debug_flags = 0;

    s64 size_store_max = 0;
    s64 nodes_store_max = 0;
};

void bdd_free(Bdd_store* store) {
    array_free(&store->exprs);
    expr_free_free(&store->expr_free);
    array_free(&store->expr_results);
    array_free(&store->bdds);
    hashmap_free(&store->bdd_lookup);
    array_free(&store->bdd_free);
    array_free(&store->bdd_log);
    array_free(&store->temp);
    hashmap_free(&store->temp_map);
    
    _evaluation_cache_free(&store->evaluation_cache);
    array_push_back(&store->evaluation_cache.frontier_indices, 0);
}

u32 _bdd_create(Bdd_store* store, Bdd node, bool* out_create = nullptr) {
    u32* ptr = hashmap_getcreate(&store->bdd_lookup, node.key(), (u32)-1);
    if (out_create) *out_create = *ptr == -1;
    if (*ptr == -1) {
        if (store->bdd_free.size) {
            // Setting the value in the hashmap
            *ptr = store->bdd_free.back();
            --store->bdd_free.size;
            // We will modify the slot, so add an entry to the undo-log.
            array_push_back(&store->bdd_log, {*ptr, false, store->bdds[*ptr]});
            store->bdds[*ptr] = node;
        } else {
            *ptr = store->bdds.size;
            array_push_back(&store->bdds, node);
        }
    }
    // Return the index at which the node is stored in the bdd's array
    return *ptr;
}

void bdd_init(Bdd_store* store, Array_t<Expr> exprs) {
    store->exprs.size = 0;
    store->expr_results.size = 0;
    array_append(&store->exprs, exprs),
    array_append_zero(&store->expr_results, store->exprs.size);
    array_memset(&store->expr_results, -1);
    
    store->n_vars = 0;
    for (Expr expr: exprs) {
        if (expr.type == Expr::VAR and store->n_vars < expr.var.var+1)
            store->n_vars = expr.var.var;
    }
    
    store->bdds.size = 0;
    _bdd_create(store, {Bdd::FALSE, 0, 0, 0, 0});
    _bdd_create(store, {Bdd::TRUE,  0, 0, 1, 1});
    
    hashmap_clear(&store->bdd_lookup);
    store->bdd_log.size = 0;

    store->evaluation_cache.assignment = array_create<ffe>(store->n_vars+1);
    store->evaluation_cache.temp_assignment_set = array_create<u64>((store->n_vars+1 + 63) / 64);
    array_push_back(&store->evaluation_cache.frontier_indices, 0);
    hashmap_set_empty(&store->evaluation_cache.high_values, -1);
    hashmap_set_empty(&store->evaluation_cache.low_values, -1);
    hashmap_set_empty(&store->evaluation_cache.middle_values, -1);

    expr_free_compute(&store->expr_free, exprs);
}

void bdd_print_one(Bdd_store* store, u32 node_it, Array_dyn<u8>* out) {
    Bdd node = store->bdds[node_it];
        
    switch (node.type) {
    case Bdd::FALSE:
    case Bdd::TRUE:
        array_printf(out, "%4lld  %c\n", node_it, "FT"[node.type == Bdd::TRUE]);
        break;
    case Bdd::NORMAL:
        array_printf(out, "%4lld  N x%-2u %4u %4u\n", node_it, (int)node.var, node.child0, node.child1);
        break;
    case Bdd::PRODUCT:
        array_printf(out, "%4lld  P x%-2u %4u %4u op=%d\n", node_it, (int)node.var, node.child0, node.child1, node.type_arg);
        break;
    case Bdd::LINK:
        array_printf(out, "%4lld  L --> %4u\n", node_it, node.child0);
        break;
    default: assert_false;
    }
}

void bdd_print(Bdd_store* store, Array_t<u8> path = {}) {
    // printf("in bdd print");

    std::ofstream outfile("BDD.txt", std::ios::app);
    Array_dyn<u8> out;
    Array_t<u64> freed = array_create<u64>((store->bdds.size + 63) / 64);
    defer {
        array_free(&out);
        array_free(&freed);
    };

    for (u32 i: store->bdd_free) {
        bitset_set(&freed, i, true);
    }
    
    outfile << "Bdd_store " << store->bdds.size << endl;
    for (s64 node_it = 0; node_it < store->bdds.size; ++node_it) {
        Bdd node = store->bdds[node_it];
        
        switch (node.type) {
        case Bdd::FALSE:
        case Bdd::TRUE:
            outfile << node_it << " " << "FT"[node.type == Bdd::TRUE] << endl;
            break;
        case Bdd::NORMAL:
            outfile << node_it << " N " << (int)node.var << " " << node.child0 << " " << node.child1 << endl;
            break;
        case Bdd::PRODUCT:
            outfile << node_it << " P " << (int)node.var << " " << node.child0 << " " << node.child1 << " " << (int)node.type_arg << endl;
            break;
        case Bdd::LINK:
            outfile << node_it << " L " << node.child0 << endl;
            break;
        default: assert_false;
        }
    }
}

u32 _bdd_create_normal(Bdd_store* store, u16 var, u32 child0, u32 child1) {
    if (child0 == child1) return child0;
    return _bdd_create(store, {Bdd::NORMAL, 0, var, child0, child1});
}

bool _bdd_op_eval(/*Expr::Type_binop*/u8 op, bool x0, bool x1) {
    u8 i = x0 | (u8)x1 << 1;
    return op >> i & 1;
}

// Create a product node and return the result. If a new node was created this way, add it to out.
u32 _bdd_create_product(Bdd_store* store, u8 op, u32 child0, u32 child1, Array_dyn<u32>* out) {
    // Check whether we are at the bottom of the recursion
    if (child0 <= 1 and child1 <= 1) {
        // Return 0 or 1 directly, depending on the result of the operation
        return _bdd_op_eval(op, child0, child1);
    }

    // If one argument is constant, we can optimise in some cases. Essentially, after plugging in the constant term, we are left with a unary binary operation. There are only four of those: FALSE, X, NOT X, and TRUE. We cannot optimise NOT X, as there is no node for it, but we can do the other two.
    if (child0 <= 1) {
        u8 op_left = op >> child0 & 5;
        switch (op_left) {
        case 0b000: return 0;
        case 0b100: return child1;
        case 0b101: return 1;
        }
    } else if (child1 <= 1) {
        u8 op_left = op >> (2*child1);
        switch (op_left) {
        case 0b00: return 0;
        case 0b10: return child0;
        case 0b11: return 1;
        }
    }

    // Note that the case child0 == child1 cannot be optimised in general, as e.g. the nodes (x AND x) and x are only logically equivalent, but they arithmetise differently: [[(x AND x)]] = [[x]]^[[x]] .
    
    // Create a node and return the index it is at
    bool created;
    u16 var = std::max(store->bdds[child0].var, store->bdds[child1].var);
    assert(store->bdds[child0].type != Bdd::LINK);
    assert(store->bdds[child1].type != Bdd::LINK);
    u32 node = _bdd_create(store, {Bdd::PRODUCT, op, var, child0, child1}, &created);
    if (created) array_push_back(out, node);
    return node;
}

// Update a node in-place, to make it a normal node with the specified children. If such a node already exists, replace node_it with a link instead. (But do not add it to store->bdd_free!)
void _bdd_make_normal(Bdd_store* store, u32 node_it, u16 var, u32 child0, u32 child1) {
    Bdd node = store->bdds[node_it];
    assert(node.type == Bdd::NORMAL or node.type == Bdd::PRODUCT);
    hashmap_delete(&store->bdd_lookup, node.key());
    
    u32 existing = -1;
    if (child0 == child1) {
        existing = child0;
    } else {
        array_push_back(&store->bdd_free, node_it);
        u32 node_it_new = _bdd_create(store, {Bdd::NORMAL, 0, var, child0, child1});
        if (node_it_new != node_it) {
            --store->bdd_free.size;
            existing = node_it_new;
        } else {
            store->bdd_log.back().referenced = true;
        }
    }

    if (existing != (u32)-1) {
        array_push_back(&store->bdd_log, {node_it, true, node});
        store->bdds[node_it] = {Bdd::LINK, 0, node.var, existing, (u32)-1};
    }
}


void bdd_draw(Bdd_store* store, u32 node, Array_t<u8> path) {
    Array_dyn<u8> out;
    Array_dyn<u32> worklist;
    Array_dyn<u64> visited;
    defer {
        array_free(&out);
        array_free(&worklist);
        array_free(&visited);
    };
    array_push_back(&worklist, node);
    array_resize(&visited, (store->bdds.size + 63) / 64);
    array_memset(&visited);
    
    array_printf(&out, "digraph G {\n");

    while (worklist.size) {
        u32 bdd_it = worklist.back();
        --worklist.size;

        if (bitset_get(visited, bdd_it)) continue;
        bitset_set(&visited, bdd_it, true);
        
        Bdd bdd = store->bdds[bdd_it];
        
        switch (bdd.type) {
        case Bdd::FALSE:
        case Bdd::TRUE:
            array_printf(&out, "%lld [label=\"%c\"];\n", bdd_it, "FT"[bdd.type == Bdd::TRUE]);
            array_printf(&out, "{rank=0; %lld;}\n", bdd_it);
            break;
        case Bdd::NORMAL:
            array_printf(&out, "%lld [label=\"%lld: x%lld\",shape=\"ellipse\"];\n", bdd_it, bdd_it, bdd.var);
            array_printf(&out, "{rank=%lld; %lld;}\n", bdd.var, bdd_it);
            if (bdd.child0) {
                array_printf(&out, "%lld -> %lld [style=dashed];\n", bdd_it, bdd.child0);
                array_push_back(&worklist, bdd.child0);
            }
            if (bdd.child1) {
                array_printf(&out, "%lld -> %lld;\n", bdd_it, bdd.child1);
                array_push_back(&worklist, bdd.child1);
            }
            break;
        case Bdd::PRODUCT:
            array_printf(&out, "%lld [label=\"%lld: %s\",shape=\"box\",style=\"filled\",fillcolor=\"#e8edee\",color=\"#104354\"];\n", bdd_it, bdd_it, Expr::binop_names_uni[bdd.type_arg]);
            array_printf(&out, "%lld -> %lld [style=dashed];\n", bdd_it, bdd.child0);
            array_printf(&out, "%lld -> %lld;\n", bdd_it, bdd.child1);
            array_append(&worklist, {bdd.child0, bdd.child1});
            break;
        case Bdd::LINK:
            array_printf(&out, "%lld [label=\"%lld\",shape=\"hexagon\",width=0.5,height=0.4,fixedsize=true];\n", bdd_it, bdd_it);
            array_printf(&out, "%lld -> %lld;\n", bdd_it, bdd.child0);
            array_push_back(&worklist, bdd.child0);
            break;
        default: assert_false;
        }

    }
    array_printf(&out, "}\n");

    array_write_to_file(path, out);
}

void _bdd_draw_result(Bdd_store* store, s64 frame, u32 bdd) {
    Array_dyn<u8> path;
    defer { array_free(&path); };

    path.size = 0;
    array_printf(&path, "out_graphs/result%03lld.dot", frame);
    bdd_draw(store, bdd, path);
    path.size = 0;
    array_printf(&path, "dot -Tsvg out_graphs/result%03lld.dot > out_graphs/result%03lld.svg", frame, frame);
    auto _ = system((char*)path.data);
}

void _bdd_debug_check_free(Bdd_store* store, u32 expr_it) {
    auto expr_free = store->expr_free.get(expr_it);
    Array_t<u64> expr_free_set = array_create<u64>((store->n_vars+1 + 63) / 64);
    defer { array_free(&expr_free_set); };
    for (u32 var: expr_free) bitset_set(&expr_free_set, var, true);

    Hashmap<bool> seen;
    seen.empty = -1;
    defer { hashmap_free(&seen); };
    Array_dyn<u32> stack;
    defer { array_free(&stack); };

    u32 root_it = store->expr_results[expr_it].bdd;
    if (root_it <= 1) return;
    array_push_back(&stack, root_it);
    hashmap_set(&seen, 0, true);
    hashmap_set(&seen, 1, true);
    
    while (stack.size) {
        u32 node_it = stack.back();
        --stack.size;

        Bdd node = store->bdds[node_it];
        u8 children = 0;
        switch (node.type) {
        case Bdd::PRODUCT:
        case Bdd::NORMAL: children = 2; break;
        case Bdd::LINK: children = 1; break;
        default: assert(false);
        }
        assert(bitset_get(expr_free_set, node.var));
        for (u8 c = 0; c < children; ++c) {
            bool* b = hashmap_getcreate(&seen, node.child(c), false);
            if (*b) continue;
            *b = true;
            array_push_back(&stack, node.child(c));
        }
    }
}

void _bdd_do_partial(Bdd_store* store, Expr::Expr_partial expr, Bdd_store::Expr_result* out_result) {
    // Idea for the future: do two partial evaluations at once
    Array_dyn<u32> stack = store->temp;
    defer { store->temp = stack; };
    
    stack.size = 0;
    hashmap_clear(&store->temp_map);
    store->temp_map.empty = -1;

    u32 root = store->expr_results[expr.child].bdd;
    array_push_back(&stack, root);
    while (stack.size) {
        u32 node_it = stack.back();
        if (hashmap_getptr(&store->temp_map, node_it)) {
            --stack.size;
            continue;
        }
        Bdd node = store->bdds[node_it];

        if (node.var < expr.var) {
            hashmap_set(&store->temp_map, node_it, node_it);
        } else if (node.var == expr.var) {
            hashmap_set(&store->temp_map, node_it, node.child(expr.val.x));
        } else {
            u32* ptr0 = hashmap_getptr(&store->temp_map, node.child0);
            u32* ptr1 = hashmap_getptr(&store->temp_map, node.child1);
            if (ptr0 and ptr1) {
                u32 node_new = _bdd_create_normal(store, node.var, *ptr0, *ptr1);
                hashmap_set(&store->temp_map, node_it, node_new);
            } else {
                if (not ptr0) array_push_back(&stack, node.child0);
                if (not ptr1) array_push_back(&stack, node.child1);
                continue;
            }
        }

        --stack.size;
    }

    out_result->bdd = hashmap_get(&store->temp_map, root);
    out_result->log = store->bdd_log.size;
}

void _bdd_do_rename(Bdd_store* store, Expr::Expr_rename expr, Bdd_store::Expr_result* out_result) {
    Array_dyn<u32> stack = store->temp;
    defer { store->temp = stack; };
    
    stack.size = 0;
    hashmap_clear(&store->temp_map);
    store->temp_map.empty = -1;

    u16 free_beg, free_end;
    if (expr.var_from < expr.var_to) {
        free_beg = expr.var_from + expr.count;
        free_end = expr.var_to   + expr.count;
    } else {
        assert(expr.var_from > expr.var_to);
        free_beg = expr.var_to;
        free_end = expr.var_from;
    }
    
    u32 root = store->expr_results[expr.child].bdd;
    array_push_back(&stack, root);
    while (stack.size) {
        u32 node_it = stack.back();
        if (hashmap_getptr(&store->temp_map, node_it)) {
            --stack.size;
            continue;
        }
        Bdd node = store->bdds[node_it];

        assert(not (free_beg <= node.var and node.var < free_end));

        if (node.var < expr.var_from) {
            hashmap_set(&store->temp_map, node_it, node_it);
        } else {
            u32 var_new = node.var;
            if (expr.var_from <= node.var and node.var < expr.var_from + expr.count) {
                var_new = (node.var - expr.var_from) + expr.var_to;
            }
            
            u32* ptr0 = hashmap_getptr(&store->temp_map, node.child0);
            u32* ptr1 = hashmap_getptr(&store->temp_map, node.child1);
            if (ptr0 and ptr1) {
                u32 node_new = _bdd_create_normal(store, var_new, *ptr0, *ptr1);
                hashmap_set(&store->temp_map, node_it, node_new);
            } else {
                if (not ptr0) array_push_back(&stack, node.child0);
                if (not ptr1) array_push_back(&stack, node.child1);
                continue;
            }
        }

        --stack.size;
    }

    out_result->bdd = hashmap_get(&store->temp_map, root);
    out_result->log = store->bdd_log.size;
}


u32 _bdd_partial(Bdd_store* store, u32 bdd_it, u16 var, u8 val) {
    Bdd bdd = store->bdds[bdd_it];
    assert(bdd.var <= var);
    if (bdd.var == var) {
        return val ? bdd.child1 : bdd.child0;
    } else {
        return bdd_it;
    }
}

void _bdd_do_binop(Bdd_store* store, u32 expr_it, Array_t<Expr> exprs, Array_t<Bdd_store::Expr_result> out_results) {
    Array_dyn<u32> nodes = store->temp;
    defer { store->temp = nodes; };
    nodes.size = 0;
    s64 nodes_last = 0;

    // printf("in_bdd_do_binop\n");
    assert(exprs[0].type == Expr::BINOP);
    Expr::Expr_binop expr = exprs[0].binop;

    u32 root = _bdd_create_product(store, expr.op, store->expr_results[expr.child0].bdd, store->expr_results[expr.child1].bdd, &nodes);

    // printf("dexpr_it %d\n", exprs.size);

    for (s64 dexpr_it = 1; dexpr_it < exprs.size; ++dexpr_it) {
        // It seems weird to start with this, but it makes more sense overall
        while (store->bdds[root].type == Bdd::LINK) root = store->bdds[root].child0;
        out_results[dexpr_it-1] = {root, store->bdd_log.size};
        
        if (store->debug_flags & Bdd_store::DEBUG_DRAW_RESULTS) {
            _bdd_draw_result(store, expr_it+dexpr_it-1, root);
        }
        if (store->debug_flags & Bdd_store::DEBUG_CHECK_FREE) {
            _bdd_debug_check_free(store, expr_it+dexpr_it-1);
        }
        
        assert(exprs[dexpr_it].type == Expr::DEGREE);
        auto dexpr = exprs[dexpr_it].degree;

        s64 nodes_last_new = nodes.size;
        for (s64 i = nodes_last; i < nodes_last_new; ++i) {
            u32 node_it = nodes[i];
            Bdd node = store->bdds[node_it];

            assert(node.type == Bdd::PRODUCT);
            assert(node.var <= dexpr.var);
            if (node.var == dexpr.var) {
                u32 child[2];
                for (u8 j = 0; j < 2; ++j) {
                    child[j] = _bdd_create_product(store, expr.op,
                        _bdd_partial(store, node.child0, dexpr.var, j),
                        _bdd_partial(store, node.child1, dexpr.var, j),
                        &nodes
                    );
                }
                _bdd_make_normal(store, node_it, dexpr.var, child[0], child[1]);
            } else {
                simple_swap(&nodes[i], &nodes[nodes_last_new-1]);
                --nodes_last_new; --i;
            }
        }

        nodes_last = nodes_last_new;
    }

    s64 i_out = nodes.size;
    for (s64 i = nodes.size-1; i >= 0; --i) {
        u32 node_it = nodes[i];
        Bdd node = store->bdds[node_it];

        assert(node.type == Bdd::LINK or node.type == Bdd::NORMAL);
        
        if (node.type == Bdd::NORMAL) {
            bool dirty = false;
            for (u8 c = 0; c < 2;) {
                Bdd child = store->bdds[node.child(c)];
                if (child.type == Bdd::LINK) {
                    dirty = true;
                    node.child(c) = child.child0;
                } else {
                    ++c;
                }
            }

            if (dirty) {
                _bdd_make_normal(store, node_it, node.var, node.child0, node.child1);
            }
        }
        if (node.type == Bdd::LINK) {
            nodes[--i_out] = node_it;
        }
    }

    // Write the last result (i.e. the non-extended BDD) here, after all the links have been removed
    while (store->bdds[root].type == Bdd::LINK) root = store->bdds[root].child0;
    out_results.back() = {root, store->bdd_log.size};
    if (store->debug_flags & Bdd_store::DEBUG_DRAW_RESULTS) {
        _bdd_draw_result(store, expr_it+exprs.size-1, root);
    }
    if (store->debug_flags & Bdd_store::DEBUG_CHECK_FREE) {
        _bdd_debug_check_free(store, expr_it+exprs.size-1);
    }
        
    for (s64 i = i_out; i < nodes.size; ++i) {
        array_push_back(&store->bdd_free, nodes[i]);
    }
    // printf("out_bdd_do_binop\n");
}

void bdd_calculate_all(Bdd_store* store) {
    for (u32 expr_it = 0; expr_it < store->exprs.size; ++expr_it) {
        auto* result = &store->expr_results[expr_it];
        assert(result->bdd == -1);
        
        Expr expr = store->exprs[expr_it];
        bool skip = false;
        
        switch (expr.type) {
        case Expr::FALSE:
            *result = {0, (u32)store->bdd_log.size};
            break;
        case Expr::TRUE:
            *result = {1, (u32)store->bdd_log.size};
            break;
        case Expr::VAR: {
            u32 bdd = _bdd_create_normal(store, expr.var.var, 0, 1);
            *result = {bdd, (u32)store->bdd_log.size};
        } break;
        case Expr::BINOP: {
            s64 index = expr_it;
            // printf("%d", store->exprs[expr_it].binop.op);
            while (expr_it+1 < store->exprs.size and store->exprs[expr_it+1].type == Expr::DEGREE) ++expr_it;
            // printf("-------index: %d, expr_it: %d--------------\n", index, expr_it);
            _bdd_do_binop(store, index, array_subarray(store->exprs, index, expr_it+1), array_subarray(store->expr_results, index, expr_it+1));
            skip = true;
        } break;
        case Expr::PARTIAL:
            _bdd_do_partial(store, expr.partial, result);
            break;
        case Expr::RENAME:
            _bdd_do_rename(store, expr.rename, result);
            break;
        default: assert_false;
        }

        if (skip) continue;
        
        if (store->debug_flags & Bdd_store::DEBUG_DRAW_RESULTS) {
            _bdd_draw_result(store, expr_it, result->bdd);
        }
        if (store->debug_flags & Bdd_store::DEBUG_CHECK_FREE) {
            _bdd_debug_check_free(store, expr_it);
        }
    }
    
    store->size_store_max = (store->bdds.size - store->bdd_free.size) * sizeof(Bdd)
        + store->bdd_log.size * sizeof(Bdd_store::Log_entry);
    store->nodes_store_max = store->bdds.size - store->bdd_free.size + store->bdd_log.size;
}

void _bdd_evaluation_cache_print(Bdd_store* store) {
    auto* ec = &store->evaluation_cache;

    printf("  assignment: [");
    for (s64 i = 1; i < ec->assignment.size; ++i) {
        if (i>1) printf(", ");
        ffe val = ec->assignment[i];
        if (val.is_invalid()) {
            printf("x%lld free", i);
        } else {
            printf("x%lld=%llx", i, val.x);
        }
    }
    printf("]\n");
    printf("  frontier:\n");
    for (s64 i = 0; i < ec->frontier_vars.size; ++i) {
        printf("    x%-3u: [", ec->frontier_vars[i]);
        u64 key = i << 32;
        bool first = true;
        for (u32 node_it: array_subindex(ec->frontier_indices, ec->frontier_data, i)) {
            ffe* val = hashmap_getptr(&ec->high_values, key | node_it);
            if (first) first = false;
            else printf(", ");
            if (val) {
                printf("$%u=%llx", node_it, val->x);
            } else {
                printf("$%u=<missing>", node_it);
            }
        }
        puts("]");
    }
    printf("  low_values: ");
    {bool first = true;
    for (auto slot: ec->low_values.slots) {
        if (slot.key == ec->low_values.empty) continue;
        if (first) first = false;
        else printf(", ");
        printf("$%llu:=%llx", slot.key, slot.val.x);
    }}
    puts("");
    printf("  low_bound: x%llu\n", ec->low_bound);
}

ffe _bdd_evaluate_node_low(Bdd_store* store, u32 root_it) {
    auto* ec = &store->evaluation_cache;
    if (ffe* ptr = hashmap_getptr(&ec->low_values, root_it)) return *ptr;

    ec->low_stack.size = 0;
    array_push_back(&ec->low_stack, root_it);
    while (ec->low_stack.size) {
        u32 node_it = ec->low_stack.back();
        u32 node_it_orig = node_it;
        Bdd node = store->bdds[node_it];
        while (node.type == Bdd::LINK) {
            node_it = node.child0;
            node = store->bdds[node_it];
        }
        // NOTE(philipp): Try whether updating the pointers makes a difference

        if (hashmap_getptr(&ec->low_values, node_it)) continue;
        
        ffe* child0 = hashmap_getptr(&ec->low_values, node.child0);
        if (not child0) { array_push_back(&ec->low_stack, node.child0); continue; }
        ffe* child1 = hashmap_getptr(&ec->low_values, node.child1);
        if (not child1) { array_push_back(&ec->low_stack, node.child1); continue; }

        ffe val;
        if (node.type == Bdd::NORMAL) {
            ffe x = ec->assignment[node.var];
            val = (1 - x) * *child0 + x * *child1;
        } else if (node.type == Bdd::PRODUCT) {
            Coeff_2d coeff = expr_op_coefficients_get(node.type_arg);
            val = coeff.c[0];
            val += coeff.c[1] * *child0;
            val += (coeff.c[2] + coeff.c[3] * *child0) * *child1;
        } else {
            assert_false;
        }

        hashmap_setnew(&ec->low_values, node_it, val);
        if (ec->low_bound < node.var) ec->low_bound = node.var;
        if (node_it != node_it_orig) {
            hashmap_setnew(&ec->low_values, node_it_orig, val);
        }
        --ec->low_stack.size;
    }
    return hashmap_get(&ec->low_values, root_it);
}

Evaluation_cache::Linear _bdd_evaluate_node_middle(Bdd_store* store, u32 node_it) {
    auto* ec = &store->evaluation_cache;
    Bdd node = store->bdds[node_it];
    if (node.var < ec->free_var or node.type == Bdd::LINK) {
        return {0, _bdd_evaluate_node_low(store, node_it)};
    }

    Evaluation_cache::Linear* ptr = hashmap_getcreate(&ec->middle_values, node_it, {0, ffe::make_invalid()});
    if (ptr->b.is_invalid()) {
        ffe child0_val = _bdd_evaluate_node_low(store, node.child0);
        ffe child1_val = _bdd_evaluate_node_low(store, node.child1);
        *ptr = {child1_val - child0_val, child0_val};
    }
    return *ptr;
}

Polynomial _linear_op(u8 op, Evaluation_cache::Linear p, Evaluation_cache::Linear q) {
    // c0 + c1*p + c2*q + c3*p*q
    // = c0 + c1*p + (c3*p + c2)*q
    //                ---------
    //                = c3p_c2
    
    Coeff_2d coeff = expr_op_coefficients_get(op);
    Evaluation_cache::Linear c3p_c2;
    c3p_c2.b = ffe{coeff.c[3]} * p.b + ffe{coeff.c[2]};
    c3p_c2.a = coeff.c[3] * p.a;

    Polynomial r = c3p_c2 * q;
    r.c += coeff.c[1] * p.b + coeff.c[0];
    r.b += coeff.c[1] * p.a;
    return r;
}

void _bdd_frontier_update(Bdd_store* store, u64 key, u16* var_next, u32 node_it, ffe coeff) {
    auto* ec = &store->evaluation_cache;
    Bdd node = store->bdds[node_it];
    ffe* ptr = hashmap_getcreate(&ec->high_values, key | node_it, ffe::make_invalid());
    if (ptr->is_invalid()) {
        *ptr = 0;
        array_push_back(&ec->frontier_data, node_it);
        if (*var_next < node.var) *var_next = node.var;
    }
    *ptr += coeff;
}

Polynomial bdd_evaluate_node(Bdd_store* store, u32 root) {
    auto* ec = &store->evaluation_cache;
    // printf("in node eval\n");

    // If no variable is free, use the high-cache
    if (ec->free_var == -1) ec->free_var = 0;
    // printf("no free var %d\n", ec->free_var);

    // Initialise the frontier, if necessary
    if (ec->frontier_vars.size == 0) {
        array_push_back(&ec->frontier_vars, store->bdds[root].var);
        array_push_back(&ec->frontier_data, root);
        array_push_back(&ec->frontier_indices, ec->frontier_data.size);
        hashmap_set(&ec->high_values, 0 | root, 1);
    }
    assert(ec->frontier_data[0] == root and ec->frontier_indices[1] == 1);

    // printf("%d\n", ec->frontier_vars.back());

    // Extend the frontier until free_var
    for (u16 var = ec->frontier_vars.back(); var > ec->free_var;) {

        // printf("in frontier %d\n", var);
        u16 var_next = 0;
        u64 key_last = (ec->frontier_vars.size-1) << 32;
        u64 key_next = ec->frontier_vars.size << 32;
        
        // Iterate through one layer, replace each node by its children, if possible
        s64 beg = ec->frontier_indices[ec->frontier_indices.size-2];
        s64 end = ec->frontier_indices.back();
        // printf("%d, %d\n", beg, end);
        for (s64 i = beg; i < end; ++i) {
            u32 node_it = ec->frontier_data[i];
            Bdd node = store->bdds[node_it];
            ffe node_fac = hashmap_get(&ec->high_values, key_last | node_it);
            // if (node.type == Bdd::PRODUCT) printf("PRODUCT\n");

            if (node.type == Bdd::NORMAL and node.var >= var) {
                // Can transfer coefficients to children, do that
                assert(node.var == var);
                ffe x = ec->assignment[node.var];
                _bdd_frontier_update(store, key_next, &var_next, node.child0, node_fac * (1-x));
                _bdd_frontier_update(store, key_next, &var_next, node.child1, node_fac * x);
                
            } else if (node.type == Bdd::LINK and node.var >= var) {
                // Can also transfer coefficients to children, do that
                assert(node.var == var);
                _bdd_frontier_update(store, key_next, &var_next, node.child0, node_fac);
            
            } else {
                // Cannot transfer coefficients, copy node instead
                assert(node.var < var);

                _bdd_frontier_update(store, key_next, &var_next, node_it, node_fac);
            }
        }

        array_push_back(&ec->frontier_vars, var_next);
        array_push_back(&ec->frontier_indices, ec->frontier_data.size);
        var = var_next;
    }

    // printf("where are you 1\n");

    // Initialise low_values, if necessary
    if (ec->low_values.size == 0) {
        hashmap_setnew(&ec->low_values, 0, 0);
        hashmap_setnew(&ec->low_values, 1, 1);
    }

    // Clear middle cache
    hashmap_clear(&ec->middle_values);
    
    // Finally, compute the value by iterating the frontier
    auto final_frontier = array_subindex(ec->frontier_indices, ec->frontier_data, ec->frontier_indices.size-2);
    u64 final_key = (ec->frontier_vars.size - 1) << 32;
    Polynomial result;
    if (store->debug_flags & Bdd_store::DEBUG_FINAL_FRONTIER) {
        printf("final frontier:\n");
    }
    
    for (u32 node_it: final_frontier) {
        Bdd node = store->bdds[node_it];
        ffe node_fac = hashmap_get(&ec->high_values, final_key | node_it);

        Polynomial p;
        if (node.var == ec->free_var and node.type == Bdd::PRODUCT) {
            auto child0_p = _bdd_evaluate_node_middle(store, node.child0);
            auto child1_p = _bdd_evaluate_node_middle(store, node.child1);
            p = _linear_op(node.type_arg, child0_p, child1_p);
        } else {
            auto lin = _bdd_evaluate_node_middle(store, node_it);
            p.b += lin.a;
            p.c += lin.b;
        }

        if (store->debug_flags & Bdd_store::DEBUG_FINAL_FRONTIER) {
            printf("    %3u <- [", node_it);
            polynomial_print(p);
            printf("] * %llx\n", node_fac.x);
        }

        p *= node_fac;
        result += p;
    }

    // printf("out node eval\n");

    return result;
}

void _bdd_assignment_load(Bdd_store* store, u32 expr, u32 assignment, s64* mark_low, s64* mark_high) {
    auto* ec = &store->evaluation_cache;
    array_memset(&ec->temp_assignment_set);

    auto arr = store->expr_free.get(expr);
    s64 left = arr.size;
    for (u32 var: arr) bitset_set(&ec->temp_assignment_set, var, true);

    // This part can be made faster by storing the assignment id of the assignment stored in ec->assignment. Once the traversal of the assignment tree hits that node, we can stop. However, this is already fast enough to now show up in my profile, and correctness is not trivial.
    for (u32 a_it = assignment; a_it != -1 and left > 0;) {
        auto a = ec->assignments[a_it];
        if (bitset_get(ec->temp_assignment_set, a.change_var)) {
            bool diff = ec->assignment[a.change_var] != a.change_val;
            bool free = a.change_val.is_invalid();
            
            ec->assignment[a.change_var] = a.change_val;
            bitset_set(&ec->temp_assignment_set, a.change_var, false);
            --left;

            if (diff or free) {
                if (*mark_low  > a.change_var-1) *mark_low  = a.change_var-1;
                if (*mark_high < a.change_var+1) *mark_high = a.change_var+1;
            }
        }
        a_it = a.parent;
    }

    assert(left == 0);

    ec->free_var = -1;
    for (u32 var: arr) {
        if (ec->assignment[var].is_invalid()) {
            assert(ec->free_var == -1);
            ec->free_var = var;
        }
    }
}

Polynomial bdd_evaluate_expr(Bdd_store* store, u32 expr, u32 assignment) {
    // printf("in bdd_eval\n");
    auto* ec = &store->evaluation_cache;

    s64 mark_low  = store->n_vars; // discard the low cache above this variable
    s64 mark_high = 1; // discard the high cache below this variable

    // Load the new assignment, compute changes
    _bdd_assignment_load(store, expr, assignment, &mark_low, &mark_high);
    
    // Undo changes to the BDD, update marks
    auto r = store->expr_results[expr];
    Array_dyn<u8> temp;
    defer { array_free(&temp); };
    while (store->bdd_log.size > r.log) {
        auto entry = store->bdd_log.back();
        if (entry.node_it == r.bdd) {
            // If the node is the root, the entire high cache must be invalidated
            mark_high = store->n_vars+1;
            // also delete it from the low cache
            u16 level = entry.node.var;
            if (mark_low > level-1) mark_low = level-1;
        } else if (entry.referenced) {
            // If the node is referenced, changing it can invalidate computed values for other node, so we have to invalidate the cache
            u16 level = entry.node.var;
            if (mark_low > level-1) mark_low = level-1;
            if (mark_high < level) mark_high = level;
        } else {
            // Otherwise, only the node itself needs to be invalidated (in rare cases, old entries for the node can survive in the low cache)
            hashmap_delete_if_present(&ec->low_values, entry.node_it);
        }
        
        store->bdds[entry.node_it] = entry.node;
        --store->bdd_log.size;
    }
    assert(store->bdd_log.size == r.log);

    // Compare roots
    if (ec->frontier_data.size and r.bdd != ec->frontier_data[0]) {
        // Root has changed, invalidate entire high cache
        mark_high = store->n_vars+1;
    }

    // Invalidate low cache
    if (ec->low_bound > mark_low) {
        // always invalidate the whole low cache at once
        hashmap_clear(&ec->low_values);
        ec->low_bound = 0;
    }

    // Invalidate high cache
    while (ec->frontier_vars.size and ec->frontier_vars.back() < mark_high) {
        u64 key = (ec->frontier_vars.size-1) << 32;
        for (u32 bdd_it: array_subindex(ec->frontier_indices, ec->frontier_data, ec->frontier_vars.size-1)) {
            hashmap_delete(&ec->high_values, key | bdd_it);
        }
        --ec->frontier_vars.size;
        --ec->frontier_indices.size;
        ec->frontier_data.size = ec->frontier_indices.back();
    }

    if (store->debug_flags & Bdd_store::DEBUG_EVALUATION_CACHE) {
        _bdd_evaluation_cache_print(store);
    }
    if (store->debug_flags & Bdd_store::DEBUG_CHECK_EVAL) {
        auto result0 = bdd_evaluate_node(store, r.bdd);
        return result0;
    } else {
        return bdd_evaluate_node(store, r.bdd);
    }

    // printf("in bdd_eval\n");
}
