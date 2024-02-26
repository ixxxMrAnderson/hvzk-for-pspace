
struct Dimacs {
    s64 n_variables = 0, n_clauses = 0, n_quantifiers = 0;

    enum Quantifier_type: u8 {
        EXISTS, FORALL
    };
    Array_dyn<u8> quantifier_types;
    Array_dyn<s64> quantifier_vars_indices;
    Array_dyn<s32> quantifier_vars_data;

    Array_t<s32> quantifier_vars(s64 quantifier) {
        return array_subarray(quantifier_vars_data, quantifier_vars_indices[quantifier], quantifier_vars_indices[quantifier+1]);
    }

    Array_dyn<s64> clauses;
    Array_dyn<s32> clause_literals;
    Array_t<s32> clause(s64 clause) {
        return array_subindex(clauses, clause_literals, clause);
    }
};

void dimacs_init(Dimacs* dimacs) {
    dimacs->n_clauses = 0;
    dimacs->n_variables = 0;
    dimacs->n_quantifiers = 0;
    dimacs->clauses.size = 0;
    dimacs->clause_literals.size = 0;
    dimacs->quantifier_vars_indices.size = 0;
    dimacs->quantifier_vars_data.size = 0;
    array_push_back(&dimacs->clauses, 0);
    array_push_back(&dimacs->quantifier_vars_indices, 0);
}

void dimacs_free(Dimacs* dimacs) {
    array_free(&dimacs->quantifier_types);
    array_free(&dimacs->quantifier_vars_indices);
    array_free(&dimacs->quantifier_vars_data);
    array_free(&dimacs->clauses);
    array_free(&dimacs->clause_literals);
}

struct Dimacs_parser {
    Status* status;
    
    // Input
    int fd;
    Array_dyn<u8> input_buf;

    // Tokens
    enum Token_type: u8 {
        LITERAL = 128, CNF, END, INVALID,
        TOKEN_TYPE_END
    };
    struct Token {
        u8 type;
        s32 value = -1;
    };
    Array_dyn<Token> token_buf;
    u8 token_state = 0;
    s64 consumed = 0, seen = 0;
    s64 line = 0, column = 0;

    // Parsing
    enum Parse_states: u8 {
        BEGIN=TOKEN_TYPE_END,
        INPUT,
        PROBLEM, PROBLEM_VARS, PROBLEM_CLAUSES,
        QUANTS, QUANT_TYPE, QUANT_ATOMS,
        CLAUSES, CLAUSE_ATOMS
    };
    Array_dyn<u8> parse_state;

    // Fixing
    Array_dyn<u64> vars_quantified;
    
    // Output
    Dimacs* result;
};

void _dimacs_parser_free(Dimacs_parser* parser) {
    array_free(&parser->input_buf);
    array_free(&parser->token_buf);
    array_free(&parser->parse_state);
    array_free(&parser->vars_quantified);
}

void _dimacs_token_type(Array_dyn<u8>* into, u8 type) {
    if (type == Dimacs_parser::LITERAL) {
        array_printf(into, "literal");
    } else if (type == Dimacs_parser::CNF) {
        array_printf(into, "cnf");
    } else if (type == Dimacs_parser::END) {
        array_printf(into, "<eof>");
    } else if (type == '\n') {
        array_printf(into, "'\\n'");
    } else {
        array_printf(into, "'%c'", type);
    }
}

void _dimacs_scan(Dimacs_parser* parser) {
    if (parser->status->bad()) return;
    
    for (s64 i = parser->seen; i < parser->input_buf.size; ++i) {
        u8 c = parser->input_buf[i];

        u8 c_type = 0;
        if (c == ' ' or c == '\t' or c == '\r') c_type = 1;
        if ('a' <= c and c <= 'z') c_type = 2;
        if (c == '\n') c_type = 3;
        if ('0' <= c and c <= '9') c_type = 4;
        if (c == '-') c_type = 5;

        ++parser->column;
        if (c_type == 3) {
            ++parser->line;
            parser->column = 0;
        }

        if (parser->token_state != 2 and c_type == 0) {
            return os_error_printf(parser->status, 221208000,
                "invalid character at line %lld column %lld: '%c'\n",
                parser->line, parser->column, (int)c
            );
        }

        // Flush token (identifier)
        if (parser->token_state == 1 and (c_type == 1 or c_type == 3)) {
            auto tok = array_subarray(parser->input_buf, parser->consumed, i);
            assert(tok.size > 0);
            parser->consumed = i;
            parser->token_state = 0;
            u8 c0 = tok[0];
            
            if (tok.size == 1 and (c0 == 'p' or c0 == 'e' or c0 == 'a')) {
                array_push_back(&parser->token_buf, {tok[0]});
                
            } else if (tok.size == 1 and c0 == 'c') {
                parser->token_state = 2;
                
            } else if (array_equal(tok, "cnf"_arr)) {
                array_push_back(&parser->token_buf, {Dimacs_parser::CNF});
                
            } else {
                array_printf(&parser->status->error_buf, "invalid identifier at line %lld column %lld: ", parser->line, parser->column);
                array_printa(&parser->status->error_buf, "'%'\n", tok);
                parser->status->code = 221208001;
                return;
            }
        } 
        
        // Flush token (literal)
        if (parser->token_state == 3 and (c_type == 1 or c_type == 3)) {
            auto tok = array_subarray(parser->input_buf, parser->consumed, i);
            assert(tok.size > 0);
            parser->consumed = i;
            parser->token_state = 0;
            
            u32 number = 0;
            bool flip_sign = tok[0] == '-';
            for (s64 j = flip_sign; j < tok.size; ++j) {
                if ('0' <= tok[j] and tok[j] <= '9') {
                    number = 10 * number + (tok[j] - '0');
                } else {
                    return os_error_printf(parser->status, 221208003,
                        "while parsing number:\ninvalid character at line %lld column %lld: '%c'\n",
                        parser->line, parser->column - (i-parser->consumed)+j, (int)tok[j]
                    );
                }
            }
            
            array_push_back(&parser->token_buf, {Dimacs_parser::LITERAL, (s32)(flip_sign ? -number : number)});
        }
        
        switch ((u64)parser->token_state << 4 | c_type) {
        case 0x01: parser->consumed = i+1; break;
        case 0x02: parser->token_state = 1; break;
        case 0x03: array_push_back(&parser->token_buf, {c}); parser->consumed = i+1; break;
        case 0x04: 
        case 0x05: parser->token_state = 3; break;
        case 0x12:
        case 0x14:
        case 0x15: break;
        case 0x20:
        case 0x21:
        case 0x22:
        case 0x24:
        case 0x25: parser->consumed = i+1; break;
        case 0x23: parser->consumed = i+1; parser->token_state = 0; break;
        case 0x32:
        case 0x35:
        case 0x34: break;
        default: assert_false; break;
        }
    }

    array_pop_front(&parser->input_buf, parser->consumed);
    parser->consumed = 0;
    parser->seen = parser->input_buf.size;
}

void _dimacs_scan_eof(Dimacs_parser* parser) {
    if (parser->status->bad()) return;
    
    if (parser->input_buf.size != 0) {
        return os_error_printf(parser->status, 221208006, "unexpected eof, while parsing token");
    }
    array_push_back(&parser->token_buf, {Dimacs_parser::END});
}

Dimacs_parser::Token _dimacs_match(Dimacs_parser* parser, s64* i, u8 type) {
    assert(i);
    if (*i >= parser->token_buf.size) {
        array_printf(&parser->status->error_buf, "unexpected eof, expected ");
        _dimacs_token_type(&parser->status->error_buf, type);
        array_printf(&parser->status->error_buf, "\n");
        parser->status->code = 221208004;
        return {Dimacs_parser::INVALID};
    }
    auto tok = parser->token_buf[*i];
    if (tok.type != type) {
        array_printf(&parser->status->error_buf, "unexpected token at line %lld column %lld: ", parser->line, parser->column);
        array_printf(&parser->status->error_buf, "expected ");
        _dimacs_token_type(&parser->status->error_buf, type);
        array_printf(&parser->status->error_buf, ", but got ");
        _dimacs_token_type(&parser->status->error_buf, tok.type);
        array_printf(&parser->status->error_buf, "\n");
        parser->status->code = 221208002;
        return {Dimacs_parser::INVALID};
    }
    ++*i;
    return tok;
}

void _dimacs_parse(Dimacs_parser* parser) {
    // see http://www.qbflib.org/qdimacs.html
    
    s64 i = 0;
    while (i < parser->token_buf.size and parser->status->good()) {
        u8 state = parser->parse_state.back();
        --parser->parse_state.size;
        auto tok = parser->token_buf[i];

        if (state < Dimacs_parser::TOKEN_TYPE_END) {
            _dimacs_match(parser, &i, state);
            continue;
        }
        
        switch (state) {
        case Dimacs_parser::INPUT:
            array_append(&parser->parse_state, {Dimacs_parser::END, Dimacs_parser::CLAUSES, Dimacs_parser::QUANTS, Dimacs_parser::PROBLEM});
            break;
            
        case Dimacs_parser::PROBLEM:
            array_append(&parser->parse_state, {'\n', Dimacs_parser::PROBLEM_CLAUSES, Dimacs_parser::PROBLEM_VARS, Dimacs_parser::CNF, 'p'});
            break;
            
        case Dimacs_parser::PROBLEM_VARS:
            parser->result->n_variables = _dimacs_match(parser, &i, Dimacs_parser::LITERAL).value;
            break;
        case Dimacs_parser::PROBLEM_CLAUSES:
            parser->result->n_clauses   = _dimacs_match(parser, &i, Dimacs_parser::LITERAL).value;
            break;

        case Dimacs_parser::QUANTS:
            if (tok.type == 'e' or tok.type == 'a') {
                array_append(&parser->parse_state, {Dimacs_parser::QUANTS, '\n', Dimacs_parser::QUANT_ATOMS, Dimacs_parser::QUANT_TYPE});
            }
            break;

        case Dimacs_parser::QUANT_TYPE: {
            u8 quant = -1;
            if (tok.type == 'e') {
                quant = Dimacs::EXISTS;
            } else if (tok.type == 'a') {
                quant = Dimacs::FORALL;
            } else {
                assert_false;
            }
            ++i;
            array_push_back(&parser->result->quantifier_types, quant);
        } break;

        case Dimacs_parser::QUANT_ATOMS:
            _dimacs_match(parser, &i, Dimacs_parser::LITERAL);
            if (tok.value == 0) {
                array_push_back(&parser->result->quantifier_vars_indices, parser->result->quantifier_vars_data.size);
                ++parser->result->n_quantifiers;
            } else if (tok.value < 0) {
                return os_error_printf(parser->status, 221208005, "while parsing quantifier set:\nunexpected negative literal at %lld column %lld\n", parser->line, parser->column);
            } else {
                array_push_back(&parser->result->quantifier_vars_data, tok.value);
                ++parser->parse_state.size;
            }
            break;

        case Dimacs_parser::CLAUSES:
            if (tok.type == Dimacs_parser::LITERAL) {
                array_append(&parser->parse_state, {Dimacs_parser::CLAUSES, '\n', Dimacs_parser::CLAUSE_ATOMS});
            }
            break;
            
        case Dimacs_parser::CLAUSE_ATOMS:
            _dimacs_match(parser, &i, Dimacs_parser::LITERAL);
            if (tok.value == 0) {
                array_push_back(&parser->result->clauses, parser->result->clause_literals.size);
            } else {
                array_push_back(&parser->result->clause_literals, tok.value);
                ++parser->parse_state.size;
            }
            break;

        default: assert_false;
        }
    }
    array_pop_front(&parser->token_buf, i);
}

void _dimacs_quantifiers_fix(Dimacs_parser* parser) {
    if (parser->status->bad()) return;
    
    parser->vars_quantified.size = 0;
    array_append_zero(&parser->vars_quantified, (parser->result->n_variables+1 + 63) / 64);
    
    for (s32 var: parser->result->quantifier_vars_data) {
        bitset_set(&parser->vars_quantified, var, true);
    }
    bitset_set(&parser->vars_quantified, 0, true);
    for (s64 var = parser->result->n_variables+1; var % 64; ++var) {
        bitset_set(&parser->vars_quantified, var, true);
    }

    s64 count = 0;
    for (u64 i: parser->vars_quantified) count += __builtin_popcountll(~i);

    if (not count) return;

    if (parser->result->quantifier_types.size == 0 or parser->result->quantifier_types[0] != Dimacs::EXISTS) {
        array_prepend_zero(&parser->result->quantifier_types, 1);
        parser->result->quantifier_types[0] = Dimacs::EXISTS;
        ++parser->result->n_quantifiers;        
        array_prepend_zero(&parser->result->quantifier_vars_indices, 1);
    }
    
    for (s64& i: array_subarray(parser->result->quantifier_vars_indices, 1)) i += count;

    array_prepend_zero(&parser->result->quantifier_vars_data, count);
    s64 i = 0;
    for (s64 var = 1; var <= parser->result->n_variables; ++var) {
        if (bitset_get(parser->vars_quantified, var)) continue;
        parser->result->quantifier_vars_data[i++] = var;
    }
}

void _dimacs_counts_fix(Dimacs_parser* parser) {
    s64 var_max = 0;
    for (s32 lit: parser->result->clause_literals) {
        u32 var = lit > 0 ? lit : -lit;
        if (var_max < var) var_max = var;
    }
    for (s32 var: parser->result->quantifier_vars_data) {
        if (var_max < var) var_max = var;
    }
    parser->result->n_variables = var_max;
    parser->result->n_clauses = parser->result->clauses.size-1;
}

struct Dimacs_parse_args {
    s64 limit_vars = 0;
    s64 limit_clauses = 0;
    s64 out_bytes_read = 0;
};

void dimacs_parse_try(Dimacs* dimacs, Array_t<u8> path, Dimacs_parse_args* args=nullptr, Status* status=nullptr) {
    if (os_status_initp(&status)) return;
    dimacs_init(dimacs);

    Dimacs_parser parser;
    defer { _dimacs_parser_free(&parser); };

    parser.status = status;
    parser.result = dimacs;
    parser.fd = os_open(path, Os_codes::OPEN_READ, 0, parser.status);
    array_push_back(&parser.parse_state, Dimacs_parser::INPUT);
    
    while (parser.status->good()) {
        s64 prev = parser.input_buf.size;
        bool flag = os_read(parser.fd, &parser.input_buf, 1024 * 16, parser.status);
        if (not flag) break;
        if (args) args->out_bytes_read += parser.input_buf.size - prev;

        _dimacs_scan(&parser);
        _dimacs_parse(&parser);
    }
    _dimacs_scan_eof(&parser);
    _dimacs_parse(&parser);

    if (parser.status->good() and parser.parse_state.size) {
        return os_error_printf(parser.status, 221208007, "unexpected eof during parsing (state=%d)\n", parser.parse_state.back());
    }
    
    _dimacs_counts_fix(&parser);
    if (args) {
        if (args->limit_vars > 0 and dimacs->n_variables > args->limit_vars) {
            return os_error_printf(parser.status, 230104002, "too many variables (is %lld, must be at most %lld)\n", dimacs->n_variables, args->limit_vars);
        }
        if (args->limit_clauses > 0 and dimacs->n_clauses > args->limit_clauses) {
            return os_error_printf(parser.status, 230104002, "too many clauses (is %lld, must be at most %lld)\n", dimacs->n_clauses, args->limit_clauses);
        }
    }
    _dimacs_quantifiers_fix(&parser);
}
void dimacs_parse(Dimacs* dimacs, Array_t<u8> path) {
    Status status;
    dimacs_parse_try(dimacs, path, nullptr, &status);
    os_error_panic(&status);
}

void dimacs_write(Dimacs* dimacs, Array_dyn<u8>* out) {
    array_printf(out, "p cnf %lld %lld\n", dimacs->n_variables, dimacs->n_clauses);
    for (s64 i = 0; i < dimacs->n_quantifiers; ++i) {
        array_printf(out, dimacs->quantifier_types[i] == Dimacs::EXISTS ? "e " : "a ");
        for (s32 var: dimacs->quantifier_vars(i)) {
            array_printf(out, "%d ", var);
        }
        array_printf(out, "0\n");
    }
    
    for (s64 i = 0; i < dimacs->n_clauses; ++i) {
        for (s32 lit: dimacs->clause(i)) {
            array_printf(out, "%d ", lit);
        }
        array_printf(out, "0\n");
    }
}

s32 dimacs_to_formula(Dimacs* dimacs, Dimacs* out) {
    s64 offset = out->n_variables + 1;
    for (s64 clause = 0; clause < dimacs->n_clauses; ++clause) {
        s32 var = offset + clause;
        // Let (l1 OR l2 OR ... OR lk) denote clause
        // We generate two implications

        // 1. var IMPLIES (l1 OR l2 OR ... OR lk), i.e. (NOT var OR l1 OR l2 OR ... OR lk)
        array_push_back(&out->clause_literals, -var);
        array_append(&out->clause_literals, dimacs->clause(clause));
        array_push_back(&out->clauses, out->clause_literals.size);

        // 2. (NOT var) IMPLIES NOT (l1 OR l2 OR ... OR lk), i.e. (var OR NOT l1) AND ... AND (var OR NOT lk)
        for (s32 li: dimacs->clause(clause)) {
            array_append(&out->clause_literals, {var, -li});
            array_push_back(&out->clauses, out->clause_literals.size);
        }
    }

    s32 var = offset + dimacs->n_clauses;
    
    // Let v1, ..., vk denote the variables we just generated for the clauses
    // We now want to generate:

    // 1. var IMPLIES (v1 AND ... AND vk), i.e. (NOT var OR v1) AND ... AND (NOT var OR vk)
    for (s32 vi = offset; vi < offset + dimacs->n_clauses; ++vi) {
        array_append(&out->clause_literals, {-var, vi});
        array_push_back(&out->clauses, out->clause_literals.size);
    }

    // 2. NOT var IMPLIES NOT (v1 AND ... AND vk), i.e. (var OR NOT v1 OR ... OR NOT vk)
    array_push_back(&out->clause_literals, var);
    for (s32 vi = offset; vi < offset + dimacs->n_clauses; ++vi) {
        array_push_back(&out->clause_literals, -vi);
    }
    array_push_back(&out->clauses, out->clause_literals.size);

    out->n_variables = var;
    out->n_clauses = out->clauses.size-1;
    return var;
}
