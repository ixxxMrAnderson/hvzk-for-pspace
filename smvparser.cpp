#include <signal.h>

namespace Smv_vartype {
    enum Variable_types: u8 {
        STATE, INPUT, NEXT, VARS_TYPE_END
    };
}

struct Smv_parser_result {
    u8 flags = 0;
    
    Array_dyn<Expr> exprs;

    u16 beg[Smv_vartype::VARS_TYPE_END];
    u16 end[Smv_vartype::VARS_TYPE_END];
    u16 size[Smv_vartype::VARS_TYPE_END];
    s64 n_variables;
    
    u32 expr_initial, expr_transition, expr_invariant;
    s64 bytes_read;
    
    u8 var_type(u16 var) {
        for (s64 i = 0; i < Smv_vartype::VARS_TYPE_END; ++i) {
            if (beg[i] <= var and var < end[i]) return i;
        }
        assert_false;
    }
};

struct Smv_parser {
    enum Flags: u8 {
        DEBUG_PRINT_TOKENS = 1, DEBUG_PRINT_EXPR = 2, DEBUG_PRINT_PENDING = 4, DEBUG_PRINT_ONESTEP = 8
    };
    
    enum Token_type: u16 {
        // first 256 values reserved for one-character tokens
        KEYWORDS_BEGIN = 256,
        KEYWORD_MODULE = KEYWORDS_BEGIN, KEYWORD_DEFINE, KEYWORD_MDEFINE, KEYWORD_CONSTANTS,
        KEYWORD_VAR, KEYWORD_IVAR, KEYWORD_FROZENVAR, KEYWORD_INIT, KEYWORD_TRANS, KEYWORD_INVAR,
        KEYWORD_SPEC, KEYWORD_CTLSPEC, KEYWORD_LTLSPEC, KEYWORD_PSLSPEC, KEYWORD_COMPUTE,
        KEYWORD_NAME, KEYWORD_INVARSPEC, KEYWORD_FAIRNESS, KEYWORD_JUSTICE, KEYWORD_COMPASSION,
        KEYWORD_ISA, KEYWORD_ASSIGN, KEYWORD_CONSTRAINT, KEYWORD_SIMPWFF, KEYWORD_CTLWFF,
        KEYWORD_LTLWFF, KEYWORD_PSLWFF, KEYWORD_COMPWFF, KEYWORD_IN, KEYWORD_MIN, KEYWORD_MAX,
        KEYWORD_MIRROR, KEYWORD_PRED, KEYWORD_PREDICATES, KEYWORD_process, KEYWORD_array,
        KEYWORD_of, KEYWORD_boolean, KEYWORD_integer, KEYWORD_real, KEYWORD_word, KEYWORD_word1,
        KEYWORD_bool, KEYWORD_signed, KEYWORD_unsigned, KEYWORD_extend, KEYWORD_resize,
        KEYWORD_sizeof, KEYWORD_uwconst, KEYWORD_swconst, KEYWORD_EX, KEYWORD_AX, KEYWORD_EF,
        KEYWORD_AF, KEYWORD_EG, KEYWORD_AG, KEYWORD_E, KEYWORD_F, KEYWORD_O, KEYWORD_G, KEYWORD_H,
        KEYWORD_X, KEYWORD_Y, KEYWORD_Z, KEYWORD_A, KEYWORD_U, KEYWORD_S, KEYWORD_V, KEYWORD_T,
        KEYWORD_BU, KEYWORD_EBF, KEYWORD_ABF, KEYWORD_EBG, KEYWORD_ABG, KEYWORD_case, KEYWORD_esac,
        KEYWORD_mod, KEYWORD_next, KEYWORD_init, KEYWORD_union, KEYWORD_in, KEYWORD_xor,
        KEYWORD_xnor, KEYWORD_self, KEYWORD_TRUE, KEYWORD_FALSE, KEYWORD_count, KEYWORD_abs,
        KEYWORD_max, KEYWORD_min, KEYWORDS_END,

        OPS_BEGIN,
        OP_IMPLY = OPS_BEGIN, OP_NE, OP_LE, OP_GE, OP_RSHIFT, OP_LSHIFT, OP_CONCAT, OP_EQUIV,
        OP_ASSIGN,
        OPS_END_PARSABLE, OP_UNARY_MINUS = OPS_END_PARSABLE, OPS_END,
        
        NUMBER, IDENTIFIER, _EXPR, _BOTTOM
    };
    static constexpr char const* keywords[] = {
        "MODULE", "DEFINE", "MDEFINE", "CONSTANTS", "VAR", "IVAR", "FROZENVAR", "INIT", "TRANS",
        "INVAR", "SPEC", "CTLSPEC", "LTLSPEC", "PSLSPEC", "COMPUTE", "NAME", "INVARSPEC",
        "FAIRNESS", "JUSTICE", "COMPASSION", "ISA", "ASSIGN", "CONSTRAINT", "SIMPWFF", "CTLWFF",
        "LTLWFF", "PSLWFF", "COMPWFF", "IN", "MIN", "MAX", "MIRROR", "PRED", "PREDICATES",
        "process", "array", "of", "boolean", "integer", "real", "word", "word1", "bool", "signed",
        "unsigned", "extend", "resize", "sizeof", "uwconst", "swconst", "EX", "AX", "EF", "AF",
        "EG", "AG", "E", "F", "O", "G", "H", "X", "Y", "Z", "A", "U", "S", "V", "T", "BU", "EBF",
        "ABF", "EBG", "ABG", "case", "esac", "mod", "next", "init", "union", "in", "xor", "xnor",
        "self", "TRUE", "FALSE", "count", "abs", "max", "min"
    };
    static constexpr char const* ops[] = {
        "->", "!=", "<=", ">=", ">>", "<<", "::", "<->", ":=", "- (unary)"
    };
    
    struct Token {
        u16 type;
        union {
            s64 number;
            u64 identifier;
            u32 expr;
        };
        Token(u16 type=0, s64 number_=0): type{type}, number{number_} {}
        Token(u16 type, u64 identifier_): type{type}, identifier{identifier_} {}
    };
    static Token token_expr(u32 expr) {
        Token t {_EXPR}; t.expr = expr; return t;
    }

    Array_dyn<Token> tokens;
    Hashmap<u16> keyword_map;
    Stringstore stringstore;
    Status* status = nullptr;

    s64 token_it = 0;

    enum Bexpr_type: u8 {
        BEXPR_INVALID, BEXPR_FALSE, BEXPR_TRUE, BEXPR_LOOKUP, BEXPR_BINOP, BEXPR_NEXT, BEXPR_NEGATE
    };
    struct Bexpr {
        u8 type, binop;
        union {
            u64 identifier;
            struct { u32 child0, child1; };
        };
        u32& child(u8 c) {
            assert(c < 2 and type == BEXPR_BINOP);
            return c ? child0 : child1;
        }

        Bexpr(u8 type, u64 identifier=0):
            type{type}, binop{0}, identifier{identifier} {}
        Bexpr(u8 type, u8 binop, u32 child0, u32 child1):
            type{type}, binop{binop}, child0{child0}, child1{child1} {}

    };
    static Bexpr bexpr_lookup(u64 identifier) { return {BEXPR_LOOKUP, identifier}; }
    static Bexpr bexpr_binop(u8 op, u32 child0, u32 child1) { return {BEXPR_BINOP, op, child0, child1}; }
    static Bexpr bexpr_next(u32 child) { return {BEXPR_NEXT, 0, child, 0}; }
    static Bexpr bexpr_negate(u32 child) { return {BEXPR_NEGATE, 0, child, 0}; }

    struct Pending {
        u64 identifier = 0;
        Offset<Bexpr> exprs = {};
        s64 dependencies_left = 0;
    };
    struct Dependency {
        s64 pending;
        u64 identifier;
    };
    
    Array_dyn<Pending> pending;
    Array_dyn<Bexpr> pending_bexpr;
    Array_dyn<Dependency> dependencies;
    u64 virtual_identifier_next = 1;

    enum Op_flags: u8  {
        OPFLAG_FLUSH = 1, OPFLAG_RIGHT_ASSOC = 2, OPFLAG_INVALID = 4, OPFLAG_BINOP = 8, OPFLAG_SQASH = 16
    };
    struct Op_info {
        u8 precedence;
        u8 flags = 0;
        u8 expr_op = 0;
        u16 matches = 0;
    };
    Array_dyn<Token> basicexpr_stack;

    Array_dyn<u64> variables, input_variables;
    Array_dyn<u64> initial, transition, invariant;

    Smv_parser_result* result;

    Array_dyn<u8> get_identifier_buf;
    Array_t<u8> get_identifier(u64 identifier) {
        if (identifier >> 63) {
            return stringstore_get_str(&stringstore, identifier);
        } else {
            get_identifier_buf.size = 0;
            array_printf(&get_identifier_buf, "$%lld", identifier);
            return get_identifier_buf;
        }
    }
};
constexpr char const* Smv_parser::keywords[];
constexpr char const* Smv_parser::ops[];

void smvparser_free(Smv_parser* parser) {
    array_free(&parser->tokens);
    hashmap_free(&parser->keyword_map);
    stringstore_free(&parser->stringstore);
    array_free(&parser->pending);
    array_free(&parser->pending_bexpr);
    array_free(&parser->dependencies);
    array_free(&parser->basicexpr_stack);
    array_free(&parser->variables);
    array_free(&parser->initial);
    array_free(&parser->transition);
}

bool _smvparser_startswith(Array_t<u8> input, s64* i, char const* str) {
    auto arr = array_create_str(str);
    bool r = *i + arr.size <= input.size and array_equal(arr, array_subarray(input, *i, *i+arr.size));
    if (r) *i += arr.size - 1;
    return r;
}

void smvparser_scan(Smv_parser* parser, Array_t<u8> input) {
    if (parser->status->bad()) return;
    
    for (s64 i = Smv_parser::KEYWORDS_BEGIN; i < Smv_parser::KEYWORDS_END; ++i) {
        auto arr = array_create_str(Smv_parser::keywords[i - Smv_parser::KEYWORDS_BEGIN]);
        u64 id = stringstore_get_id(&parser->stringstore, arr);
        hashmap_set(&parser->keyword_map, id, i);
    }
    
    s64 state = 0;
    s64 id_start;
    bool num_flip = false;
    s64 num = 0;
    for (s64 i = 0; i <= input.size; ++i) {
        u8 c = i < input.size ? input[i] : 0;
        u8 c_next = i+1 < input.size ? input[i+1] : 0;
        bool is_id0 = ('a' <= c and c <= 'z') or ('A' <= c and c <= 'Z') or c == '_';
        bool is_digit = '0' <= c and c <= '9';
        bool is_id = is_id0 or is_digit or c == '$' or c == '#' or c == '-' or c == '.';
        bool is_space = c == ' ' or c == '\n' or c == '\r' or c == '\t';
        
        if (state == 0) {
            if (is_space) {
                // nothing
            } else if (_smvparser_startswith(input, &i, "--")) {
                state = 3;
            } else if (_smvparser_startswith(input, &i, "/--")) {
                state = 4;
            } else if (is_id0) {
                state = 1;
                id_start = i;
            } else if (is_digit) {
                state = 2;
                num = c - '0';
                num_flip = false;
            } else if (c == '-' and '0' <= c_next and c_next <= '9') {
                state = 2;
                num = 0;
                num_flip = true;
            } else {
                bool found = false;
                
                for (u16 op = Smv_parser::OPS_BEGIN; op < Smv_parser::OPS_END_PARSABLE; ++op) {
                    auto op_name = Smv_parser::ops[op - Smv_parser::OPS_BEGIN];
                    if (_smvparser_startswith(input, &i, op_name)) {
                        array_push_back(&parser->tokens, {op});
                        found = true;
                        break;
                    }
                }
                if (not found) {
                    array_push_back(&parser->tokens, {c});
                }
            }
        } else if (state == 1) {
            if (is_id) {
                // nothing
            } else {
                auto ident = array_subarray(input, id_start, i);
                u64 id = stringstore_get_id(&parser->stringstore, ident);
                if (u16* tok_type = hashmap_getptr(&parser->keyword_map, id)) {
                    array_push_back(&parser->tokens, {*tok_type});
                } else {
                    array_push_back(&parser->tokens, {Smv_parser::IDENTIFIER, id});
                }
                state = 0;
                --i;
            }
        } else if (state == 2) {
            if (is_digit) {
                num = 10*num + c - '0';
            } else {
                if (num_flip) num = -num;
                array_push_back(&parser->tokens, {Smv_parser::NUMBER, num});
                state = 0;
                --i;
            }
        } else if (state == 3) {
            if (c == '\n') state = 0;
        } else if (state == 4) {
            if (c == '-' and _smvparser_startswith(input, &i, "--/")) state = 0;
        } else {
            assert_false;
        }
    }
}

Array_t<u8> _smvparser_token_type_nice(u16 type) {
    static u8 buf;
    if (type == 0) {
        return "<eof>"_arr;
    } else if (type == '\n') {
        return "'\\n'"_arr;
    } else if (type < 128) {
        buf = type;
        return {&buf, 1};
    } else if (Smv_parser::KEYWORDS_BEGIN <= type and type < Smv_parser::KEYWORDS_END) {
        return array_create_str(Smv_parser::keywords[type - Smv_parser::KEYWORDS_BEGIN]);
    } else if (Smv_parser::OPS_BEGIN <= type and type < Smv_parser::OPS_END) {
        return array_create_str(Smv_parser::ops[type - Smv_parser::OPS_BEGIN]);
    }
    switch (type) {
    case Smv_parser::NUMBER: return "<number>"_arr;
    case Smv_parser::IDENTIFIER: return "<identifier>"_arr;
    case Smv_parser::_EXPR: return "<expr>"_arr;
    case Smv_parser::_BOTTOM: return "<bottom>"_arr;
    default: assert_false;
    }
}

void smvparser_print_token_one(Smv_parser* parser, s64 token_it, Smv_parser::Token tok) {
    printf("%4lld  %s", token_it, (char*)_smvparser_token_type_nice(tok.type).data);
    if (tok.type == Smv_parser::NUMBER) {
        printf(" : %lld", tok.number);
    } else if (tok.type == Smv_parser::IDENTIFIER) {
        printf(" : %llx : ", tok.identifier);
        array_fwrite(stringstore_get_str(&parser->stringstore, tok.identifier));
    } else if (tok.type == Smv_parser::_EXPR) {
        printf(" : %u", tok.expr);
    }
}

void smvparser_print_tokens(Smv_parser* parser) {
    if (parser->status->bad()) return;
    puts("Tokens after scanning:");
    for (s64 i = 0; i < parser->tokens.size; ++i) {
        Smv_parser::Token tok = parser->tokens[i];
        smvparser_print_token_one(parser, i, tok);
        puts("");
    }
}
void smvparser_print_stack(Smv_parser* parser) {
    if (parser->status->bad()) return;
    puts("Expr stack:");
    for (s64 i = 0; i < parser->basicexpr_stack.size; ++i) {
        Smv_parser::Token tok = parser->basicexpr_stack[i];
        printf(" | ");
        smvparser_print_token_one(parser, i, tok);
        puts("");
    }
}

void smvparser_print_bexpr(Smv_parser* parser, s64 bexpr_it) {
    if (parser->status->bad()) return;
    printf("    %4lld  ", bexpr_it);
    auto bexpr = parser->pending_bexpr[bexpr_it];
    if (bexpr.type == Smv_parser::BEXPR_FALSE) {
        printf("false");
    } else if (bexpr.type == Smv_parser::BEXPR_TRUE) {
        printf("true");
    } else if (bexpr.type == Smv_parser::BEXPR_LOOKUP) {
        format_print("lookup %a", parser->get_identifier(bexpr.identifier));
    } else if (bexpr.type == Smv_parser::BEXPR_BINOP) {
        format_print("%s %d, %d", Expr::binop_names[bexpr.binop], bexpr.child0, bexpr.child1);
    } else if (bexpr.type == Smv_parser::BEXPR_NEXT) {
        format_print("next %d", bexpr.child0);
    } else if (bexpr.type == Smv_parser::BEXPR_NEGATE) {
        format_print("NEG %d", bexpr.child0);
    } else {
        assert_false;
    }
}

void smvparser_print_pending_one(Smv_parser* parser, Smv_parser::Pending pen) {
    if (parser->status->bad()) return;
    format_print("%a := [%d]\n", parser->get_identifier(pen.identifier), pen.dependencies_left);
    for (s64 i = pen.exprs.beg; i < pen.exprs.beg + pen.exprs.size; ++i) {
        smvparser_print_bexpr(parser, i);
        puts("");
    }
}

void smvparser_print_pending(Smv_parser* parser) {
    if (parser->status->bad()) return;
    for (auto pen: parser->pending) {
        smvparser_print_pending_one(parser, pen);
    }
}

bool smvparser_match_try(Smv_parser* parser, u16 type, Smv_parser::Token* out_tok=nullptr) {
    if (parser->status->bad()) return false;
    
    Smv_parser::Token tok = parser->tokens[parser->token_it];
    if (tok.type != type) return false;
    if (out_tok) *out_tok = tok;
    ++parser->token_it;
    return true;
}

Smv_parser::Token smvparser_match(Smv_parser* parser, u16 type) {
    if (parser->status->bad()) return {};
    
    Smv_parser::Token tok = parser->tokens[parser->token_it];
    if (tok.type != type) {
        parser->status->code = 20230123001;
        array_printa(&parser->status->error_buf, "Expected token of type %, got %\n", _smvparser_token_type_nice(type), _smvparser_token_type_nice(tok.type));
        return {};
    }
    ++parser->token_it;
    return tok;
}

void smvparser_parse_var_declaration(Smv_parser* parser) {
    smvparser_match(parser, Smv_parser::KEYWORD_VAR);
    while (true) {
        Smv_parser::Token tok;
        if (not smvparser_match_try(parser, Smv_parser::IDENTIFIER, &tok)) break;
        smvparser_match(parser, ':');
        smvparser_match(parser, Smv_parser::KEYWORD_boolean);
        smvparser_match(parser, ';');
        if (parser->status->bad()) return;
        array_push_back(&parser->variables, tok.identifier);
    }
}

void smvparser_parse_ivar_declaration(Smv_parser* parser) {
    smvparser_match(parser, Smv_parser::KEYWORD_IVAR);
    while (true) {
        Smv_parser::Token tok;
        if (not smvparser_match_try(parser, Smv_parser::IDENTIFIER, &tok)) break;
        smvparser_match(parser, ':');
        smvparser_match(parser, Smv_parser::KEYWORD_boolean);
        smvparser_match(parser, ';');
        if (parser->status->bad()) return;
        array_push_back(&parser->input_variables, tok.identifier);
    }
}

void smvparser_parse_constants_declaration(Smv_parser* parser) {
    smvparser_match(parser, Smv_parser::KEYWORD_CONSTANTS);
    while (true) {
        Smv_parser::Token tok;
        smvparser_match(parser, Smv_parser::IDENTIFIER);
        if (not smvparser_match_try(parser, ',')) break;
    }
    smvparser_match(parser, ';');
}

Smv_parser::Op_info _smvparser_op_info(Smv_parser::Token op) {
    switch (op.type) {
    case '(': return {255};
    case ')': return {0, Smv_parser::OPFLAG_BINOP | Smv_parser::OPFLAG_FLUSH};
    case '[': return {1};
    case '!': return {2};
    case Smv_parser::OP_CONCAT: return {3};
    case Smv_parser::OP_UNARY_MINUS: return {4};
    case '*': 
    case '/': 
    case Smv_parser::KEYWORD_mod: return {5};
    case '+': 
    case '-': return {6};
    case Smv_parser::OP_RSHIFT: 
    case Smv_parser::OP_LSHIFT: return {7};
    case Smv_parser::KEYWORD_union: return {8};
    case Smv_parser::KEYWORD_in: return {9};
    case '=':                      return {10, Smv_parser::OPFLAG_BINOP, Expr::XNOR};
    case '<':                      return {10, Smv_parser::OPFLAG_BINOP, Expr::NOT_X_AND_Y};
    case '>':                      return {10, Smv_parser::OPFLAG_BINOP, Expr::X_AND_NOT_Y};
    case Smv_parser::OP_NE:        return {10, Smv_parser::OPFLAG_BINOP, Expr::XOR};
    case Smv_parser::OP_LE:        return {10, Smv_parser::OPFLAG_BINOP, Expr::IMPLY};
    case Smv_parser::OP_GE:        return {10, Smv_parser::OPFLAG_BINOP, Expr::IMPLIED};
    case '&':                      return {11, Smv_parser::OPFLAG_BINOP, Expr::AND};
    case '|':                      return {12, Smv_parser::OPFLAG_BINOP, Expr::OR};
    case Smv_parser::KEYWORD_xor:  return {12, Smv_parser::OPFLAG_BINOP, Expr::XOR};
    case Smv_parser::KEYWORD_xnor: return {12, Smv_parser::OPFLAG_BINOP, Expr::XNOR};
    case '?': 
    case ':':  return {13, Smv_parser::OPFLAG_BINOP};
    case Smv_parser::OP_EQUIV: return {14, Smv_parser::OPFLAG_BINOP, Expr::XNOR};
    case Smv_parser::OP_IMPLY: return {15, Smv_parser::OPFLAG_BINOP | Smv_parser::OPFLAG_RIGHT_ASSOC, Expr::IMPLY};
    case ';':  return {16, Smv_parser::OPFLAG_BINOP};
    case Smv_parser::_BOTTOM: return {255};
    default: return {255, Smv_parser::OPFLAG_INVALID};
    }
}

bool _smvparser_match_boolbinop_try(Smv_parser* parser, Smv_parser::Token* out_tok) {
    Smv_parser::Token tok = parser->tokens[parser->token_it];
    if (_smvparser_op_info(tok).flags & Smv_parser::OPFLAG_BINOP) {
        ++parser->token_it;
        if (out_tok) *out_tok = tok;
        return true;
    }
    return false;
}

void _smvparser_parse_basic_pushexpr(Smv_parser* parser, Smv_parser::Bexpr bexpr) {
    array_push_back(&parser->pending_bexpr, bexpr);
    array_push_back(&parser->basicexpr_stack, Smv_parser::token_expr(parser->pending_bexpr.size-1));
}

void smvparser_parse_basic_atom(Smv_parser* parser, Smv_parser::Token tok, bool* out_flag_invalid) {
    if (parser->status->bad()) return;
    
    if (tok.type == Smv_parser::NUMBER) {
        if (tok.number == 0 or tok.number == 1) {
            _smvparser_parse_basic_pushexpr(parser, {tok.number ? Smv_parser::BEXPR_TRUE : Smv_parser::BEXPR_FALSE});
        } else {
            if (out_flag_invalid) *out_flag_invalid = true;
            _smvparser_parse_basic_pushexpr(parser, {Smv_parser::BEXPR_FALSE});
            //return os_error_printf(parser->status, 20230124004, "Invalid number %lld in expression\n", tok.number);
        }
    } else if (tok.type == Smv_parser::IDENTIFIER) {
        _smvparser_parse_basic_pushexpr(parser, Smv_parser::bexpr_lookup(tok.identifier));
        array_push_back(&parser->dependencies, {parser->pending.size-1, tok.identifier});
        ++parser->pending.back().dependencies_left;
        
    } else if (tok.type == Smv_parser::KEYWORD_FALSE) {
        _smvparser_parse_basic_pushexpr(parser, {Smv_parser::BEXPR_FALSE});
    } else if (tok.type == Smv_parser::KEYWORD_TRUE) {
        _smvparser_parse_basic_pushexpr(parser, {Smv_parser::BEXPR_TRUE});
        
    } else {
        assert_false;
    }
}

void smvparser_parse_basic_reduce(Smv_parser* parser) {
    if (parser->status->bad()) return;
    auto* stack = &parser->basicexpr_stack;
    
    Smv_parser::Token tok = (*stack)[stack->size-2];
    auto tok_info  = _smvparser_op_info(tok);
    if (tok_info.expr_op) {
        u32 c0 = (*stack)[stack->size-3].expr;
        u32 c1 = (*stack)[stack->size-1].expr;
        stack->size -= 3;
        _smvparser_parse_basic_pushexpr(parser, Smv_parser::bexpr_binop(tok_info.expr_op, c0, c1));
        
    } else if (tok.type == '!') {
        u32 c0 = (*stack)[stack->size-1].expr;
        stack->size -= 2;
        _smvparser_parse_basic_pushexpr(parser, Smv_parser::bexpr_negate(c0));
        
    } else if (tok.type == ':') {
        tok = (*stack)[stack->size-4];
        if (tok.type == '?') {
            u32 c0 = (*stack)[stack->size-5].expr;
            u32 c1 = (*stack)[stack->size-3].expr;
            u32 c2 = (*stack)[stack->size-1].expr;
            s64 it = parser->pending_bexpr.size;
            stack->size -= 5;
            
            array_push_back(&parser->pending_bexpr, Smv_parser::bexpr_binop(Expr::AND, c0, c1));
            array_push_back(&parser->pending_bexpr, Smv_parser::bexpr_binop(Expr::NOT_X_AND_Y, c0, c2));
            _smvparser_parse_basic_pushexpr(parser, Smv_parser::bexpr_binop(Expr::OR, it, it+1));
        } else if (tok.type == Smv_parser::KEYWORD_case or tok.type == ';') {
            // nothing
        } else {
            parser->status->code = 20230124005;
            array_printa(&parser->status->error_buf, "Unexpected ':' in expression following % (must follow '?' or case)\n", _smvparser_token_type_nice(tok.type));
            return;
        }
    } else {
        parser->status->code = 20230125002;
        array_printa(&parser->status->error_buf, "Cannot reduce expression with infix %\n", _smvparser_token_type_nice(tok.type));
        return;
    }
}

void smvparser_parse_basic_flush(Smv_parser* parser) {
    if (parser->status->bad()) return;
    auto* stack = &parser->basicexpr_stack;
    
    Smv_parser::Token tok = (*stack)[stack->size-1];
    if (tok.type == ')') {
        tok = (*stack)[stack->size-3];
        if (tok.type != '(') {
            return os_error_printf(parser->status, 20230125001, "Unmatched ')'\n");
        }

        assert((*stack)[stack->size-2].type == Smv_parser::_EXPR);
        (*stack)[stack->size-3] = (*stack)[stack->size-2];
        stack->size -= 2;

        tok = (*stack)[stack->size-2];
        if (tok.type == Smv_parser::KEYWORD_next) {
            tok = (*stack)[stack->size-1];
            assert(tok.type == Smv_parser::_EXPR);
            stack->size -= 2;
            _smvparser_parse_basic_pushexpr(parser, Smv_parser::bexpr_next(tok.expr));
        }
        
    } else {
        assert_false;
    }
}

void smvparser_parse_basic_case(Smv_parser* parser) {
    if (parser->status->bad()) return;
    auto* stack = &parser->basicexpr_stack;

    s64 len = 0;
    
    while (true) {
        bool valid = (*stack)[stack->size-4*len-1].type == ';'
                 and (*stack)[stack->size-4*len-2].type == Smv_parser::_EXPR
                 and (*stack)[stack->size-4*len-3].type == ':'
                 and (*stack)[stack->size-4*len-4].type == Smv_parser::_EXPR;
        if (not valid) {
            return os_error_printf(parser->status, 20230125003, "Invalid case expression\n");
        }
        ++len;
        if ((*stack)[stack->size-4*len-1].type == Smv_parser::KEYWORD_case) break;
    }

    if (len == 0) {
        return os_error_printf(parser->status, 20230125003, "Invalid case expression, must have at least one case\n");
    }
    u32 expr_it = (*stack)[stack->size-2].expr;
    for (s64 i = 1; i < len; ++i) {
        u32 cond  = (*stack)[stack->size-4*i-4].expr;
        u32 value = (*stack)[stack->size-4*i-2].expr;

        s64 it = parser->pending_bexpr.size;
        array_push_back(&parser->pending_bexpr, Smv_parser::bexpr_binop(Expr::AND, cond, value));
        array_push_back(&parser->pending_bexpr, Smv_parser::bexpr_binop(Expr::NOT_X_AND_Y, cond, expr_it));
        array_push_back(&parser->pending_bexpr, Smv_parser::bexpr_binop(Expr::OR, it, it+1));
        expr_it = it+2;
    }
    stack->size -= 4*len + 1;
    array_push_back(stack, Smv_parser::token_expr(expr_it));
}

u8 _smvparser_parse_basic_special(Smv_parser::Token a, Smv_parser::Token b) {
    // 0: do not reduce
    // 1: reduce
    // 2: stop
    // 255: no special action
    
    bool done = false;
    if (b.type == ':') {
        done = a.type == '?' or a.type == ';' or a.type == Smv_parser::KEYWORD_case;
    } else if (b.type == ';') {
        if (a.type == Smv_parser::_BOTTOM) return 2;
        done = a.type == ':';
    } else if (b.type == ')') {
        done = a.type == '(';        
    } else {
        return 255;
    }
    return not done;
}

void smvparser_parse_basic(Smv_parser* parser, u64 identifier, bool simple_expr=false) {
    auto* stack = &parser->basicexpr_stack;
    stack->size = 0;
    array_push_back(stack, Smv_parser::_BOTTOM);

    array_push_back(&parser->pending, {identifier});
    s64 pending_bexpr_index = parser->pending_bexpr.size;
    s64 dependencies_index = parser->dependencies.size;

    // NuSMV unfortunately still generates non-boolean expressions in boolean models, but they are not used. We can parse them, but then flag them as invalid and discard them.
    bool flag_invalid = identifier == 0;

    bool flag_print = parser->result->flags & Smv_parser::DEBUG_PRINT_EXPR;
    
    u8 state = 0;
    while (parser->status->good()) {
        if (flag_print) smvparser_print_token_one(parser, parser->token_it, parser->tokens[parser->token_it]);
        bool flag_print_stack = false;
        
        if (state == 0) {
            Smv_parser::Token tok;
            if (smvparser_match_try(parser, Smv_parser::NUMBER, &tok)
                    or smvparser_match_try(parser, Smv_parser::IDENTIFIER, &tok)
                    or smvparser_match_try(parser, Smv_parser::KEYWORD_FALSE, &tok)
                    or smvparser_match_try(parser, Smv_parser::KEYWORD_TRUE, &tok)) {
                smvparser_parse_basic_atom(parser, tok, &flag_invalid);
                state = 1;
                
            } else if (smvparser_match_try(parser, '(', &tok)
                    or smvparser_match_try(parser, '!', &tok)
                    or smvparser_match_try(parser, Smv_parser::KEYWORD_case, &tok)) {
                array_push_back(stack, tok);
                
            } else if (smvparser_match_try(parser, Smv_parser::KEYWORD_esac, &tok)) {
                if (flag_print) { printf(" -> case"); flag_print_stack = true; }
                smvparser_parse_basic_case(parser);
                state = 1;
                
            } else if (smvparser_match_try(parser, Smv_parser::KEYWORD_next, &tok)) {
                if (simple_expr) {
                    if (flag_print) puts("");
                    parser->status->code = 20230124003;
                    array_printf(&parser->status->error_buf, "next must not appear in a simple expression\n");
                    return;
                }
                if (flag_print) {
                    smvparser_print_token_one(parser, parser->token_it, parser->tokens[parser->token_it]);
                    puts(" -> shift");
                }
                
                smvparser_match(parser, '(');
                array_append(stack, {tok, {'('}});
                
            } else {
                if (flag_print) puts("");
                parser->status->code = 20230124001;
                array_printa(&parser->status->error_buf, "Invalid token % at start of expression\n", _smvparser_token_type_nice(parser->tokens[parser->token_it].type));
                return;
            }
            if (flag_print) puts(" -> shift");
            
        } else if (state == 1) {
            Smv_parser::Token tok;
            if (not _smvparser_match_boolbinop_try(parser, &tok)) {
                if (flag_print) puts(" -> stop");
                break;
            }
            
            auto tok_info  = _smvparser_op_info(tok);

            while (parser->status->good()) {
                auto tok_stack = (*stack)[stack->size-2];
                u8 prec_stack = _smvparser_op_info(tok_stack).precedence;
                u8 action = _smvparser_parse_basic_special(tok_stack, tok);
                if (action == 2) {
                    --parser->token_it;
                    state = 2;
                    break;
                } else if (action == 0) {
                    break;
                }
                
                bool reduce = action == 1
                    or prec_stack < tok_info.precedence
                    or (prec_stack == tok_info.precedence and (~tok_info.flags & Smv_parser::OPFLAG_RIGHT_ASSOC));
                if (not reduce) break;
                
                if (flag_print) { printf(" -> reduce"); fflush(stdout); flag_print_stack = true; }

                smvparser_parse_basic_reduce(parser);
            }
            if (parser->status->bad()) {
                if (flag_print) puts("");
                return;
            }
            if (state == 2) {
                if (flag_print) puts(" -> stop");
                break;
            }

            array_push_back(stack, tok);
            if (tok_info.flags & Smv_parser::OPFLAG_FLUSH) {
                if (flag_print) { printf(" -> flush"); fflush(stdout); flag_print_stack = true; }

                smvparser_parse_basic_flush(parser);
                state = 1;
            } else {
                state = 0;
            }
            
            if (flag_print) puts(" -> shift");
        } else if (state == 2) {
            assert_false;
        }
        
        if (flag_print_stack) smvparser_print_stack(parser);
    }

    if (parser->status->bad()) return;

    while (stack->size > 2) {
        smvparser_parse_basic_reduce(parser);
        if (parser->status->bad()) return;
    }

    if (flag_invalid) {
        --parser->pending.size;
        parser->pending_bexpr.size = pending_bexpr_index;
        parser->dependencies.size = dependencies_index;
        return;
    }
    
    assert(stack->back().type == Smv_parser::_EXPR and stack->back().expr == parser->pending_bexpr.size-1);
    parser->pending.back().exprs = array_makeoffset(parser->pending_bexpr, pending_bexpr_index);
}

void smvparser_parse_init_constraint(Smv_parser* parser) {
    smvparser_match(parser, Smv_parser::KEYWORD_INIT);
    u64 identifier = parser->virtual_identifier_next++;
    smvparser_parse_basic(parser, identifier, true);
    smvparser_match_try(parser, ';');
    array_push_back(&parser->initial, identifier);
    array_push_back(&parser->dependencies, {0, identifier});
    ++parser->pending[0].dependencies_left;
}

void smvparser_parse_trans_constraint(Smv_parser* parser) {
    smvparser_match(parser, Smv_parser::KEYWORD_TRANS);
    u64 identifier = parser->virtual_identifier_next++;
    smvparser_parse_basic(parser, identifier, false);
    smvparser_match_try(parser, ';');
    array_push_back(&parser->transition, identifier);
    array_push_back(&parser->dependencies, {0, identifier});
    ++parser->pending[0].dependencies_left;
}
void smvparser_parse_invar_constraint(Smv_parser* parser) {
    smvparser_match(parser, Smv_parser::KEYWORD_INVAR);
    u64 identifier = parser->virtual_identifier_next++;
    smvparser_parse_basic(parser, identifier, true);
    smvparser_match_try(parser, ';');
    array_push_back(&parser->invariant, identifier);
    array_push_back(&parser->dependencies, {0, identifier});
    ++parser->pending[0].dependencies_left;
}

void smvparser_parse_define_declaration(Smv_parser* parser) {
    smvparser_match(parser, Smv_parser::KEYWORD_DEFINE);
    Smv_parser::Token tok = smvparser_match(parser, Smv_parser::IDENTIFIER);
    while (true) {
        smvparser_match(parser, Smv_parser::OP_ASSIGN);
        smvparser_parse_basic(parser, tok.identifier, false);
        smvparser_match(parser, ';');
        
        if (not smvparser_match_try(parser, Smv_parser::IDENTIFIER, &tok)) break;
    }
}

bool smvparser_match_toplevel(Smv_parser* parser, bool call);
void smvparser_skip_toplevel(Smv_parser* parser) {
    ++parser->token_it;
    while (not smvparser_match_toplevel(parser, false)) ++parser->token_it;
}
    
bool smvparser_match_toplevel(Smv_parser* parser, bool call) {
    u16 tok_type_next = parser->tokens[parser->token_it].type;
    switch (tok_type_next) {
    case Smv_parser::KEYWORD_VAR:        if (call) smvparser_parse_var_declaration(parser);       return true;
    case Smv_parser::KEYWORD_IVAR:       if (call) smvparser_parse_ivar_declaration(parser);      return true;
    case Smv_parser::KEYWORD_INIT:       if (call) smvparser_parse_init_constraint(parser);       return true;
    case Smv_parser::KEYWORD_TRANS:      if (call) smvparser_parse_trans_constraint(parser);      return true;
    case Smv_parser::KEYWORD_INVAR:      if (call) smvparser_parse_invar_constraint(parser);      return true;
    case Smv_parser::KEYWORD_DEFINE:     if (call) smvparser_parse_define_declaration(parser);    return true;
    case Smv_parser::KEYWORD_CONSTANTS:  if (call) smvparser_parse_constants_declaration(parser); return true;
    case Smv_parser::KEYWORD_CTLSPEC:    if (call) smvparser_skip_toplevel(parser);               return true;
    case Smv_parser::KEYWORD_LTLSPEC:    if (call) smvparser_skip_toplevel(parser);               return true;
    case Smv_parser::KEYWORD_SPEC:       if (call) smvparser_skip_toplevel(parser);               return true;
    case Smv_parser::KEYWORD_INVARSPEC:  if (call) smvparser_skip_toplevel(parser);               return true;
    case Smv_parser::KEYWORD_FAIRNESS:   if (call) smvparser_skip_toplevel(parser);               return true;
    case Smv_parser::KEYWORD_JUSTICE:    if (call) smvparser_skip_toplevel(parser);               return true;
    case Smv_parser::KEYWORD_COMPASSION: if (call) smvparser_skip_toplevel(parser);               return true;
    default: return false;
    }
}


void smvparser_parse_module(Smv_parser* parser) {
    smvparser_match(parser, Smv_parser::KEYWORD_MODULE);
    smvparser_match(parser, Smv_parser::IDENTIFIER);
    while (parser->status->good()) {
        bool matched = smvparser_match_toplevel(parser, true);
        if (not matched) break;
    }

    if (parser->status->good() and parser->token_it+1 < parser->tokens.size) {
        return os_error_printf(parser->status, 20230127001, "Unexpected eof at token %lld.\n", parser->token_it);
    }
}

void smvparser_init_pending(Smv_parser* parser) {
    if (parser->status->bad()) return;

    array_push_back(&parser->pending, {});
}


void smvparser_map_variables(Smv_parser_result* result, s64 n_state, s64 n_input) {
    // IMPORTANT: If you change this order, also change the order in which identifiers are assigned below
    // @Cleanup
    using namespace Smv_vartype;
    result->size[STATE] = n_state;
    result->size[INPUT] = n_input;
    result->size[NEXT]  = n_state;
    
    u16 index = 1;
    result->beg[STATE] = index; index += result->size[STATE];
    result->end[STATE] = index;
    result->beg[INPUT] = index; index += result->size[INPUT];
    result->end[INPUT] = index;
    result->beg[NEXT]  = index; index += result->size[NEXT];
    result->end[NEXT]  = index;
    
    result->n_variables = 0;
    for (s64 i = 0; i < VARS_TYPE_END; ++i) {
        result->n_variables += result->size[i];
    }
}

void smvparser_resolve_pending(Smv_parser* parser) {
    using namespace Smv_vartype;
    if (parser->status->bad()) return;
    
    struct Expr_ref {
        u32 expr;
        bool negated;
    };
    Hashmap<Expr_ref> map_id;
    Hashmap<Expr_ref> map_bexpr;
    Hashmap<u32> map_next;
    Array_dyn<u32> stack_next;
    Array_dyn<s64> pending_left;
    defer {
        hashmap_free(&map_id); 
        hashmap_free(&map_bexpr); 
        hashmap_free(&map_next);
        array_free(&stack_next);
        array_free(&pending_left);
    };
    map_bexpr.empty = -1;
    
    assert(parser->result->exprs.size == 0);
    array_push_back(&parser->result->exprs, {Expr::FALSE});

    smvparser_map_variables(parser->result, parser->variables.size, parser->input_variables.size);
    
    for (u64 var_id: parser->variables) {
        u32 var = parser->result->exprs.size;
        array_push_back(&parser->result->exprs, Expr::make_var(var));
        hashmap_setnew(&map_id, var_id, Expr_ref {var, false});
    }
    for (u64 var_id: parser->input_variables) {
        u32 var = parser->result->exprs.size;
        array_push_back(&parser->result->exprs, Expr::make_var(var));
        hashmap_setnew(&map_id, var_id, Expr_ref {var, false});
    }
    for (s64 i = 0; i < parser->result->size[STATE]; ++i) {
        u32 var = parser->result->exprs.size;
        array_push_back(&parser->result->exprs, Expr::make_var(var));
    }

    for (s64 i = 1; i < parser->pending.size; ++i) {
        array_push_back(&pending_left, i);
    }
    
    bool dirty = true;
    while (dirty) {
        dirty = false;

        // Update the dependency counts
        for (s64 i = 0; i < parser->dependencies.size; ++i) {
            auto dep = parser->dependencies[i];
            if (not hashmap_getptr(&map_id, dep.identifier)) continue;
            --parser->pending[dep.pending].dependencies_left;
            parser->dependencies[i] = parser->dependencies.back();
            --parser->dependencies.size;
            --i;
        }

        if (parser->pending[0].dependencies_left == 0) break;
        
        // Convert all Bexpr without dependencies to Expr
        for (s64 i = 0; i < pending_left.size; ++i) {
            auto pen = parser->pending[pending_left[i]];
            if (pen.dependencies_left) continue;

            if (parser->result->flags & Smv_parser::DEBUG_PRINT_PENDING)
                format_print("Generating expressions for %a\n", parser->get_identifier(pen.identifier));

            hashmap_clear(&map_bexpr);
            {s64 bexpr_it = pen.exprs.beg;
            for (auto bexpr: array_suboffset(parser->pending_bexpr, pen.exprs)) {
                Expr_ref expr_ref;
                if (bexpr.type == Smv_parser::BEXPR_FALSE) {
                    expr_ref = {0, false};
                } else if (bexpr.type == Smv_parser::BEXPR_TRUE) {
                    expr_ref = {0, true};
                    
                } else if (bexpr.type == Smv_parser::BEXPR_LOOKUP) {
                    expr_ref = hashmap_get(&map_id, bexpr.identifier);
                    
                } else if (bexpr.type == Smv_parser::BEXPR_NEGATE) {
                    expr_ref =  hashmap_get(&map_bexpr, bexpr.child0);
                    expr_ref.negated ^= 1;
                    
                } else if (bexpr.type == Smv_parser::BEXPR_BINOP) {
                    Expr_ref c0 = hashmap_get(&map_bexpr, bexpr.child0);
                    Expr_ref c1 = hashmap_get(&map_bexpr, bexpr.child1);
                    Expr e = expr_make_binop_flip(bexpr.binop, c0.expr, c0.negated, c1.expr, c1.negated);
                    array_push_back(&parser->result->exprs, e);
                    expr_ref = {(u32)parser->result->exprs.size-1, false};

                } else if (bexpr.type == Smv_parser::BEXPR_NEXT) {
                    expr_ref = hashmap_get(&map_bexpr, bexpr.child0);
                    stack_next.size = 0;
                    array_push_back(&stack_next, expr_ref.expr);
                    while (stack_next.size) {
                        u32 expr_it = stack_next.back();
                        if (hashmap_getptr(&map_next, expr_it)) {
                            --stack_next.size; continue;
                        }

                        Expr expr = parser->result->exprs[expr_it];
                        if (expr.type == Expr::FALSE) {
                            hashmap_setnew(&map_next, expr_it, 0);
                            --stack_next.size;                            
                        } else if (expr.type == Expr::VAR) {
                            u16 var = expr.var.var;
                            if (parser->result->var_type(var) == STATE) {
                                var = var - parser->result->beg[STATE] + parser->result->beg[NEXT];
                            }
                            hashmap_setnew(&map_next, expr_it, var);
                            --stack_next.size;                            
                        } else if (expr.type == Expr::BINOP) {
                            u32* c0 = hashmap_getptr(&map_next, expr.binop.child0);
                            u32* c1 = hashmap_getptr(&map_next, expr.binop.child1);
                            if (not c0) array_push_back(&stack_next, expr.binop.child0);
                            if (not c1) array_push_back(&stack_next, expr.binop.child1);
                            if (c0 and c1) {
                                array_push_back(&parser->result->exprs, Expr::make_binop(expr.binop.op, *c0, *c1));
                                hashmap_setnew(&map_next, expr_it, parser->result->exprs.size-1);
                                --stack_next.size;
                            }
                        } else {
                            assert_false;
                        }
                    }

                    expr_ref.expr = hashmap_get(&map_next, expr_ref.expr);
                }

                hashmap_setnew(&map_bexpr, bexpr_it, expr_ref);
                ++bexpr_it;
            }}

            auto expr_ref = hashmap_get(&map_bexpr, pen.exprs.beg + pen.exprs.size-1);
            hashmap_set(&map_id, pen.identifier, expr_ref);
            pending_left[i] = pending_left.back();
            --pending_left.size;
            --i;
            dirty = true;
        }
    }

    if (parser->pending[0].dependencies_left) {
        s64 s = pending_left.size;
        return os_error_printf(parser->status, 20230127001, "There %s %lld unresolved dependenc%s.\n", s!=1?"are":"is", s, s!=1?"ies":"y");
    }
    
    s32 initial = 0x7fffffff;
    for (u64 expr_id: parser->initial) {
        auto expr_ref = hashmap_get(&map_id, expr_id);
        s32 expr_lit = expr_ref.negated ? -expr_ref.expr : expr_ref.expr;
        expr_reduce(&parser->result->exprs, Expr::AND, &initial, expr_lit);
    }
    expr_reduce_finalize(&parser->result->exprs, &initial, true);
    parser->result->expr_initial = initial;
    
    s32 transition = 0x7fffffff;
    for (u64 expr_id: parser->transition) {
        auto expr_ref = hashmap_get(&map_id, expr_id);
        s32 expr_lit = expr_ref.negated ? -expr_ref.expr : expr_ref.expr;
        expr_reduce(&parser->result->exprs, Expr::AND, &transition, expr_lit);
    }
    expr_reduce_finalize(&parser->result->exprs, &transition, true);
    parser->result->expr_transition = transition;
    
    s32 invariant = 0x7fffffff;
    for (u64 expr_id: parser->invariant) {
        auto expr_ref = hashmap_get(&map_id, expr_id);
        s32 expr_lit = expr_ref.negated ? -expr_ref.expr : expr_ref.expr;
        expr_reduce(&parser->result->exprs, Expr::AND, &invariant, expr_lit);
    }
    expr_reduce_finalize(&parser->result->exprs, &invariant, true);
    parser->result->expr_invariant = invariant;

}


void smvparser_parse(Smv_parser_result* result, Array_t<u8> path, Status* status=nullptr) {
    if (os_status_initp(&status)) return;

    Array_t<u8> input = os_read_file(path, status);
    defer { array_free(&input); };
    result->bytes_read = input.size;
    
    Smv_parser parser;
    defer { smvparser_free(&parser); };
    
    parser.status = status;
    parser.result = result;

    smvparser_scan(&parser, input);
    if (result->flags & Smv_parser::DEBUG_PRINT_TOKENS)
        smvparser_print_tokens(&parser);
    
    smvparser_init_pending(&parser);
    
    smvparser_parse_module(&parser);
    if (result->flags & Smv_parser::DEBUG_PRINT_PENDING)
        smvparser_print_pending(&parser);
    
    smvparser_resolve_pending(&parser);
}

void smvparser_generate_query(Smv_parser_result* r, s64 max_steps) {
    using namespace Smv_vartype;

    u32 transition = r->expr_transition;
    for (u16 var = r->beg[INPUT]; var < r->end[INPUT]; ++var) {
        transition = expr_make_quant(&r->exprs, Expr::OR, var, transition);
    }
    
    u32 expr_it = r->expr_initial;
    array_push_back(&r->exprs, Expr::make_binop(Expr::AND, expr_it, r->expr_invariant));
    expr_it = r->exprs.size-1;
    
    for (s64 i = 0; i < max_steps; ++i) {
        u32 prior = expr_it;
        
        array_push_back(&r->exprs, Expr::make_binop(Expr::AND, expr_it, transition));
        expr_it = r->exprs.size-1;
        for (u16 var = r->beg[STATE]; var < r->end[STATE]; ++var) {
            expr_it = expr_make_quant(&r->exprs, Expr::OR, var, expr_it);
        }
        
        array_push_back(&r->exprs, Expr::make_rename(r->beg[NEXT], r->beg[STATE], expr_it, r->size[STATE]));
        array_push_back(&r->exprs, Expr::make_binop(Expr::AND, r->expr_invariant, r->exprs.size-1));
        array_push_back(&r->exprs, Expr::make_binop(Expr::OR, prior, r->exprs.size-1));
        expr_it = r->exprs.size-1;
    }
    assert(expr_it == r->exprs.size-1);
}
