
#include <sys/stat.h>
#include <sys/types.h>
#include <cstdio>

#include "lib/global.hpp"
#include "lib/os_linux.cpp"
#include "lib/hashmap.cpp"
#include "lib/rng.cpp"
#include "lib/dimacs.cpp"
#include "lib/number.cpp"
#include "lib/format.cpp"
#include "lib/stringstore.cpp"

#include "ffe.cpp"
#include "expr.cpp"
#include "bdd.cpp"
#include "prover.cpp"
#include "verifier.cpp"
#include "server.cpp"
#include "smvparser.cpp"

int threads = 1, party, port, type = Commitment::VOLE;

void args_print_usage(Array_t<u8> arg0) {
    printf("Usage:\n  ");
    array_fwrite(arg0);
    printf(" [<options> ...] [--solver|--verifier] [--] <instance>\n  ");
    array_fwrite(arg0);
    puts(" [<options> ...] --prover|--fuzz");
    puts("");
    puts("Modes:");
    puts("  --solver (default)\n    Run both prover and verifier");
    puts("  --verifier\n    Run only the verifier (experimental)");
    puts("  --prover\n    Run only the prover (experimental)");
    puts("  --fuzz\n    Use this when running the solver inside a fuzzer.");
    puts("  --no-verify\n    Do not perform the sumcheck algorithm, only solve the instance.");
    puts("");
    puts("Configuration:");
    puts("  --host <ip> (default auto)\n    Which ip to connect to (when running the verifier) / listen on (when running the prover). Specify auto to connect to localhost and listening on all interfaces.");
    puts("  --port <port> (default 39411)\n    Which port to use");
    puts("  --no-skip-outer\n    Apply the outermost (existential) quantifier as well, so that the formula is closed.");
    puts("  --simple-quantifier\n    When converting QDIMACS to QBC, do not push the quantifiers inward.");
    puts("  --order <file> (default auto)\n    Map variables using this order. If left empty, the identity mapping is used. If auto, determine the path based on the instance, by changing the extension to .order .");
    puts("  --format qdimacs|smv|auto (default auto)\n    Input format. If auto, the format is determined based on the extension, defaulting to qdimacs. Note that the smv parser only operates on the flattened boolean instances, and is considered experimental.");
    puts("  --smv-steps <n> (default unbounded)\n    Maximum number of steps for smv instances. If unbounded, all reachable configurations are counted, otherwise the configurations reachable in at most n steps.");
    puts("");
    puts("Debug options:");
    puts("  --debug-draw-qbc\n    Have verifier draw the circuit (input instance).");
    puts("  --debug-draw-expr\n    Have verifier draw the polynomial expression (input with degree reductions).");
    puts("  --debug-draw-results\n    Draw the resulting eBDD for each expression.");
    puts("  --debug-sumcheck-log\n    Output a step-by-step commentary of the sumcheck algorithm.");
    puts("  --debug-final-frontier\n    For each expression evaluate by Prover, output the linear combination that is computed.");
    puts("  --debug-evaluation-cache\n    Print the state of the evaluation cache before evaluation of each expression.");
    puts("  --debug-check-free\n    Check that each computed bdd only contains nodes with the free variables of the expression.");
    puts("  --debug-check-eval\n    Run both the fast and the naive evaluation algorithm and compare the results.");
    puts("  --debug-small-numbers\n    Verifier only picks random numbers between 0 and 10.");
    puts("  --debug-check-instance\n    Generate a SAT formula that is satisfiable iff the CNF in the input DIMACS and the generated unquantified boolean circuit are not equivalent. Written to check_instance.dimacs . Only works if --simple-quantifier is used.");
    puts("  --debug-smv-tokens\n    After scanning, dump the array of tokens.");
    puts("  --debug-smv-expr\n    While parsing expressions, print step-by-step commentary.");
    puts("  --debug-smv-pending\n    Dump the pending expressions after parsing.");
    puts("  -d,--debug\n    Enable all of the above");
    puts("");
    puts("Output options:");
    puts("  -v,--verbose\n    Same as --debug-sumcheck-log");
    puts("  --no-progress\n    Do not show progress information");
    puts("  --no-stats\n    Do not show statistics");
    puts("  --no-units\n    Statistics are formatted without units");
    puts("  -s,--silent\n    Same as --no-progress --no-stats");
    puts("  -h,--help\n     Print this help");
    exit(1);
}

struct Args {
    enum Mode: u8 {
        SOLVER, VERIFIER, PROVER
    };
    u8 mode = SOLVER;
    Array_t<u8> host;
    u16 port = 39411;
    u16 party = 0;

    u8 bdd_flags = 0;
    u8 verifier_flags = 0;
    bool no_progress = false, no_stats = false;
    bool check_instance = false;
    
    Array_t<u8> instance;
    u8 expr_flags = 0;
    u8 smv_flags = 0;
    bool fuzz_mode = false;
    Array_t<u8> order = "auto"_arr;

    enum Format: u8 {
        FORMAT_AUTO, FORMAT_QDIMACS, FORMAT_SMV
    };
    u8 format = FORMAT_AUTO;
    s64 steps = 1;
};

void args_parse(Args* args, Array_t<Array_t<u8>> argv) {
    u8 state = 0;
    bool instance_set = false;
    
    for (s64 i = 1; i < argv.size; ++i) {
        auto arg = argv[i];
        
        if (state == 0) {
            // Parse option
            if (arg.size == 0 or arg[0] != '-') {
                state = 1;
                --i;
            } else if (array_equal(arg, "--solver"_arr)) {
                args->mode = Args::SOLVER;
            } else if (array_equal(arg, "--verifier"_arr)) {
                args->mode = Args::VERIFIER;
            } else if (array_equal(arg, "--prover"_arr)) {
                args->mode = Args::PROVER;
                instance_set = true;
            } else if (array_equal(arg, "--fuzz"_arr)) {
                args->mode = Args::SOLVER;
                args->instance = "/dev/stdin"_arr;
                args->fuzz_mode = true;
                args->no_progress = true;
                args->no_stats = true;
                instance_set = true;
            } else if (array_equal(arg, "--no-verify"_arr)) {
                args->mode = Args::SOLVER;
                args->verifier_flags |= Verifier::NO_VERIFY;
            } else if (array_equal(arg, "--host"_arr)) {
                state = 2;
            } else if (array_equal(arg, "--port"_arr)) {
                state = 3;
            } else if (array_equal(arg, "--order"_arr)) {
                state = 4;
            } else if (array_equal(arg, "--format"_arr)) {
                state = 5;
            } else if (array_equal(arg, "--smv-steps"_arr)) {
                state = 6;
            } else if (array_equal(arg, "--party"_arr)) {
                state = 7;
            } else if (array_equal(arg, "--no-skip-outer"_arr)) {
                args->expr_flags |= Expr_flags::SKIP_OUTER;
            } else if (array_equal(arg, "--simple-quantifier"_arr)) {
                args->expr_flags |= Expr_flags::SIMPLE_QUANTIFIER;
            } else if (array_equal(arg, "--debug-draw-qbc"_arr)) {
                args->verifier_flags |= Verifier::DEBUG_DRAW_QBC;
            } else if (array_equal(arg, "--debug-draw-expr"_arr)) {
                args->verifier_flags |= Verifier::DEBUG_DRAW_EXPR;
            } else if (array_equal(arg, "--debug-draw-results"_arr)) {
                args->bdd_flags |= Bdd_store::DEBUG_DRAW_RESULTS;
            } else if (array_equal(arg, "--debug-final_frontier"_arr)) {
                args->bdd_flags |= Bdd_store::DEBUG_FINAL_FRONTIER;
            } else if (array_equal(arg, "--debug-evaluation-cache"_arr)) {
                args->bdd_flags |= Bdd_store::DEBUG_EVALUATION_CACHE;
            } else if (array_equal(arg, "--debug-check-free"_arr)) {
                args->bdd_flags |= Bdd_store::DEBUG_CHECK_FREE;
            } else if (array_equal(arg, "--debug-check-eval"_arr)) {
                args->bdd_flags |= Bdd_store::DEBUG_CHECK_EVAL;
            } else if (array_equal(arg, "--debug-small-numbers"_arr)) {
                args->verifier_flags |= Verifier::DEBUG_SMALL_NUMBERS;
            } else if (array_equal(arg, "--debug-check-instance"_arr)) {
                args->expr_flags |= Expr_flags::DEBUG_CHECK_INSTANCE;

            } else if (array_equal(arg, "--debug-smv-tokens"_arr)) {
                args->smv_flags |= Smv_parser::DEBUG_PRINT_TOKENS;
            } else if (array_equal(arg, "--debug-smv-expr"_arr)) {
                args->smv_flags |= Smv_parser::DEBUG_PRINT_EXPR;
            } else if (array_equal(arg, "--debug-smv-pending"_arr)) {
                args->smv_flags |= Smv_parser::DEBUG_PRINT_PENDING;
                
            } else if (array_equal(arg, "--debug"_arr) or array_equal(arg, "-d"_arr)) {
                args->bdd_flags = -1;
                args->verifier_flags = -1;
                args->smv_flags = -1;
            } else if (array_equal(arg, "--verbose"_arr) or array_equal(arg, "-v"_arr) or array_equal(arg, "--debug-sumcheck-log"_arr)) {
                args->verifier_flags |= Verifier::DEBUG_SUMCHECK_LOG;

            } else if (array_equal(arg, "--silent"_arr) or array_equal(arg, "-s"_arr)) {
                args->no_progress = true;
                args->no_stats = true;
            } else if (array_equal(arg, "--no-progress"_arr)) {
                args->no_progress = true;
            } else if (array_equal(arg, "--no-stats"_arr)) {
                args->no_stats = true;
            } else if (array_equal(arg, "--no-units"_arr)) {
                global_format_ignore_units = true;
                
            } else if (array_equal(arg, "--help"_arr) or array_equal(arg, "-h"_arr)) {
                args_print_usage(argv[0]);
            } else if (array_equal(arg, "--"_arr)) {
                state = 1;
            } else {
                printf("Unknown option ");
                array_fwrite(arg);
                puts(" (try --help)");
                exit(1);
            }
        } else if (state == 1) {
            if (instance_set) {
                printf("Too many instances specified ");
                array_fwrite(arg);
                puts(" (try --help)");
                exit(1);
            }
            args->instance = arg;
            instance_set = true;
            state = 0;
        } else if (state == 2) {
            args->host = arg;
            state = 0;
        } else if (state == 3) {
            port = number_parse<u16>(arg);
            // os_error_panic();
            state = 0;
        } else if (state == 4) {
            args->order = arg;
            state = 0;
        } else if (state == 5) {
            if (array_equal(arg, "qdimacs"_arr)) {
                args->format = Args::FORMAT_QDIMACS;
            } else if (array_equal(arg, "smv"_arr)) {
                args->format = Args::FORMAT_SMV;
            } else if (array_equal(arg, "auto"_arr)) {
                args->format = Args::FORMAT_AUTO;
            } else {
                puts("Invalid --format value, must be qdimacs, smv or auto.");
                exit(1);
            }
            state = 0;
        } else if (state == 6) {
            args->steps = number_parse<s64>(arg);
            os_error_panic();
            state = 0;
        } else if (state == 7) {
            party = number_parse<u16>(arg);
            state = 0;
         } else {
            assert_false;
        }
    }

    if (state != 0) {
        puts("Unexpected end of arguments (try --help)");
        exit(1);
    }
    if (not instance_set) {
        puts("No instance specified (try --help)");
        exit(1);
    }
    if (not args->host.data or array_equal(args->host, "auto"_arr)) {
        args->host = "127.0.0.1"_arr;
    }
}

void main_order(Args* args, Array_t<Expr> exprs) {
    if (global_os.status.bad()) return;
    
    Array_dyn<u8> order_use;
    defer { array_free(&order_use); };
    
    if (args->order.size and array_equal(args->order, "auto"_arr)) {            
        s64 index = -1;
        for (s64 i = args->instance.size-1; i >= 0; --i) {
            u8 c = args->instance[i];
            if (c == '.') {
                index = i; break;
            } else if (c == '/') {
                break;
            }
        }
        if (index == -1) index = args->instance.size;
        array_append(&order_use, array_subarray(args->instance, 0, index));
        array_printf(&order_use, ".order");
        array_push_back(&order_use, 0);
        --order_use.size;


        if (os_access(order_use, Os_codes::ACCESS_READ)) {
            if (not args->no_progress) {
                puts("found");
            }
        } else {
            if (not args->no_progress) {
                puts(" not found");
            }
            order_use.size = 0;
        }
        
    } else if (args->order.size) {
        array_append(&order_use, args->order);
        if (not args->no_progress) {
            printf("Using variable order from %a\n", order_use);
        }
    }

    if (order_use.size) {
        Array_t<u32> order = expr_order_parse_try(order_use);
        defer { array_free(&order); };
        if (order.size) {
            expr_order_apply(&exprs, order);
        }
    }
}

s64 main_instance(Args* args, Array_dyn<Expr>* out_exprs, Array_dyn<u8>* out_stats, s64* out_n_variables) {
    if (global_os.status.bad()) return 0;
    
    if (args->format == Args::FORMAT_AUTO) {
        s64 index = args->instance.size;
        for (s64 i = index-1; i >= 0; --i) {
            u8 c = args->instance[i];
            if (c == '/') break;
            if (c == '.') {index = i; break;}
        }
        auto ext = array_subarray(args->instance, index);
        if (array_equal(ext, ".smv"_arr) or array_equal(ext, ".nusmv"_arr)) {
            args->format = Args::FORMAT_SMV;
        } else {
            args->format = Args::FORMAT_QDIMACS;
        }
    }

    if (args->format == Args::FORMAT_QDIMACS) {
        // printf("-------------------I am a dimacs----------------\n");
        Dimacs dimacs;
        Dimacs_parse_args dimacs_args;
        if (args->fuzz_mode) {
            dimacs_args.limit_vars = 128;
            dimacs_args.limit_clauses = 32768;
        }
        defer { dimacs_free(&dimacs); };
        dimacs_init(&dimacs);
        dimacs_parse_try(&dimacs, args->instance, &dimacs_args);
        expr_from_dimacs_try(out_exprs, dimacs, args->expr_flags);
        if (global_os.status.bad()) return 0;
        
        return dimacs_args.out_bytes_read;
        
    } else if (args->format == Args::FORMAT_SMV) {
        Smv_parser_result smv;
        smv.exprs = *out_exprs;
        smv.flags = args->smv_flags;
        smvparser_parse(&smv, args->instance);
        if (global_os.status.bad()) return 0;

        smvparser_generate_query(&smv, args->steps);
        *out_exprs = smv.exprs;
        *out_n_variables = smv.size[Smv_vartype::STATE];
        
        return smv.bytes_read;
    } else {
        assert_false;
    }
}

void init(Verifier* veri, Prover* prover, Array_t<Expr> exprs_qbc, s64 n_variables=-1, u8 debug_flags=0, u8 expr_flags = 0){
    assert(prover->type == Prover::UNINITIALIZED);
    prover->type = Prover::LOCAL;
    memset(&prover->local, 0, sizeof(prover->local));
    prover->local.store = {};

    veri->debug_flags = debug_flags;
    veri->expr_free.expr_free.size = 0;
    veri->expr_free.expr_free_data.size = 0;
    veri->expr_flags = expr_flags;

    _convert_to_poly(veri, exprs_qbc);

    assert(veri->assertions.data == nullptr);
    veri->assertions = array_create<Array_dyn<Verifier::Assertion>>(veri->exprs.size);


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

int main(int argc, char** argv_) {
    Args args;
    Prover prover;
    Verifier veri;
    uint64_t counter = 0;
    Array_dyn<u8> stats_instance;
    Array_dyn<Expr> exprs;
    s64 n_variables = -1;
    BoolIO<NetIO> *ios[threads];

    os_init();

    Array_t<Array_t<u8>> argv = array_create<Array_t<u8>>(argc);
    defer { array_free(&argv); };
    for (s64 i = 0; i < argc; ++i) {
        argv[i] = array_create_str(argv_[i]);
    }

    args_parse(&args, argv);

    for (int i = 0; i < threads; ++i) {
        ios[i] = new BoolIO<NetIO>(
            new NetIO(party == ALICE ? nullptr : "127.0.0.1", port + i),
            party == ALICE);
    }

    defer { array_free(&exprs); };
    s64 instance_size = main_instance(&args, &exprs, &stats_instance, &n_variables);

    defer { prover_free(&prover); };
    defer { verifier_free(&veri); };

    main_order(&args, exprs);
    init(&veri, &prover, exprs, n_variables, args.verifier_flags, args.expr_flags);

    u64 begin = os_now();
    if (party == ALICE) prover_calculate(&prover, veri.exprs);
    prover.time_duration_calc += os_now() - begin;
    // prover solve time / IP time / ZK time (VOLE: different network / NIZK: proof size)

    begin = os_now();

    if (type == Commitment::VOLE) setup_zk_arith<BoolIO<NetIO>>(ios, threads, party);
    // else setup_perdersen(ios[0], party);

    bool code = sumcheck(&veri, &prover, ios[0], party);
    if (!code) return 255;

    prover.time_duration_eval += os_now() - begin;

    finalize_zk_arith<BoolIO<NetIO>>();
    for (int i = 0; i < threads; ++i) {
        counter += ios[i]->counter;
        delete ios[i]->io;
        delete ios[i];
    }
        
    printf("  Instance size: .. %.2fKB\n", (double)instance_size/1024);
    printf("  Solving time:    %.2fs\n", (double)prover.time_duration_calc/1000000000);
    printf("  Proving time:     %.2fs\n", (double)prover.time_duration_eval/1000000000);
    printf("  Bytes sent: ..... %.2fMB\n", (double)counter/1024/1024);
    if (args.mode == Args::SOLVER) {
        Bdd_store* store = &prover.local.store;
        printf("  BDD store: ...... %ldMB\n", (double)store->size_store_max/1024/1024);
    }

    return 0;
}
