#include <arpa/inet.h>
#include <sys/socket.h>
#include "emp-zk/emp-zk-arith/int_fp.h"

struct Prover_local {
    Bdd_store store;
};

enum struct MessageType {
    calculating = 0,
    assignementSet =1,
    evaluating = 2
};

struct Message {
    MessageType type;
    u32 expr;
    u32 assignment;
    u32 slot;
    s64 length;
};

struct Prover_network{
public:
    sockaddr_in sendSockAddr{};
    int clientSd{};
    Message msg {};
    Polynomial res {};
};

struct Prover {
    enum Types: u8 {
        UNINITIALIZED, LOCAL, NETWORK
    };

    Prover() {};
    
    u8 type = UNINITIALIZED;
    union {
        Prover_local local;
        Prover_network network;
    };
    
    u64 time_duration_calc = 0;
    u64 time_duration_eval = 0;
    u64 sizeDataSentToProver = 0;
    u64 sizeDataToVerifier = 0;
};

void prover_free(Prover* prover) {
    if (prover->type == Prover::LOCAL) {
        bdd_free(&prover->local.store);
    }
}

void prover_calculate(Prover* prover_, Array_t<Expr> exprs) {    
    auto prover = &prover_->local;
    bdd_init(&prover->store, exprs);
    bdd_calculate_all(&prover->store);
}

void prover_assignment_set(Prover* prover_, u32 slot, Assignment assign) {    
    auto prover = &prover_->local;
    auto assignments = &prover->store.evaluation_cache.assignments;
    if (slot >= assignments->size) {
        array_resize(assignments, slot+1);
    }
    (*assignments)[slot] = assign;
}

void before_evaluating(Array_dyn<Assignment> assignments, Array_t<ffe> temp_assignment, Array_dyn<u64> temp_set, u32 assignment) {
    array_memset(&temp_assignment, 0);
    array_memset(&temp_set);
    for (u32 a_it = assignment; a_it != -1;) {
        auto a = assignments[a_it];
        if (not bitset_get(temp_set, a.change_var)) {
            temp_assignment[a.change_var] = a.change_val;
            bitset_set(&temp_set, a.change_var, true);
        }
        a_it = a.parent;
    }
}

vector<Commitment*> prover_evaluate(Prover* prover_, u32 expr, u32 assignment, int party, u8 type) {
    Polynomial result;
    vector<Commitment*> ret;
    // printf("in prover eval\n");
    if (party == ALICE) {
        auto prover = &prover_->local;
        result = bdd_evaluate_expr(&prover->store, expr, assignment);
    }

    ret.push_back(Commit(result.a.x, party, type));
    ret.push_back(Commit(result.b.x, party, type));
    ret.push_back(Commit(result.c.x, party, type));
    // printf("out prover eval\n");

    return ret;
}
