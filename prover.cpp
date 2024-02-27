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

void prover_init_local(Prover* prover, u8 flags) {
    assert(prover->type == Prover::UNINITIALIZED);
    prover->type = Prover::LOCAL;
    memset(&prover->local, 0, sizeof(prover->local));
    prover->local.store = {};
    prover->local.store.debug_flags = flags;
}

void prover_init_network(Prover* prover, Array_t<u8> ip, u16 port) {
    assert(prover->type == Prover::UNINITIALIZED);
    prover->type = Prover::NETWORK;
    Prover_network* nprover = &prover->network;
    memset(nprover, 0, sizeof(*nprover));
    
    bzero((char*)&(nprover->sendSockAddr), sizeof(nprover->sendSockAddr));
    nprover->sendSockAddr.sin_family = AF_INET; //Using IPV4

    assert(*ip.end() == 0);
    inet_pton(AF_INET, (char*)ip.data, &(nprover->sendSockAddr.sin_addr));
    nprover->sendSockAddr.sin_port = htons(port);
    nprover->clientSd = socket(AF_INET, SOCK_STREAM, 0);

    int status = connect(nprover->clientSd, (sockaddr*) &(nprover->sendSockAddr), sizeof(nprover->sendSockAddr));
    while(status < 0){
        status = connect(nprover->clientSd, (sockaddr*) &(nprover->sendSockAddr), sizeof(nprover->sendSockAddr));
        printf("Connection to the server FAILED!\n");
    }
    printf("Connected to the server!\n");
}

void prover_calculate(Prover* prover_, Array_t<Expr> exprs) {
    u64 begin = os_now();
    
    if (prover_->type == Prover::LOCAL) {
        auto prover = &prover_->local;
        bdd_init(&prover->store, exprs);
        bdd_calculate_all(&prover->store);
        
    } else if (prover_->type == Prover::NETWORK) {
        auto prover = &prover_->network;
        Message newmsg{MessageType::calculating, 0, 0, 0, exprs.size};
        prover->msg = newmsg;
        size_t len{sizeof(newmsg)};
        send(prover->clientSd, &prover->msg, len, 0);
        send(prover->clientSd, exprs.data, exprs.size * sizeof(Expr), 0);
        
    } else {
        assert_false;
    }

    // Do not count the size of the instance towards the certificate
    //prover_->sizeDataSentToProver += sizeof(exprs.size) + exprs.size * sizeof(Expr);
    prover_->time_duration_calc += os_now() - begin;
}

void prover_assignment_set(Prover* prover_, u32 slot, Assignment assign) {
    u64 begin = os_now();
    defer { prover_->time_duration_eval += os_now() - begin; };
    
    if (prover_->type == Prover::LOCAL) {
        auto prover = &prover_->local;
        auto assignments = &prover->store.evaluation_cache.assignments;
        if (slot >= assignments->size) {
            array_resize(assignments, slot+1);
        }
        (*assignments)[slot] = assign;
        
    } else if (prover_->type == Prover::NETWORK) {
        Prover_network* prover = &prover_->network;
        Message newmsg{MessageType::assignementSet, 0, 0, slot, sizeof(Assignment)};
        prover->msg = newmsg;
        size_t len {sizeof(newmsg)};
        send(prover->clientSd, &(prover->msg), len, 0);
        send(prover->clientSd, &assign, sizeof(Assignment) , 0);
    }

    prover_->sizeDataSentToProver += sizeof(slot) + sizeof(Assignment);
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

Polynomial prover_evaluate(Prover* prover_, u32 expr, u32 assignment) {
    u64 begin = os_now();
    Polynomial result;
    
    if (prover_->type == Prover::LOCAL) {
        auto prover = &prover_->local;
        result = bdd_evaluate_expr(&prover->store, expr, assignment);
        
    } else if (prover_->type == Prover::NETWORK) {
        Prover_network* prover = &prover_->network;
        Message newmsg{MessageType::evaluating, expr, assignment, 0, 0};
        prover->msg = newmsg;
        size_t len {sizeof(newmsg)};
        send(prover->clientSd, &(prover->msg), len, 0);
        //send(prover->clientSd, assignment.data, assignment.size * sizeof(ffe),0);
        recv(prover->clientSd, (Polynomial*)&(prover->res), sizeof(Polynomial),0);
        result = prover->res;
        
    } else {
        assert_false;
    }
    
    prover_->time_duration_eval += os_now() - begin;
    prover_->sizeDataSentToProver += sizeof(expr) + sizeof(assignment);
    prover_->sizeDataToVerifier += sizeof(Polynomial);
    return result;
}
