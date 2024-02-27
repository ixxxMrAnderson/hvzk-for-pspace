
struct Server {
    sockaddr_in addr{};
    Bdd_store store{};
    Array_dyn<Assignment> assignments;
    Array_t<ffe> temp_assignment;
    Array_dyn<u64> temp_set;
    int sd{};
    int clientSd{};
    sockaddr_in clientAddr{};
    Message received;
    Polynomial send;

};

void server_run(Server* server, Array_t<u8> ip, u16 port){
    server->store = {};
    bzero((char*)&(server->addr), sizeof(server->addr));
    server->addr.sin_family = AF_INET;
    server->addr.sin_addr.s_addr = htonl(INADDR_ANY);
    server->addr.sin_port = htons(port);
    server->sd = socket(AF_INET, SOCK_STREAM, 0);
    if(server->sd == 0){
        printf("The server could not be established\n");
        exit(1);
    }
    int status= ::bind(server->sd, (struct sockaddr*) &(server->addr),sizeof(server->addr));
    if(status < 0){
        printf("Could not bind the server\n");
        exit(1);
    }
    //We accept at most 1 verifier
    listen(server->sd, 1);
    //Connect to the Client
    socklen_t sockLength = sizeof(server->clientAddr);
    server->clientSd = accept(server->sd, (sockaddr *) &(server->clientAddr), &sockLength);
    if(server->clientSd < 0){
        printf("could not accept the client\n");
        exit(1);
    }
    //now respond to requirements of the verifier
    while(true){
        int nbReceived = recv(server->clientSd, (Message*)&(server->received), sizeof(server->received), 0);
        if(nbReceived > 0) {
            // NOTE(philipp): Broke it again, sorry
            #if 0
            if(server->received.type == MessageType::evaluating){
                u32 assignement = server->received.assignment;
                before_evaluating(server->assignments, server->temp_assignment, server->temp_set, assignement);
                server->send = bdd_evaluate_expr(&server->store, (server->received).expr, server->temp_assignment);
                send(server->clientSd, &(server->send), sizeof(Polynomial), 0);
            } else if (server->received.type == MessageType::calculating){
                Expr *datas = (Expr *) malloc(server->received.length * sizeof(struct Expr));
                recv(server->clientSd, datas, server->received.length * sizeof(struct  Expr),0);
                Array_t<Expr> exprs{datas,server->received.length};
                bdd_init(&server->store, exprs);
                bdd_calculate_all(&server->store);
                array_resize(&server->temp_assignment, server->store.n_vars+1);
                array_resize(&server->temp_set, (server->store.n_vars+1 + 63) / 64);
            } else if (server->received.type == MessageType::assignementSet){
                u32 slot = server->received.slot;
                Assignment * assignment = (Assignment *) malloc(sizeof(Assignment));
                recv(server->clientSd, assignment, sizeof(Assignment), 0);
                if (slot >= server->assignments.size) {
                    array_resize(&server->assignments, slot+1);
                }
                server->assignments[slot] = *assignment;
            }
            #endif
        }
    } //Hier den stop signalisieren und die sd s close()
}
