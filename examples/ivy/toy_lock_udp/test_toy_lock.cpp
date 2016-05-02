#include "toy_lock.h"
#include <iostream>
#include <stdlib.h>
#include <sys/types.h>          /* See NOTES */
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/ip.h> 
#include <sys/select.h>
#include <string.h>
#include <stdio.h>

// Override methods to implement low-level network service

class my_lock : public toy_lock {

public:

    int sock;
    int my_id;

    my_lock(int id){
        my_id = id;
        sock = socket(AF_INET, SOCK_DGRAM, 0);
        if (sock < 0)
            { std::cerr << "cannot create socket\n"; exit(1); }

        struct sockaddr_in myaddr;
        memset((char *)&myaddr, 0, sizeof(myaddr));
        myaddr.sin_family = AF_INET;
        myaddr.sin_addr.s_addr = htonl(INADDR_ANY);
        myaddr.sin_port = htons(4990+my_id);
        if (bind(sock, (struct sockaddr *)&myaddr, sizeof(myaddr)) < 0)
            { std::cerr << "bind failed\n"; exit(1); }
    }

    void ext__l__send(int dst, int pkt) {
        struct sockaddr_in dstaddr;
        memset((char *)&dstaddr, 0, sizeof(dstaddr));
        dstaddr.sin_family = AF_INET;
        dstaddr.sin_addr.s_addr = htonl(INADDR_ANY);
        dstaddr.sin_port = htons(4990+dst);
        
        std::cout << "SENDING\n";
        if (sendto(sock,&pkt,sizeof(int),0,(sockaddr *)&dstaddr,sizeof(sockaddr_in)) < 0) 
            { std::cerr << "sendto failed\n"; exit(1); }
    }

    int ext__l__recv(int rcvr) {
        int pkt;
        std::cout << "RECEIVING\n";
        if (recvfrom(sock,&pkt,sizeof(int),0,0,0) < 0)
            { std::cerr << "recvfrom failed\n"; exit(1); }
        return pkt;
    }

    void ivy_assume(bool test) {
        if (!test) {
            std::cerr << "ASSUMPTION FAILED\n";
            exit(1);
        }
    }

};

int main(int argc, char **argv){

    if (argc != 2) {
        std::cerr << "usage: test_toy_lock <index>\n";
        return(1);
    }

    int my_id = atoi(argv[1]);

    my_lock dut(my_id);

    if (dut.p__held[my_id])
        std::cout << "holding lock -- press return to grant\n";

    while(true) {

        fd_set rdfds;
        FD_ZERO(&rdfds);
        FD_SET(0,&rdfds); // stdin
        FD_SET(dut.sock,&rdfds);
        struct timeval timeout;
        timeout.tv_sec = 1;
        timeout.tv_usec = 0;

        int foo = select(dut.sock+1,&rdfds,0,0,&timeout);

        if (foo < 0)
            {perror("select failed"); exit(1);}
        
        if (foo == 0){
            std::cout << "TIMEOUT\n";            
            dut.ext__n__timeout(my_id);
        }
        else if (FD_ISSET(0,&rdfds)) {
            char *buf[256];
            read(0,buf,256);
            dut.ext__p__grant(my_id);
        }
        else if (FD_ISSET(dut.sock,&rdfds)) {
            dut.ext__n__incoming(my_id);
            if (dut.p__held[my_id])
                std::cout << "holding lock -- press return to grant\n";
        }
        else 
            {perror("select exited without input"); exit(1);}
            

    }

    
}
