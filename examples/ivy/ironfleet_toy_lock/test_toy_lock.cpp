#include "toy_lock.h"
#include <iostream>
#include <stdlib.h>

// Override methods to implement low-level network service

class my_lock : public toy_lock {

    std::vector<std::vector<int> > pkts;

public:
    my_lock(){
        pkts.resize(__CARD__node);
    }

    void ext__l__send(int pkt) {
        pkts[pkt>>2].push_back(pkt);
    }

    int ext__l__receive(int rcvr) {
        int idx = rand() % pkts[rcvr].size();
        return pkts[rcvr][idx];
    }

    bool has_packet(int rcvr){
        return pkts[rcvr].size() > 0;
    }
};

int main(int argc, char **argv){

    my_lock dut;
    for (unsigned i = 0; i < 1000; i++) {
        int n1 = rand() % dut.__CARD__node;
        if (dut.p__held[n1]) {
            int n2 = rand() % dut.__CARD__node;
            std::cout << n1 << " sending grant to " << n2 << "\n";
            dut.ext__p__grant(n1,n2);
        } else if (dut.has_packet(n1)) {
            std::cout << n1 << " receiving accept\n";
            dut.ext__p__accept(n1);
            if (dut.p__held[n1])
                std::cout << n1 << " got lock!\n";
        }
    }
    
}
