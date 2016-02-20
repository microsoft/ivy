#include <iostream>
#include "ivy_test.h"



int main(){
    ivy_test tb;

    init_gen ig;
    ext__c__acquire_gen cag;

    for (int j = 0; j < 1; j++) {

        std::cout << "initializing\n";
        if (!ig.generate(tb)){
            std::cout << " no initial states!";
            break;
        }

        if (cag.generate(tb)) {
            std::cout << "__loc__ltime_ = " << cag.__loc__ltime_ << "\n";
            std::cout << "__loc__own = " << cag.__loc__own << "\n";
            std::cout << "__loc__word = " << cag.__loc__word << "\n";
            std::cout << "__loc__addr_hi = " << cag.__loc__addr_hi << "\n";
            std::cout << "__loc__id_ = " << cag.__loc__id_ << "\n";
            std::cout << "__loc__a = " << cag.__loc__a << "\n";
            std::cout << "__loc__data_ = " << cag.__loc__data_ << "\n";
            std::cout << "__loc__op = " << cag.__loc__op << "\n";

        }
        else {
            std::cout << "deadlock";
            break;
        }            
    }
}

void ivy_assert(bool c){
    if (!c) {
        std::cerr << "assert failed\n";
    }
}

void ivy_assume(bool c){
    if (!c) {
        std::cerr << "assume failed\n";
    }
}

int choose(int rng, int label){
    return 0;
}
