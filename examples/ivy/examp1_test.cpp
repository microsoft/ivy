#include <iostream>
#include "ivy_test.h"



int main(){
    ivy_test tb;
    for(int i = 0; i < 3; i++)
        for(int j = 0; j < 3; j++)
            tb.__lt[i][j] = i < j;
    tb.zero = 0;
    tb.s__last = 0;
    tb.a0__last = 0;
    tb.a0__token = true;
    tb.a1__last = 0;
    tb.a1__token = false;
    tb.i__hastok = 0;
    tb.i__last = 0;
    for (int i = 0; i < 3; i++)
        tb.f[i] = 2-i;
    tb.__init();

    init_gen ig;

    a0__serve_gen a0sg;
    a1__serve_gen a1sg;

    for (int j = 0; j < 10; j++) {
        ig.generate(tb);

        for (int i = 0; i < 10; i++) {

            if (a0sg.generate(tb)) {
                std::cout << "a0.serve(" << a0sg.inp << ") = ";
                std::cout << tb.a0__serve(a0sg.inp) << std::endl;
            }

            else if (a1sg.generate(tb)) {
                std::cout << "a1.serve(" << a1sg.inp << ") = ";
                std::cout << tb.a1__serve(a1sg.inp) << std::endl;
            }

            else {
                std::cout << "deadlock\n";
                break;
            }
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
