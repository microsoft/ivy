#include "udp_test.h"
#include <iostream>
#include <unistd.h>
/*

To compile:

ivy_to_cpp target=class isolate=iso_impl build=true udp_test.ivy
g++ -g udp_class_test.cpp udp_test.o -o udp_class_test -pthread


 */

/* To implement the imported actions, we subclass udp_test.  Notice
   imported actions begin with 'imp__', and '__' replaces '.', so
   foo.send becomes imp__foo__send.
 */

class myclass : public udp_test {
    virtual void imp__foo__recv(int dst, int v) {
        std::cout << "process " << dst << " received " << v << std::endl;
    }
};

/* In the main, we create an instance and call its exported methods. */

int main(int argc, const char **argv) {
    myclass obj;
    obj.ext__foo__send(0,1,1);
    sleep(1);
}
