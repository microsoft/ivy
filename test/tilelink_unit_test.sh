#/bin/bash

cd ../examples/tilelink/unit_test
ivy_to_cpp isolate=iso_b tilelink_coherence_manager_tester.ivy
g++ -c -I$Z3DIR/include tilelink_coherence_manager_tester.cpp

