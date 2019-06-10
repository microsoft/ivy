Stage 2 compiler
================

This is stage 2 compiler. For the moment, it is identical to the stage
1 compiler except for some small changes in the main file
`ivy_s2.ivy`.  In can be compiler by the stage 1 compiler like this:

$ IVY_INCLUDE_PATH=../s1/include ../s1/ivyc_s1 ivyc_s2.ivy
$ g++ -I../s1/include -O2 -o ivyc_s2 -std=c++17 ivyc_s2.cpp


