Stage 3 compiler
================

This is stage 3 compiler. For the moment, it is identical to the stage
3 compiler. In can be compiled by the stage 2 compiler like this:

$ IVY_INCLUDE_PATH=../s2/include ../s2/ivyc_s2 ivyc_s3.ivy
$ g++ -I../s1/include -O2 -o ivyc_s3 -std=c++17 ivyc_s3.cpp


