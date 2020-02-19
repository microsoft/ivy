Stage 1 compiler
================

The stage 1 compiler is written in Ivy and can be compiled by Ivy 1.7,
written in Python. To compile:

$ ivyc target=repl ivyc_s1.ivy
$ g++ -O2 -o ivyc_s1 ivyc_s1.cpp -pthread
