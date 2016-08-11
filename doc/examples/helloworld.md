---
layout: page
title: Hello, world!
---

Having specified and verified a protocol or two, it's natural to want
to try actually running a verified protocol. Ivy programs can be
compiled into the C++ language and executed in various ways.

The simplest way to try out an Ivy program is to generate a
read-eval-print loop (REPL). We'll start with the closest thing we can
write to the "Hello, world!" program in Ivy. Ivy programs are
*reactive*, meaning that they ony do something when called upon by
their environment.  This means we can't actually write a program that
spontaneously prints a message. Here is an approximation:

    #lang ivy1.6

    action world

    action hello = {
        call world
    }

    export hello
    import word
    
This program provides an action `hello` that calls action `world`
provided by the environment. Let's try compiling and running this program:

    $ ivy_to_cpp target=repl helloworld.ivy
    $ ls helloworld.*
    helloworld.cpp  helloworld.h  helloworld.ivy

The command `ivy_to_cpp` header and implementation files `helloworld.h` and
`helloworld.cpp`. We can compile them to produce an executable file like this:

    $ c++ -o helloworld helloworld.cpp

Now let's run the program:

    $ ./helloworld
    >

The prompt `>` tells us we're in the REPL. We can now call an exported action:

    > hello
    world

When we call `hello` the program calls `world`. 

