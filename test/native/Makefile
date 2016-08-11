all: test

test.cpp: test.ivy
	ivy_to_cpp target=repl test.ivy

test: test.cpp
	g++ -g -o test test.cpp
