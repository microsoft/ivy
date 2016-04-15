all: test_toy_lock

toy_lock.cpp: toy_lock.ivy
	ivy_to_cpp target=impl isolate=iso_code toy_lock.ivy

test_toy_lock: toy_lock.cpp test_toy_lock.cpp
	g++ -g -o test_toy_lock test_toy_lock.cpp toy_lock.cpp
