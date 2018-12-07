%.cpp: %.ivy
	ivy_to_cpp target=repl isolate=iso_impl $<

%: %.cpp
	g++ -g -o $@ $<

%.test.cpp: %.ivy
	ivy_to_cpp target=test classname=$*.test $<

%.test: %.test.cpp
	g++ -I $(Z3DIR)/include -L $(Z3DIR)/lib -g -o $@ $< hash.cpp -lz3


.PRECIOUS: %.cpp %.test.cpp
