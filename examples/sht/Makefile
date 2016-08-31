%.cpp: %.ivy
	ivy_to_cpp target=repl isolate=iso_impl $<

%: %.cpp
	g++ -g -o $@ $<

.PRECIOUS: %.cpp