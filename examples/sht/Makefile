%.cpp: %.ivy
	ivy_to_cpp target=repl $<

%: %.cpp
	g++ -g -o $@ $<
