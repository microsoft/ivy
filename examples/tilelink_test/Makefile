BIN=tilelink_two_port_tester

$(BIN): tilelink_two_port_tester.h tilelink_two_port_tester.cpp hash.h hash.cpp main.cpp tilelink_two_port_dut.h tilelink_queue_model.cpp
	g++ -g -I $(Z3DIR)/include -L $(Z3DIR)/lib -o $(BIN) main.cpp tilelink_two_port_tester.cpp hash.cpp  tilelink_queue_model.cpp -lz3

tilelink_two_port_tester.h,tilelink_two_port_tester.cpp:  tilelink_two_port_tester.ivy tilelink_abstract_spec.ivy tilelink_concrete_spec.ivy
	ivy_to_cpp isolate=iso_b tilelink_two_port_tester.ivy

