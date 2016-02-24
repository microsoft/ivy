BIN=tilelink_two_port_tester

$(BIN): tilelink_two_port_tester.h tilelink_two_port_tester.cpp hash.h hash.cpp main.cpp tilelink_two_port_dut.h tilelink_queue_model.cpp
	g++ -g -I $(Z3DIR)/include -L $(Z3DIR)/lib -o $(BIN) main.cpp tilelink_two_port_tester.cpp hash.cpp  tilelink_queue_model.cpp -lz3

tilelink_two_port_tester.h,tilelink_two_port_tester.cpp:  tilelink_two_port_tester.ivy tilelink_abstract_spec.ivy tilelink_concrete_spec.ivy
	ivy_to_cpp isolate=iso_b tilelink_two_port_tester.ivy

L2UNITGEN = $(L2UNITDIR)/generated-src
L2UNITOBJ = $(L2UNITGEN)/L2Unit.DefaultCPPConfig-0.o $(L2UNITGEN)/L2Unit.DefaultCPPConfig-1.o

tilelink_coherence_manager: tilelink_two_port_tester.h tilelink_two_port_tester.cpp hash.h hash.cpp main.cpp tilelink_two_port_dut.h tilelink_coherence_manager.cpp $(L2UNITGEN)/L2Unit.DefaultCPPConfig.h $(L2UNITOBJ)
	g++ -g -I $(Z3DIR)/include -I $(L2UNITGEN) -L $(Z3DIR)/lib -o $(BIN) main.cpp tilelink_two_port_tester.cpp hash.cpp tilelink_coherence_manager.cpp $(L2UNITOBJ) -lz3

#	g++ -g  -I/home/mcmillan/projects/rocket-chip/riscv/include -I/home/mcmillan/projects/rocket-chip/csrc -I/home/mcmillan/projects/rocket-chip/dramsim2 -include /home/mcmillan/projects/rocket-chip/l2_unit/generated-src/L2Unit.DefaultCPPConfig.scr_map.h -include /home/mcmillan/projects/rocket-chip/l2_unit/generated-src/L2Unit.DefaultCPPConfig.h -include /home/mcmillan/projects/rocket-chip/l2_unit/generated-src/consts.DefaultCPPConfig.h -I/home/mcmillan/projects/rocket-chip/l2_unit/generated-src -c -o L2Unit.DefaultCPPConfig-0.o L2Unit.DefaultCPPConfig-0.cpp