BIN=tilelink_two_port_tester

$(BIN): tilelink_two_port_tester.h tilelink_two_port_tester.cpp hash.h hash.cpp main.cpp tilelink_two_port_dut.h tilelink_queue_model.cpp
	g++ -g -I $(Z3DIR)/include -L $(Z3DIR)/lib -o $(BIN) main.cpp tilelink_two_port_tester.cpp hash.cpp  tilelink_queue_model.cpp -lz3

tilelink_two_port_tester.h tilelink_two_port_tester.cpp:  tilelink_two_port_tester.ivy tilelink_abstract_spec.ivy tilelink_concrete_spec.ivy
	ivy_to_cpp isolate=iso_b tilelink_two_port_tester.ivy

L2UNITGEN = $(L2UNITDIR)/generated-src
L2UNITOBJ = $(L2UNITGEN)/L2Unit.DefaultCPPConfig-0.o $(L2UNITGEN)/L2Unit.DefaultCPPConfig-1.o

tilelink_coherence_manager_tester.h tilelink_coherence_manager_tester.cpp:  tilelink_coherence_manager_tester.ivy tilelink_abstract_spec.ivy tilelink_concrete_spec.ivy
	ivy_to_cpp isolate=iso_b tilelink_coherence_manager_tester.ivy

tilelink_coherence_manager: tilelink_coherence_manager_tester.h tilelink_coherence_manager_tester.cpp hash.h hash.cpp main.cpp tilelink_two_port_dut.h tilelink_coherence_manager.cpp $(L2UNITGEN)/L2Unit.DefaultCPPConfig.h $(L2UNITOBJ)
	g++ -g -I $(Z3DIR)/include -I $(L2UNITGEN) -L $(Z3DIR)/lib -o tilelink_coherence_manager main.cpp tilelink_coherence_manager_tester.cpp hash.cpp tilelink_coherence_manager.cpp $(L2UNITOBJ) -lz3

$(L2UNITGEN)/L2Unit.DefaultCPPConfig-0.o: $(L2UNITGEN)/L2Unit.DefaultCPPConfig-0.cpp $(L2UNITGEN)/L2Unit.DefaultCPPConfig.h
	g++ -g  -I$(ROCKETCHIP)/riscv/include -I$(ROCKETCHIP)/csrc -I$(ROCKETCHIP)/dramsim2 -include $(L2UNITGEN)/L2Unit.DefaultCPPConfig.scr_map.h -include $(L2UNITGEN)/L2Unit.DefaultCPPConfig.h -include $(L2UNITGEN)/consts.DefaultCPPConfig.h -I$(L2UNITGEN) -c -o $(L2UNITGEN)/L2Unit.DefaultCPPConfig-0.o $(L2UNITGEN)/L2Unit.DefaultCPPConfig-0.cpp

$(L2UNITGEN)/L2Unit.DefaultCPPConfig-1.o: $(L2UNITGEN)/L2Unit.DefaultCPPConfig-1.cpp $(L2UNITGEN)/L2Unit.DefaultCPPConfig.h
	g++ -g  -I$(ROCKETCHIP)/riscv/include -I$(ROCKETCHIP)/csrc -I$(ROCKETCHIP)/dramsim2 -include $(L2UNITGEN)/L2Unit.DefaultCPPConfig.scr_map.h -include $(L2UNITGEN)/L2Unit.DefaultCPPConfig.h -include $(L2UNITGEN)/consts.DefaultCPPConfig.h -I$(L2UNITGEN) -c -o $(L2UNITGEN)/L2Unit.DefaultCPPConfig-1.o $(L2UNITGEN)/L2Unit.DefaultCPPConfig-1.cpp
