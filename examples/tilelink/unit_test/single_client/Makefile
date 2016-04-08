BIN=tilelink_two_port_tester

$(BIN): tilelink_two_port_tester.h tilelink_two_port_tester.cpp hash.h hash.cpp main.cpp tilelink_two_port_dut.h tilelink_queue_model.cpp
	g++ -g -I $(Z3DIR)/include -L $(Z3DIR)/lib -o $(BIN) main.cpp tilelink_two_port_tester.cpp hash.cpp  tilelink_queue_model.cpp -lz3

# Generic tester for L2 (inner TL = L1, outer TL = MC)

tilelink_two_port_tester.h tilelink_two_port_tester.cpp:  tilelink_two_port_tester.ivy tilelink_abstract_spec.ivy tilelink_concrete_spec.ivy
	ivy_to_cpp isolate=iso_b tilelink_two_port_tester.ivy

tilelink_coherence_manager_tester.h tilelink_coherence_manager_tester.cpp:  tilelink_coherence_manager_tester.ivy tilelink_abstract_spec.ivy tilelink_concrete_spec.ivy
	ivy_to_cpp isolate=iso_b tilelink_coherence_manager_tester.ivy

# Apply generic tester to BroadcastHub

L2BROADCASTGEN = $(ROCKETCHIP)/l2_broadcast/generated-src
L2BROADCASTOBJ = $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig-0.o $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig-1.o

tilelink_l2_broadcast: tilelink_coherence_manager_tester.h tilelink_coherence_manager_tester.cpp hash.h hash.cpp main.cpp tilelink_two_port_dut.h tilelink_l2_broadcast.cpp $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig.h $(L2BROADCASTOBJ)
	g++ -g -I $(Z3DIR)/include -I $(L2BROADCASTGEN) -L $(Z3DIR)/lib -o tilelink_coherence_manager main.cpp tilelink_coherence_manager_tester.cpp hash.cpp tilelink_l2_broadcast.cpp $(L2BROADCASTOBJ) -lz3

$(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig-0.o: $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig-0.cpp $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig.h
	g++ -g  -I$(ROCKETCHIP)/riscv/include -I$(ROCKETCHIP)/csrc -I$(ROCKETCHIP)/dramsim2 -include $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig.scr_map.h -include $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig.h -include $(L2BROADCASTGEN)/consts.DefaultCPPConfig.h -I$(L2BROADCASTGEN) -c -o $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig-0.o $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig-0.cpp

$(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig-1.o: $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig-1.cpp $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig.h
	g++ -g  -I$(ROCKETCHIP)/riscv/include -I$(ROCKETCHIP)/csrc -I$(ROCKETCHIP)/dramsim2 -include $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig.scr_map.h -include $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig.h -include $(L2BROADCASTGEN)/consts.DefaultCPPConfig.h -I$(L2BROADCASTGEN) -c -o $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig-1.o $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig-1.cpp

# Apply generic tester to L2 cache

L2CACHEGEN = $(ROCKETCHIP)/l2_cache/generated-src-debug
L2CACHECONFIG = DefaultL2CPPConfig
L2CACHEBASE = L2Unit.$(L2CACHECONFIG)
L2CACHEOBJ = $(L2CACHEGEN)/$(L2CACHEBASE)-0.o $(L2CACHEGEN)/$(L2CACHEBASE)-1.o

tilelink_l2_cache: tilelink_coherence_manager_tester.h tilelink_coherence_manager_tester.cpp tilelink_coherence_manager.cpp hash.h hash.cpp main.cpp tilelink_two_port_dut.h tilelink_l2_cache.cpp $(L2CACHEGEN)/$(L2CACHEBASE).h $(L2CACHEOBJ)
	g++ -g -I $(Z3DIR)/include -I $(L2CACHEGEN) -L $(Z3DIR)/lib -o tilelink_l2_cache main.cpp tilelink_coherence_manager_tester.cpp hash.cpp tilelink_l2_cache.cpp $(L2CACHEOBJ) -lz3

$(L2CACHEGEN)/$(L2CACHEBASE)-0.o: $(L2CACHEGEN)/$(L2CACHEBASE)-0.cpp $(L2CACHEGEN)/$(L2CACHEBASE).h
	g++ -g  -I$(ROCKETCHIP)/riscv/include -I$(ROCKETCHIP)/csrc -I$(ROCKETCHIP)/dramsim2 -include $(L2CACHEGEN)/$(L2CACHEBASE).scr_map.h -include $(L2CACHEGEN)/$(L2CACHEBASE).h -include $(L2CACHEGEN)/consts.$(L2CACHECONFIG).h -I$(L2CACHEGEN) -c -o $(L2CACHEGEN)/$(L2CACHEBASE)-0.o $(L2CACHEGEN)/$(L2CACHEBASE)-0.cpp

$(L2CACHEGEN)/$(L2CACHEBASE)-1.o: $(L2CACHEGEN)/$(L2CACHEBASE)-1.cpp $(L2CACHEGEN)/$(L2CACHEBASE).h
	g++ -g  -I$(ROCKETCHIP)/riscv/include -I$(ROCKETCHIP)/csrc -I$(ROCKETCHIP)/dramsim2 -include $(L2CACHEGEN)/$(L2CACHEBASE).scr_map.h -include $(L2CACHEGEN)/$(L2CACHEBASE).h -include $(L2CACHEGEN)/consts.$(L2CACHECONFIG).h -I$(L2CACHEGEN) -c -o $(L2CACHEGEN)/$(L2CACHEBASE)-1.o $(L2CACHEGEN)/$(L2CACHEBASE)-1.cpp
