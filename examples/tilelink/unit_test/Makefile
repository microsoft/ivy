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

$(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig-2.o: $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig-2.cpp $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig.h
	g++ -g  -I$(ROCKETCHIP)/riscv/include -I$(ROCKETCHIP)/csrc -I$(ROCKETCHIP)/dramsim2 -include $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig.scr_map.h -include $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig.h -include $(L2BROADCASTGEN)/consts.DefaultCPPConfig.h -I$(L2BROADCASTGEN) -c -o $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig-2.o $(L2BROADCASTGEN)/L2Unit.DefaultCPPConfig-2.cpp

# Apply generic tester to L2 cache

L2CACHEGEN = $(ROCKETCHIP)/l2_cache/generated-src-debug
L2CACHECONFIG = DefaultL2CPPConfig
L2CACHEBASE = L2Unit.$(L2CACHECONFIG)
L2CACHEOBJ = $(L2CACHEGEN)/$(L2CACHEBASE)-0.o $(L2CACHEGEN)/$(L2CACHEBASE)-1.o $(L2CACHEGEN)/$(L2CACHEBASE)-2.o

tilelink_l2_cache: tilelink_coherence_manager_tester.h tilelink_coherence_manager_tester.cpp tilelink_coherence_manager.cpp hash.h hash.cpp main.cpp tilelink_two_port_dut.h tilelink_l2_cache.cpp $(L2CACHEGEN)/$(L2CACHEBASE).h $(L2CACHEOBJ)
	g++ -g -I $(Z3DIR)/include -I $(L2CACHEGEN) -L $(Z3DIR)/lib -o tilelink_l2_cache main.cpp tilelink_coherence_manager_tester.cpp hash.cpp tilelink_l2_cache.cpp $(L2CACHEOBJ) -lz3

$(L2CACHEGEN)/$(L2CACHEBASE)-0.o: $(L2CACHEGEN)/$(L2CACHEBASE)-0.cpp $(L2CACHEGEN)/$(L2CACHEBASE).h
	g++ -g  -I$(ROCKETCHIP)/riscv/include -I$(ROCKETCHIP)/csrc -I$(ROCKETCHIP)/dramsim2 -include $(L2CACHEGEN)/$(L2CACHEBASE).scr_map.h -include $(L2CACHEGEN)/$(L2CACHEBASE).h -include $(L2CACHEGEN)/consts.$(L2CACHECONFIG).h -I$(L2CACHEGEN) -c -o $(L2CACHEGEN)/$(L2CACHEBASE)-0.o $(L2CACHEGEN)/$(L2CACHEBASE)-0.cpp

$(L2CACHEGEN)/$(L2CACHEBASE)-1.o: $(L2CACHEGEN)/$(L2CACHEBASE)-1.cpp $(L2CACHEGEN)/$(L2CACHEBASE).h
	g++ -g  -I$(ROCKETCHIP)/riscv/include -I$(ROCKETCHIP)/csrc -I$(ROCKETCHIP)/dramsim2 -include $(L2CACHEGEN)/$(L2CACHEBASE).scr_map.h -include $(L2CACHEGEN)/$(L2CACHEBASE).h -include $(L2CACHEGEN)/consts.$(L2CACHECONFIG).h -I$(L2CACHEGEN) -c -o $(L2CACHEGEN)/$(L2CACHEBASE)-1.o $(L2CACHEGEN)/$(L2CACHEBASE)-1.cpp

# Make L2HellaCacheBank emulator

srcdir = $(shell pwd)

L2HellaCacheBank/L2HellaCacheBank.o:
	install -d L2HellaCacheBank
	export CXX='g++ -g' && cd $(ROCKETCHIP) && sbt "project uncore" "run L2HellaCacheBank DefaultL2Config --backend c --genHarness --compile --debug --vcd --ioDebug --targetDir $(srcdir)/L2HellaCacheBank"

L2HellaCacheBank/L2HellaCacheBank.prms.h: L2HellaCacheBank/L2HellaCacheBank.o
	sed -e 's/(/#define /' -e 's/,/ /' -e 's/)//' L2HellaCacheBank/L2HellaCacheBank.prm > L2HellaCacheBank/L2HellaCacheBank.prms.h

tilelink_coherence_manager_hella.cpp: tilelink_coherence_manager.cpp 
	sed -e 's/managerEndpoint_//g' -e 's/L2Unit_/L2HellaCacheBank_/g' tilelink_coherence_manager.cpp > tilelink_coherence_manager_hella.cpp

test_L2HellaCacheBank: tilelink_coherence_manager_tester.h tilelink_coherence_manager_tester.cpp tilelink_coherence_manager_hella.cpp hash.h hash.cpp main.cpp tilelink_two_port_dut.h tilelink_hella_cache.cpp L2HellaCacheBank/L2HellaCacheBank.h L2HellaCacheBank/L2HellaCacheBank.o L2HellaCacheBank/L2HellaCacheBank.prms.h
	g++ -g -I $(Z3DIR)/include -I L2HellaCacheBank -L $(Z3DIR)/lib -o test_L2HellaCacheBank main.cpp tilelink_coherence_manager_tester.cpp hash.cpp tilelink_hella_cache.cpp L2HellaCacheBank/L2HellaCacheBank.o -lz3

# Make L2BroadcastHub emulator

L2BroadcastHub/L2BroadcastHub.o:
	install -d L2BroadcastHub
	export CXX='g++ -g' && cd $(ROCKETCHIP) && sbt "project uncore" "run L2BroadcastHub DefaultL2Config --backend c --genHarness --compile --debug --vcd --ioDebug --targetDir $(srcdir)/L2BroadcastHub"

L2BroadcastHub/L2BroadcastHub.prms.h: L2BroadcastHub/L2BroadcastHub.o
	sed -e 's/(/#define /' -e 's/,/ /' -e 's/)//' L2BroadcastHub/L2BroadcastHub.prm > L2BroadcastHub/L2BroadcastHub.prms.h

#L2BroadcastHub/L2BroadcastHub_fixed.o: L2BroadcastHub/L2BroadcastHub_fixed.cpp
#	g++ -g -c -o L2BroadcastHub/L2BroadcastHub_fixed.o -I L2BroadcastHub -I $(ROCKETCHIP)/csrc L2BroadcastHub/L2BroadcastHub_fixed.cpp

tilelink_coherence_manager_bcast.cpp: tilelink_coherence_manager.cpp 
	sed -e 's/managerEndpoint_//g' -e 's/L2Unit_/L2BroadcastHub_/g' tilelink_coherence_manager.cpp > tilelink_coherence_manager_bcast.cpp

test_L2BroadcastHub: tilelink_coherence_manager_tester.h tilelink_coherence_manager_tester.cpp tilelink_coherence_manager_bcast.cpp hash.h hash.cpp main.cpp tilelink_two_port_dut.h tilelink_broadcast_hub.cpp L2BroadcastHub/L2BroadcastHub.o L2BroadcastHub/L2BroadcastHub.prms.h
	g++ -g -I $(Z3DIR)/include -I L2BroadcastHub -L $(Z3DIR)/lib -o test_L2BroadcastHub main.cpp tilelink_coherence_manager_tester.cpp hash.cpp tilelink_broadcast_hub.cpp L2BroadcastHub/L2BroadcastHub.o -lz3

