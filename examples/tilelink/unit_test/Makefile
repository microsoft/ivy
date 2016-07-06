################################################################################
# Parameters you can set

#L2Config = DefaultL2Config

#L2Config = W1Cached1WaysConfig
 L2Config = W1Cached2WaysConfig
# L2Config = W2Cached1WaysConfig
# L2Config = W2Cached2WaysConfig

################################################################################
# Don't change after this

all: test_L2HellaCacheBank test_L2BroadcastHub

# Generic tester for L2 (inner TL = L1, outer TL = MC)

tilelink_coherence_manager_tester.h tilelink_coherence_manager_tester.cpp:  tilelink_coherence_manager_tester.ivy tilelink_abstract_spec.ivy tilelink_concrete_spec.ivy
	ivy_to_cpp isolate=iso_b tilelink_coherence_manager_tester.ivy

# Make L2HellaCacheBank emulator

srcdir = $(shell pwd)

L2HellaCacheBank/L2HellaCacheBank.o: $(ROCKETCHIP)/uncore/src/main/scala/Builder.scala
	install -d L2HellaCacheBank
	export CXX='g++ -g' && cd $(ROCKETCHIP) && sbt "project uncore" "run agents.L2HellaCacheBank $(L2Config) --backend c --genHarness --compile --debug --vcd --ioDebug --targetDir $(srcdir)/L2HellaCacheBank"

L2HellaCacheBank/L2HellaCacheBank.prms.h: L2HellaCacheBank/L2HellaCacheBank.o
	sed -e 's/(/#define /' -e 's/,/ /' -e 's/)//' L2HellaCacheBank/agents.L2HellaCacheBank.prm > L2HellaCacheBank/L2HellaCacheBank.prms.h

tilelink_coherence_manager_hella.cpp: tilelink_coherence_manager.cpp 
	sed -e 's/managerEndpoint_//g' -e 's/L2Unit_/L2HellaCacheBank_/g' tilelink_coherence_manager.cpp > tilelink_coherence_manager_hella.cpp

test_L2HellaCacheBank: tilelink_coherence_manager_tester.h tilelink_coherence_manager_tester.cpp tilelink_coherence_manager_hella.cpp hash.h hash.cpp main.cpp tilelink_two_port_dut.h tilelink_hella_cache.cpp L2HellaCacheBank/L2HellaCacheBank.o L2HellaCacheBank/L2HellaCacheBank.prms.h
	g++ -g -I $(Z3DIR)/include -I L2HellaCacheBank -L $(Z3DIR)/lib -o test_L2HellaCacheBank main.cpp tilelink_coherence_manager_tester.cpp hash.cpp tilelink_hella_cache.cpp L2HellaCacheBank/L2HellaCacheBank.o -lz3

# Make L2BroadcastHub emulator

L2BroadcastHub/L2BroadcastHub.o: $(ROCKETCHIP)/uncore/src/main/scala/Builder.scala
	install -d L2BroadcastHub
	export CXX='g++ -g' && cd $(ROCKETCHIP) && sbt "project uncore" "run agents.L2BroadcastHub $(L2Config) --backend c --genHarness --compile --debug --vcd --ioDebug --targetDir $(srcdir)/L2BroadcastHub"

L2BroadcastHub/L2BroadcastHub.prms.h: L2BroadcastHub/L2BroadcastHub.o
	sed -e 's/(/#define /' -e 's/,/ /' -e 's/)//' L2BroadcastHub/agents.L2BroadcastHub.prm > L2BroadcastHub/L2BroadcastHub.prms.h

#L2BroadcastHub/L2BroadcastHub_fixed.o: L2BroadcastHub/L2BroadcastHub_fixed.cpp
#	g++ -g -c -o L2BroadcastHub/L2BroadcastHub_fixed.o -I L2BroadcastHub -I $(ROCKETCHIP)/csrc L2BroadcastHub/L2BroadcastHub_fixed.cpp

tilelink_coherence_manager_bcast.cpp: tilelink_coherence_manager.cpp 
	sed -e 's/managerEndpoint_//g' -e 's/L2Unit_/L2BroadcastHub_/g' tilelink_coherence_manager.cpp > tilelink_coherence_manager_bcast.cpp

test_L2BroadcastHub: tilelink_coherence_manager_tester.h tilelink_coherence_manager_tester.cpp tilelink_coherence_manager_bcast.cpp hash.h hash.cpp main.cpp tilelink_two_port_dut.h tilelink_broadcast_hub.cpp L2BroadcastHub/L2BroadcastHub.o L2BroadcastHub/L2BroadcastHub.prms.h
	g++ -g -I $(Z3DIR)/include -I L2BroadcastHub -L $(Z3DIR)/lib -o test_L2BroadcastHub main.cpp tilelink_coherence_manager_tester.cpp hash.cpp tilelink_broadcast_hub.cpp L2BroadcastHub/L2BroadcastHub.o -lz3

clean:
	rm -f tilelink_coherence_manager_tester.h tilelink_coherence_manager_tester.cpp L2HellaCacheBank/* L2BroadcastHub/*
	rmdir L2HellaCacheBank L2BroadcastHub
