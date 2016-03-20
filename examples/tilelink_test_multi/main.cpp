#include <iostream>
#include <stdexcept>
#include "tilelink_coherence_manager_tester.h"
#include "tilelink_two_port_dut.h"
#include <sys/types.h>
#include <unistd.h>

struct rgen : public ivy_gen {
  virtual int choose(int rng,const char *name) {
    return rand() % rng;
  }
};

typedef tilelink_two_port_dut::acquire acquire;
typedef tilelink_two_port_dut::finish finish;
typedef tilelink_two_port_dut::release release;
typedef tilelink_two_port_dut::grant grant;
typedef tilelink_two_port_dut::probe probe;
 
void mutate_memory(tilelink_coherence_manager_tester & tb){
    int client = rand() % tb.__CARD__client_id;
    int addr = rand() % tb.__CARD__addr;
    if (tb.front__excl_p[client][addr]) {
        int data = rand() % tb.__CARD__data;
        tb.ref__mem[addr] = data;
        tb.front__dirt_p[client][addr] = 1;
        std::cout << "write(cid = " << client << ", addr = " << addr << ", data = " << data << "\n";
    }
}

void usage(){
    std::cerr << "usage: [options] [random-seed] \n";
    std::cerr << "options: \n";
    std::cerr << "  -c <int>    max clock cycles per trace\n";
    std::cerr << "  -t <int>    max number of traces\n";
    std::cerr << "  -r          delay voluntary releases\n";
    std::cerr << "  -a          delay uncached acquire if vol release\n";
    std::cerr << "  -u          one uncached client\n";
    std::cerr << "  -d          inject random delays for progress testing";
    exit(1);
}

struct delay {
    bool on;
    int time, off_cycle, on_cycle;
    bool enabled;
    delay() {time = 0; enabled = false; on = false;}
    void enable(int _off_cycle, int _on_cycle) {
        enabled = true;
        off_cycle = _off_cycle;
        on_cycle = _on_cycle;
        on = false;
        time = time = rand() % off_cycle;
    }
    bool tick(){
        if (!enabled) return false;
        if (time == 0) {
            if (on) {
                on = false;
                time = rand() % off_cycle;
            }
            else {
                on = true;
                time = rand() % on_cycle;
            }
        }
        else
            time--;
        return on;
    }
};

int main(int argc, const char **argv){

    unsigned random_seed = (unsigned)time(NULL) ^ (unsigned)getpid();
      
    int arg = 1;
    bool delay_rels = false;
    bool delay_acqs = false;
    bool inject_delays = false;
    bool uncached_client = false;
    int max_cycles = 1000;
    int max_traces = 1;

    while (arg < argc) {
        // option -c: max clock cycles per trace
        if (arg < argc - 1 && argv[arg] == std::string("-c")) {
            arg++;
            max_cycles = atoi(argv[arg++]);
        }
        // option -c: max number of traces
        if (arg < argc - 1 && argv[arg] == std::string("-t")) {
            arg++;
            max_traces = atoi(argv[arg++]);
        }
        // option -r: delay voluntary release to work around L2 cache bug
        else if (argv[arg] == std::string("-r")) {
            arg++;
            delay_rels = true;
        }
        // option -a: delay uncached acquire if voluntary release to work around BroadcastHub bug
        else if (argv[arg] == std::string("-a")) {
            arg++;
            delay_acqs = true;
        }
        // option -d: delay uncached acquire if voluntary release to work around BroadcastHub bug
        else if (argv[arg] == std::string("-d")) {
            arg++;
            inject_delays = true;
        }
        // option -u: one uncached and one cached client
        else if (argv[arg] == std::string("-u")) {
            arg++;
            uncached_client = true;
        }
        else break;
    }        

    if (argc > arg){
        if (!isdigit(argv[arg][0]))
            usage();
        random_seed = atoi(argv[arg++]);
    }
        
    if (arg != argc) {
        usage();
    }

    srand(random_seed);


    for (int j = 0; j < max_traces; j++) {

        tilelink_coherence_manager_tester tb;
        tilelink_two_port_dut *dut_ptr = create_tilelink_two_port_dut();
        tilelink_two_port_dut &dut = *dut_ptr;

        init_gen ig;
        ext__c__acquire_gen cag;
        ext__c__finish_gen cfg;
        ext__c__release_gen crg;
        ext__c__perform_gen cpg;
        ext__m__grant_gen mgg;
        ext__m__probe_gen mpg;

        int rel_del = 0;

        std::cout << "initializing\n";
        if (!ig.generate(tb)){
            std::cout << " no initial states!";
            break;
        }

	// For now, make all the memory cached on front

        for (int cl = 0; cl < 2; cl++){
            for (int a = 0; a < 4; a++) 
                tb.front__cached[cl][a] = 1 ? (cl == 0 || !uncached_client) : 0;
            for (int a = 0; a < 2; a++)
                tb.front__cached_hi[cl][a] = 1 ? (cl == 0 || !uncached_client) : 0;
        }

        // Assume front interface is ordered

        tb.front__ordered = 1;
        
#if 0
	tb.back__cached[0] = 0;
	tb.back__cached[1] = 0;
	tb.back__cached[2] = 0;
	tb.back__cached[3] = 0;
	tb.back__cached_hi[0] = 0;
	tb.back__cached_hi[1] = 0;
#endif

	rgen rg;
	tb.___ivy_gen = &rg;

        // buffers for input messages to design

        std::vector<acquire> acq_i;
        std::vector<finish> fns_i;
        std::vector<release> rls_i;
        std::vector<grant> gnt_i;
        std::vector<probe> prb_i;

        int BUF_MAX = 1;

        acquire acq_m;
        finish fns_m;
        release rls_m;
        grant gnt_c;
        probe prb_c;

        bool acq_gen,fns_gen,rls_gen,gnt_gen,prb_gen;

        delay delays[10];
        if (inject_delays)
            for (int i = 0; i < 10; i++)
                delays[i].enable(100,200);

        int all_events_serialized = -1;

	for (int cycle = 0; cycle < max_cycles; cycle++) {

          if (all_events_serialized == -1) {
              bool all_done = true;
              for(int lt = 0; lt < tb.__CARD__ltime; lt++)
                  if (!tb.ref__evs__serialized[lt])
                      all_done = false;
              if (all_done)
                  all_events_serialized = cycle;
          }
          else if (cycle == all_events_serialized + 100) {
              std::cout << "all events done, ending trace\n";
              break;
          }

	  // beginning of clock cycle

            mutate_memory(tb);

	  // tee up input messages for the dut

            //            int the_addr_hi,the_word;
            //          tb.ext__c__acquire(1,0,the_addr_hi,the_word,0,tb.ref__evs__type_[0],tb.ref__evs__data_[0],0,0);


          // we buffer the input messages so that we can present more
          // than one input in a clock cycle.  TODO: we ought to
          // dequeue these messages randomly.

	  
          if (!delays[0].tick() && rand() % 2 && acq_i.size() < BUF_MAX && cag.generate(tb)) {
              acquire acq_g = {cag.cid,cag.id_,cag.addr_hi,cag.word,cag.own,cag.op,cag.data_,0 /* cag.block */,cag.ltime_};
	      tb.ext__c__acquire(acq_g.cid,acq_g.id_,acq_g.addr_hi,acq_g.word,acq_g.own,acq_g.op, acq_g.data_, acq_g.block, acq_g.ltime_);
              acq_i.push_back(acq_g);
              std::cout << "gen: " << acq_g << std::endl;
          }
          acq_gen = acq_i.size();
          if (acq_gen) acq_m = acq_i[0];
          dut.mp()->set_acquire(acq_gen,acq_m);
	  
          if (!delays[1].tick() && rand() % 2 && fns_i.size() < BUF_MAX && cfg.generate(tb)) {
              finish fns_g = {cfg.cid, cfg.id_, cfg.addr_hi, cfg.word, cfg.own};
              tb.ext__c__finish(fns_g.cid, fns_g.id_, fns_g.addr_hi, fns_g.word, fns_g.own);
              fns_i.push_back(fns_g);
              std::cout << "gen: " << fns_g << std::endl;
          }
          fns_gen = fns_i.size();
          if (fns_gen) fns_m = fns_i[0];
          dut.mp()->set_finish(fns_gen,fns_m);

          if (!delays[2].tick() && rand() % 2 && rls_i.size() < BUF_MAX && crg.generate(tb)) {
              release rls_g = {crg.cid, crg.id_, crg.voluntary, crg.addr_hi, crg.word, crg.dirty, crg.data_};
              tb.ext__c__release(rls_g.cid, rls_g.id_, rls_g.voluntary, rls_g.addr_hi, rls_g.word, rls_g.dirty, rls_g.data_);
              rls_i.push_back(rls_g);
              std::cout << "gen: " << rls_g << std::endl;
              rel_del = (delay_rels && crg.voluntary) ? 6 : 0;
          }
          rls_gen = rls_i.size() && !rel_del;
          if (rel_del) rel_del--;  
          if (rls_gen) rls_m = rls_i[0];
          dut.mp()->set_release(rls_gen,rls_m);

          // if workaround, don't input a vol release and uncached acquire in same cycle
          if (delay_acqs && rls_gen && rls_m.voluntary && acq_gen && acq_m.own == 0){
              acq_gen = false;
              dut.mp()->set_acquire(false,acq_m);
          }
              
          if (!delays[3].tick() && rand() % 2 && gnt_i.size() < BUF_MAX && mgg.generate(tb)) {
              grant gnt_g = {0 /* mgg.cid */, mgg.clnt_txid, mgg.mngr_txid, mgg.word,mgg.own,mgg.relack,mgg.data_,mgg.addr_hi,0 /* mgg.ltime_ */};
	      tb.ext__m__grant(gnt_g.cid, gnt_g.clnt_txid,gnt_g.clnt_txid,gnt_g.word,gnt_g.own,gnt_g.relack,gnt_g.data_,gnt_g.addr_hi,gnt_g.ltime_);
              gnt_i.push_back(gnt_g);
              std::cout << "gen: " << gnt_g << std::endl;
          }
          gnt_gen = gnt_i.size();
          if (gnt_gen) gnt_c = gnt_i[0];
          dut.cp()->set_grant(gnt_gen,gnt_c);

          if (!delays[4].tick() && rand() % 2 && prb_i.size() < BUF_MAX && mpg.generate(tb)) {
              probe prb_g = {0 /* mpg.cid */, 0 /* mpg.id_ */, 0 /* mpg.addr_hi */};
              tb.ext__m__probe(prb_g.cid, prb_g.id_, prb_g.addr_hi);
              prb_i.push_back(prb_g);
              std::cout << "gen: " << prb_g << std::endl;
          }
          prb_gen = prb_i.size();
          if (prb_gen) prb_c = prb_i[0];
          dut.cp()->set_probe(prb_gen,prb_c);

	  // choose ready signals for dut outputs

          bool acq_delayed = delays[5].tick();
	  bool acq_ready = rand() % 2 && !acq_delayed;
	  bool fns_ready = !delays[6].tick() && rand() % 2;
	  bool rls_ready = !delays[7].tick() && rand() % 2;
	  bool gnt_ready = !delays[8].tick() && rand() % 2;
	  bool prb_ready = !delays[9].tick() && rand() % 2;

	  dut.cp()->set_acquire_ready(acq_ready);
	  dut.cp()->set_finish_ready(fns_ready);
	  dut.cp()->set_release_ready(rls_ready);
	  dut.mp()->set_grant_ready(gnt_ready);
	  dut.mp()->set_probe_ready(prb_ready);
	  
          std::cout << "====clock " << cycle << "====\n";
          try {
              dut.clock();
          }
          catch (const std::runtime_error &err) {
              std::cerr << err.what() << "\n";
              return 1;
          }

          // dequeue the accepted messages

          if (acq_gen && dut.mp()->get_acquire_ready()){
	      std::cout << "input: " << acq_m << std::endl;
              acq_i.erase(acq_i.begin());
          }

          if (fns_gen && dut.mp()->get_finish_ready()){
	      std::cout << "input: " << fns_m << std::endl;
              fns_i.erase(fns_i.begin());
          }

          if (rls_gen && dut.mp()->get_release_ready()){
	      std::cout << "input: " << rls_m << std::endl;
              rls_i.erase(rls_i.begin());
          }

          if (gnt_gen && dut.cp()->get_grant_ready()){
	      std::cout << "input: " << gnt_c << std::endl;
              gnt_i.erase(gnt_i.begin());
	  }

          if (prb_gen && dut.cp()->get_probe_ready()){
	      std::cout << "input: " << prb_c << std::endl;
              prb_i.erase(prb_i.begin());
          }

	  // get the dut outputs

	  acquire acq_c;
	  bool acq_send = dut.cp()->get_acquire(acq_c);
 	  finish fns_c;
	  bool fns_send = dut.cp()->get_finish(fns_c);
	  release rls_c;
	  bool rls_send = dut.cp()->get_release(rls_c);
	  grant gnt_m;
	  bool gnt_send = dut.mp()->get_grant(gnt_m);
	  probe prb_m;
	  bool prb_send = dut.mp()->get_probe(prb_m);
	    
	  // check the dut outputs, advancing tester state

	  if (acq_send & acq_ready){
	    std::cout << "output: " << acq_c << std::endl;
            if (acq_c.own == 0 && !acq_c.block){
                // TEMPORARY: treat non-block memory ops as uncached and perform them
                // on behalf of the DUT (in principle, DUT should do this). We need a better
                // way to distinguish ops from uncached clients.
                tb.ref__perform(acq_c.ltime_,tb.buf_id);
            }
            tb.ext__b__acquire(acq_c.cid,acq_c.id_,acq_c.addr_hi,acq_c.word,acq_c.own,acq_c.op,acq_c.data_,acq_c.block,acq_c.ltime_);
          }
	  if (fns_send & fns_ready){
	    std::cout << "output: " << fns_c << std::endl;
            tb.ext__b__finish(fns_c.cid, fns_c.id_, fns_c.addr_hi, fns_c.word, fns_c.own);
          }
	  if (rls_send & rls_ready){
	    std::cout << "output: " << rls_c << std::endl;
            tb.ext__b__release(rls_c.cid, rls_c.id_, rls_c.voluntary, rls_c.addr_hi, rls_c.word, rls_c.dirty, rls_c.data_);
          }
	  if (gnt_send & gnt_ready){
            std::cout << "output: " << gnt_m << std::endl;
	    tb.ext__b__grant(gnt_m.cid,gnt_m.clnt_txid,gnt_m.mngr_txid,gnt_m.word,gnt_m.own,gnt_m.relack,gnt_m.data_,gnt_m.addr_hi,gnt_m.ltime_);
          }
	  if (prb_send & prb_ready){
            std::cout << "output: " << prb_m << std::endl;
	    tb.ext__b__probe(prb_m.cid,prb_m.id_, prb_m.addr_hi);
          }

          tb.back_acq_rdy = acq_ready || !acq_send; 
          if (!tb.back_acq_rdy) std::cout << "outer acq blocked";
          tb.__tick(50);

	  // end of clock cycle
	}	  

        delete dut_ptr;
    }
}

void my_error() {
    exit(1);
}

void ivy_assert(bool c){
    if (!c) {
        std::cerr << "assert failed\n";
        std::cout << "assert failed\n";
        my_error();
    }
}

void ivy_assume(bool c){
    if (!c) {
        std::cerr << "assume failed\n";
        std::cout << "assume failed\n";
        my_error();
    }
}

void ivy_check_progress(int guarantee_ticks, int assume_ticks){
    //    std::cout << "check_progress: " << guarantee_ticks << "," << assume_ticks << "\n";
    if (guarantee_ticks > 50 && assume_ticks < 10) {
        std::cerr << "progress property failed\n";
        std::cout << "progress property failed\n";
        my_error();
    }
}

int choose(int rng, int label){
    return 0;
}
