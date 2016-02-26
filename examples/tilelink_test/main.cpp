#include <iostream>
#include "tilelink_coherence_manager_tester.h"
#include "tilelink_two_port_dut.h"

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
 
int main(){
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

    for (int j = 0; j < 1; j++) {

        std::cout << "initializing\n";
        if (!ig.generate(tb)){
            std::cout << " no initial states!";
            break;
        }

	// For now, make all the memory cached on front

	tb.front__cached[0] = 1;
	tb.front__cached[1] = 1;
	tb.front__cached[2] = 1;
	tb.front__cached[3] = 1;
	tb.front__cached_hi[0] = 1;
	tb.front__cached_hi[1] = 1;

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

	for (int cycle = 0; cycle < 1000; cycle++) {

	  // beginning of clock cycle

	  // tee up input messages for the dut

          // we buffer the input messages so that we can present more
          // than one input in a clock cycle.  TODO: we ought to
          // dequeue these messages randomly.

	  
          if (rand() % 2 && acq_i.size() < BUF_MAX && cag.generate(tb)) {
              acquire acq_g = {cag.id_,cag.addr_hi,cag.word,cag.own,cag.op,cag.data_,cag.ltime_};
	      tb.ext__c__acquire(acq_g.id_,acq_g.addr_hi,acq_g.word,acq_g.own,acq_g.op, acq_g.data_, acq_g.ltime_);
              acq_i.push_back(acq_g);
          }
          acq_gen = acq_i.size();
          if (acq_gen) acq_m = acq_i[0];
          dut.mp()->set_acquire(acq_gen,acq_m);
	  
          if (rand() % 2 && fns_i.size() < BUF_MAX && cfg.generate(tb)) {
              finish fns_g = {cfg.id_, cfg.addr_hi, cfg.word, cfg.own};
              tb.ext__c__finish(fns_g.id_, fns_g.addr_hi, fns_g.word, fns_g.own);
              fns_i.push_back(fns_g);
          }
          fns_gen = fns_i.size();
          if (fns_gen) fns_m = fns_i[0];
          dut.mp()->set_finish(fns_gen,fns_m);

          if (rand() % 2 && rls_i.size() < BUF_MAX && crg.generate(tb)) {
              release rls_g = {crg.id_, crg.voluntary, crg.addr_hi, crg.word, crg.dirty, crg.data_};
              tb.ext__c__release(rls_g.id_, rls_g.voluntary, rls_g.addr_hi, rls_g.word, rls_g.dirty, rls_g.data_);
              rls_i.push_back(rls_g);
          }
          rls_gen = rls_i.size();
          if (rls_gen) rls_m = rls_i[0];
          dut.mp()->set_release(rls_gen,rls_m);

          if (rand() % 2 && gnt_i.size() < BUF_MAX && mgg.generate(tb)) {
              grant gnt_g = {mgg.id_,mgg.word,mgg.own,mgg.relack,mgg.data_,mgg.addr_hi,0 /* mgg.ltime_ */};
	      tb.ext__m__grant(gnt_g.id_,gnt_g.word,gnt_g.own,gnt_g.relack,gnt_g.data_,gnt_g.addr_hi,gnt_g.ltime_);
              gnt_i.push_back(gnt_g);
          }
          gnt_gen = gnt_i.size();
          if (gnt_gen) gnt_c = gnt_i[0];
          dut.cp()->set_grant(gnt_gen,gnt_c);

          if (rand() % 2 && prb_i.size() < BUF_MAX && mpg.generate(tb)) {
              probe prb_g = {0 /* mpg.id_ */, 0 /* mpg.addr_hi */};
              tb.ext__m__probe(prb_g.id_, prb_g.addr_hi);
              prb_i.push_back(prb_g);
          }
          prb_gen = prb_i.size();
          if (prb_gen) prb_c = prb_i[0];
          dut.cp()->set_probe(prb_gen,prb_c);

	  // choose ready signals for dut outputs

	  bool acq_ready = rand() % 2;
	  bool fns_ready = rand() % 2;
	  bool rls_ready = rand() % 2;
	  bool gnt_ready = rand() % 2;
	  bool prb_ready = rand() % 2;
	  dut.cp()->set_acquire_ready(acq_ready);
	  dut.cp()->set_finish_ready(fns_ready);
	  dut.cp()->set_release_ready(rls_ready);
	  dut.mp()->set_grant_ready(gnt_ready);
	  dut.mp()->set_probe_ready(prb_ready);
	  
          std::cout << "====clock====\n";
	  dut.clock();

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
            tb.ext__b__acquire(acq_c.id_,acq_c.addr_hi,acq_c.word,acq_c.own,acq_c.op,acq_c.data_,acq_c.ltime_);
          }
	  if (fns_send & fns_ready){
	    std::cout << "output: " << fns_c << std::endl;
            tb.ext__b__finish(fns_c.id_, fns_c.addr_hi, fns_c.word, fns_c.own);
          }
	  if (rls_send & rls_ready){
	    std::cout << "output: " << rls_c << std::endl;
            tb.ext__b__release(rls_c.id_, rls_c.voluntary, rls_c.addr_hi, rls_c.word, rls_c.dirty, rls_c.data_);
          }
	  if (gnt_send & gnt_ready){
            std::cout << "output: " << gnt_m << std::endl;
	    tb.ext__b__grant(gnt_m.id_,gnt_m.word,gnt_m.own,gnt_m.relack,gnt_m.data_,gnt_m.addr_hi,gnt_m.ltime_);
          }
	  if (prb_send & prb_ready){
            std::cout << "output: " << prb_m << std::endl;
	    tb.ext__b__probe(prb_m.id_, prb_m.addr_hi);
          }



	  // end of clock cycle
	}	  


    }
}

void ivy_assert(bool c){
    if (!c) {
        std::cerr << "assert failed\n";
    }
}

void ivy_assume(bool c){
    if (!c) {
        std::cerr << "assume failed\n";
    }
}

int choose(int rng, int label){
    return 0;
}
