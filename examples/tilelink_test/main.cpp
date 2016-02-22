#include <iostream>
#include "tilelink_two_port_tester.h"
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
    tilelink_two_port_tester tb;
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

	// For now, make all the memory cached

	tb.front__cached[0] = 1;
	tb.front__cached[1] = 1;
	tb.front__cached[2] = 1;
	tb.front__cached[3] = 1;
	tb.front__cached_hi[0] = 1;
	tb.front__cached_hi[1] = 1;

	tb.back__cached[0] = 1;
	tb.back__cached[1] = 1;
	tb.back__cached[2] = 1;
	tb.back__cached[3] = 1;
	tb.back__cached_hi[0] = 1;
	tb.back__cached_hi[1] = 1;

	rgen rg;
	tb.___ivy_gen = &rg;

	for (int cycle = 0; cycle < 100; cycle++) {

	  // beginning of clock cycle

	  // tee up input messages for the dut
	  
	  acquire dummy_acq;
	  dut.mp()->set_acquire(false,dummy_acq);
	  
	  if (dut.mp()->get_acquire_ready() && rand() % 2) {
	    if (cag.generate(tb)) {

	      // advance the tester state
	      tb.ext__c__acquire(cag.id_,cag.addr_hi,cag.word,cag.own,cag.op, cag.data_, cag.ltime_);

	      // generate message for dut 
	      acquire acq_m = {cag.id_,cag.addr_hi,cag.word,cag.own,cag.op,cag.data_,cag.ltime_};
	      dut.mp()->set_acquire(true,acq_m);

	      std::cout << "input: " << acq_m << std::endl;
	    }
	  }	    

	  finish dummy_fns;
	  dut.mp()->set_finish(false,dummy_fns);
	  
	  if (dut.mp()->get_finish_ready() && rand() % 2) {
	    if (cfg.generate(tb)) {

	      // advance the tester state
              tb.ext__c__finish(cfg.id_, cfg.addr_hi, cfg.word, cfg.own);

	      // generate message for dut 
	      finish fns_m = {cfg.id_, cfg.addr_hi, cfg.word, cfg.own};
	      dut.mp()->set_finish(true,fns_m);

	      std::cout << "input: " << fns_m << std::endl;
	    }
	  }	    

	  release dummy_rls;
	  dut.mp()->set_release(false,dummy_rls);
	  
	  if (dut.mp()->get_release_ready() && rand() % 2) {
	    if (crg.generate(tb)) {

	      // advance the tester state
              tb.ext__c__release(crg.id_, crg.voluntary, crg.addr_hi, crg.word, crg.dirty, crg.data_);

	      // generate message for dut 
	      release rls_m = {crg.id_, crg.voluntary, crg.addr_hi, crg.word, crg.dirty, crg.data_};
	      dut.mp()->set_release(true,rls_m);

	      std::cout << "input: " << rls_m << std::endl;
	    }
	  }	    

	  grant dummy_gnt;
	  dut.cp()->set_grant(false,dummy_gnt);

	  if (dut.cp()->get_grant_ready() && rand() % 2) {
	    if (mgg.generate(tb)) {

	      // advance the tester state
	      tb.ext__m__grant(mgg.id_,mgg.word,mgg.own,mgg.relack,mgg.data_,mgg.addr_hi,mgg.ltime_);
	      
	      // generate message for dut 
	      grant gnt_c = {mgg.id_,mgg.word,mgg.own,mgg.relack,mgg.data_,mgg.addr_hi,mgg.ltime_};
	      dut.cp()->set_grant(true,gnt_c);

	      std::cout << "input: " << gnt_c << std::endl;
	    }
	  }

	  probe dummy_prb;
	  dut.cp()->set_probe(false,dummy_prb);

	  if (dut.cp()->get_probe_ready() && rand() % 2) {
	    if (mpg.generate(tb)) {

	      // advance the tester state
              tb.ext__m__probe(0 /* mpg.id_ */, mpg.addr_hi);
	      
	      // generate message for dut 
              probe prb_c = {0 /* mpg.id_ */, mpg.addr_hi};
	      dut.cp()->set_probe(true,prb_c);

	      std::cout << "input: " << prb_c << std::endl;
	    }
	  }

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

	  // clock the dut

          std::cout << "====clock====\n";
	  dut.clock();

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
