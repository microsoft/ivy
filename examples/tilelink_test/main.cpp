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
    ext__c__perform_gen cpg;
    ext__m__grant_gen mgg;

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

	while(1) {

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

	  if (acq_send)
	    tb.ext__b__acquire(acq_c.id_,acq_c.addr_hi,acq_c.word,acq_c.own,acq_c.op,acq_c.data_,acq_c.ltime_);
	  if (gnt_send)
	    tb.ext__b__grant(gnt_m.id_,gnt_m.word,gnt_m.own,gnt_m.relack,gnt_m.data_,gnt_m.addr_hi,gnt_m.ltime_);

	  // clock the dut

	  dut.clock();

	  // end of clock cycle
	}	  

#if 0
	tb.ext__c__acquire(0 /* id_ */,
			   0 /* addr_hi */,
			   0 /* word */,
			   1 /* own */,
			   0 /* op */, 
			   0 /* data_ */, 
			   0 /* ltime_ */);


	tb.ext__b__acquire(0 /* id_ */,
			   0 /* addr_hi */,
			   0 /* word */,
			   1 /* own */,
			   0 /* op */, 
			   0 /* data_ */, 
			   0 /* ltime_ */);
#endif

        if (cag.generate(tb)) {
	  std::cout << "ACQUIRE:\n";
            std::cout << "ltime_ = " << cag.ltime_ << "\n";
            std::cout << "own = " << cag.own << "\n";
            std::cout << "word = " << cag.word << "\n";
            std::cout << "addr_hi = " << cag.addr_hi << "\n";
            std::cout << "id_ = " << cag.id_ << "\n";
            std::cout << "data_ = " << cag.data_ << "\n";
            std::cout << "op = " << cag.op << "\n";
	    tb.ext__c__acquire(cag.id_,
			       cag.addr_hi,
			       cag.word,
			       cag.own,
			       cag.op, 
			       cag.data_, 
			       cag.ltime_);

	    struct tilelink_two_port_dut::acquire acq_m = {cag.id_,
				   cag.addr_hi,
				   cag.word,
				   cag.own,
				   cag.op, 
				   cag.data_, 
				   cag.ltime_};
	    
	    dut.mp()->set_acquire(true,acq_m);

	    dut.clock();

	    dut.mp()->set_acquire(false,acq_m);
	    dut.cp()->set_acquire_ready(true);

	    struct tilelink_two_port_dut::acquire acq_c;
	    bool send = dut.cp()->get_acquire(acq_c);
	    
	    dut.clock();

	    if (send) {
	      
		    tb.ext__b__acquire(acq_c.id_,
				       acq_c.addr_hi,
				       acq_c.word,
				       acq_c.own,
				       acq_c.op, 
				       acq_c.data_, 
				       acq_c.ltime_);
            }
        }
        else {
            std::cout << "deadlock";
            break;
        }            

        if (mgg.generate(tb)) {
	    std::cout << "GRANT:\n";
	    std::cout << "id_ = " << mgg.id_ << "\n";
	    std::cout << "word = " << mgg.word << "\n";
	    std::cout << "own = " << mgg.own << "\n";
	    std::cout << "relack = " << mgg.relack << "\n";
	    std::cout << "data_ = " << mgg.data_ << "\n";
	    
	    std::cout << "addr_hi = " << mgg.addr_hi << "\n";
	    std::cout << "ltime_ = " << mgg.ltime_ << "\n";
	    tb.ext__m__grant(mgg.id_,
			     mgg.word,
			     mgg.own,
			     mgg.relack,
			     mgg.data_,
			     mgg.addr_hi,
			     mgg.ltime_);

	    struct tilelink_two_port_dut::grant gnt_c = {mgg.id_,
			     mgg.word,
			     mgg.own,
			     mgg.relack,
			     mgg.data_,
			     mgg.addr_hi,
			     mgg.ltime_};
	    
	    dut.cp()->set_grant(true,gnt_c);

	    dut.clock();

	    dut.cp()->set_grant(false,gnt_c);
	    dut.mp()->set_grant_ready(true);

	    struct tilelink_two_port_dut::grant gnt_m;
	    bool send = dut.mp()->get_grant(gnt_m);
	    
	    dut.clock();

	    if (send) {

	      tb.ext__b__grant(gnt_m.id_,
			       gnt_m.word,
			       gnt_m.own,
			       gnt_m.relack,
			       gnt_m.data_,
			       gnt_m.addr_hi,
			       gnt_m.ltime_);
	    }
        }
        else {
            std::cout << "deadlock";
            break;
        }            

	// make up a read event we can do now
	
	int addr = tb.addr_cons[mgg.addr_hi][mgg.word];
	tb.ref__evs__type_[0] = 0;
	tb.ref__evs__addr_[0] = addr;
	tb.ref__evs__id_[0] = tb.c_id;
	tb.ext__c__perform(0,tb.c_id);


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
