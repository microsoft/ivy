/* This is a wrapper for the C++ simulator of the RocketChip Coherence
   manager. */

/* Issues for BroadcastHub:


*/

#include "tilelink_two_port_dut.h"
#include "L2Unit.DefaultCPPConfig.h"
#include "hash.h"

using namespace hash_space;

int to_a_type(int own, int op){
    switch(own) {
    case 0:
        switch (op) {
        case 0: return 0b000; // getType
        case 1: return 0b010; // putType
        case 2: return 0b100; // putAtomicType
        }
    case 1:
        return 0; // acquireShared
    case 2:
        return 1; // acquireExclusive
    }
}

int to_r_type(int voluntary, int dirty){
    // TODO: temporary!!! All voluntary releases contain data
    if (voluntary)
        return 0b000;  // releaseInvalidateData
    if (!dirty) 
        return 0b011; // releaseInvalidateAck
    return 0b000;  // releaseInvalidateData
}

// TODO: we don't have any exclusive grant without data (grantExclusiveAck)
int to_g_type(int own){
    switch(own) {
    case 0: 0b000; // TODO: what for uncached?
    case 1: 0b000; // grantShared
    case 2: 0b001; // grantExclusive
    }
}

int to_g_own(int is_builtin_type, int g_type){
    if (is_builtin_type)
        return 0;
    if (g_type == 0b000)
        return 1;
    return 2;
}

bool to_g_relack(int is_builtin_type, int g_type){
    if (is_builtin_type)
        return g_type == 0b000;
    return false;
}

int to_a_own(int is_builtin_type, int a_type){
    if (is_builtin_type)
        return 0;
    if (a_type == 0b000)
        return 1;
    return 2;
}

int to_a_op(int a_type){
    switch (a_type) {
    case 0b000 : return 0; // getType
    case 0b010 : return 1; // putType
    case 0b100 : return 2; // putAtomicType
    case 0b001 : return 0; // getBlock
    case 0b011 : return 1; // putBlock
    }
    std::cout << "unknown a_type:" << a_type << "\n";
    return 0; // unknown type

}

class tilelink_coherence_manager : public tilelink_two_port_dut {

    /* This is the "inner" port */
  
  struct my_manager_port : public manager_port {
    L2Unit_t &dut;

    hash_map<int, hash_map<std::pair<int,int>,int> > client_txid_to_addr_hi;
    hash_map<int, hash_map<std::pair<int,int>,int> > client_txid_to_ltime;
    hash_map<int, hash_map<int,int> > client_rls_txid_to_addr_hi;

    my_manager_port(L2Unit_t &_dut) : dut(_dut) {}

    void set_acquire(bool send, const acquire &a){
        dut.L2Unit__io_inner_acquire_valid = LIT<1>(send);
        dut.L2Unit__io_inner_acquire_bits_client_id = LIT<2>(a.cid);        
        dut.L2Unit__io_inner_acquire_bits_client_xact_id = LIT<2>(a.id_);
        dut.L2Unit__io_inner_acquire_bits_is_builtin_type = LIT<1>(a.own == 0);
        dut.L2Unit__io_inner_acquire_bits_addr_beat = LIT<2>(a.word);
        dut.L2Unit__io_inner_acquire_bits_a_type = LIT<3>(to_a_type(a.own,a.op));
        dut.L2Unit__io_inner_acquire_bits_union = LIT<17>(0); // TODO: what here?
        dut.L2Unit__io_inner_acquire_bits_addr_block = LIT<26>(a.addr_hi);
        dut.L2Unit__io_inner_acquire_bits_data = LIT<128>(a.data_);
        if(send) {
            client_txid_to_addr_hi[a.cid][std::pair<int,int>(a.id_,a.own)] = a.addr_hi;
            client_txid_to_ltime[a.cid][std::pair<int,int>(a.id_,a.own)] = a.ltime_;
        }
    }
    bool get_acquire_ready(){
        return dut.L2Unit__io_inner_acquire_ready.values[0];
    }
    void set_finish(bool send, const finish &a){
        dut.L2Unit__io_inner_finish_valid = LIT<1>(send);
        dut.L2Unit__io_inner_finish_bits_manager_xact_id = LIT<4>(a.id_);
        if (send) {
            //            std::cout << "finish_manager_xact = " << dut.L2Unit__io_inner_finish_bits_manager_xact_id.values[0] << "\n";
        }
    }
    bool get_finish_ready(){
        return dut.L2Unit__io_inner_finish_ready.values[0];
    }
    void set_release(bool send, const release &a){
        dut.L2Unit__io_inner_release_valid = LIT<1>(send);
        dut.L2Unit__io_inner_release_bits_voluntary = LIT<1>(a.voluntary);
        dut.L2Unit__io_inner_release_bits_client_xact_id = LIT<2>(a.id_);
        dut.L2Unit__io_inner_release_bits_client_id = LIT<2>(a.cid);        
        dut.L2Unit__io_inner_release_bits_addr_beat = LIT<2>(a.word);
        dut.L2Unit__io_inner_release_bits_r_type = LIT<3>(to_r_type(a.voluntary,a.dirty));
        dut.L2Unit__io_inner_release_bits_addr_block = LIT<26>(a.addr_hi);
        dut.L2Unit__io_inner_release_bits_data = LIT<128>(a.data_);
        if (send) {
            client_rls_txid_to_addr_hi[a.cid][a.id_] = a.addr_hi;
        }
    }
    bool get_release_ready(){
        return dut.L2Unit__io_inner_release_ready.values[0];
    }
    bool get_grant(grant &a){
        a.own = to_g_own(dut.L2Unit__io_inner_grant_bits_is_builtin_type.values[0],
                         dut.L2Unit__io_inner_grant_bits_g_type.values[0]);
        a.word = dut.L2Unit__io_inner_grant_bits_addr_beat.values[0];
        a.clnt_txid = dut.L2Unit__io_inner_grant_bits_client_xact_id.values[0];
        a.mngr_txid = dut.L2Unit__io_inner_grant_bits_manager_xact_id.values[0];
        a.relack = to_g_relack(dut.L2Unit__io_inner_grant_bits_is_builtin_type.values[0],
                               dut.L2Unit__io_inner_grant_bits_g_type.values[0]);
        a.cid = dut.L2Unit__io_inner_grant_bits_client_id.values[0];
        a.data_ = dut.L2Unit__io_inner_grant_bits_data.values[0];
        a.addr_hi = a.relack ? client_rls_txid_to_addr_hi[a.cid][a.clnt_txid] : client_txid_to_addr_hi[a.cid][std::pair<int,int>(a.clnt_txid,a.own)];
        a.ltime_ = client_txid_to_ltime[a.cid][std::pair<int,int>(a.clnt_txid,a.own)];
        bool send = dut.L2Unit__io_inner_grant_valid.values[0];
        if (send) {
            //            std::cout << "grant_manager_xact = " << dut.L2Unit__io_inner_grant_bits_manager_xact_id.values[0] << " relack = " << a.relack  << "\n";
        }
        return send;
    }
    void set_grant_ready(bool b){
        dut.L2Unit__io_inner_grant_ready = LIT<1>(b);
    }
    bool get_probe(probe &a){
        // TODO: handle L2Unit__io_inner_probe_bits_p_type
        // TODO: don't have client id bits yet
        a.cid = dut.L2Unit__io_inner_probe_bits_client_id.values[0];
        a.addr_hi = dut.L2Unit__io_inner_probe_bits_addr_block.values[0];
        return dut.L2Unit__io_inner_probe_valid.values[0];
    }
    void set_probe_ready(bool b){
        dut.L2Unit__io_inner_probe_ready = LIT<1>(b);
    }
  };

  struct my_client_port : public client_port {

    L2Unit_t &dut;

      hash_map<int,int> manager_txid_to_client_txid;
      hash_map<int,int> manager_txid_to_addr_hi;
      hash_map<int,int> manager_txid_to_word;
      hash_map<int,int> manager_txid_to_own;


    my_client_port(L2Unit_t &_dut) : dut(_dut) {}

    bool get_acquire(acquire &a){
        a.cid = dut.L2Unit__io_inner_acquire_bits_client_id.values[0];
        // TODO: high bit of txid seems to be used for something I don't understand
        a.id_ = dut.L2Unit__io_outer_acquire_bits_client_xact_id.values[0] & 0x07L;
        a.own = to_a_own(dut.L2Unit__io_outer_acquire_bits_is_builtin_type.values[0],
                         dut.L2Unit__io_outer_acquire_bits_a_type.values[0]);
        a.word = dut.L2Unit__io_outer_acquire_bits_addr_beat.values[0];
        a.op = to_a_op(dut.L2Unit__io_outer_acquire_bits_a_type.values[0]);
        // dut.L2Unit__io_outer_acquire_bits_union -- TODO: what here?
        a.addr_hi = dut.L2Unit__io_outer_acquire_bits_addr_block.values[0];
        a.data_ = a.op ? dut.L2Unit__io_outer_acquire_bits_data.values[0] : 0;
        a.ltime_ = 0;
        return dut.L2Unit__io_outer_acquire_valid.values[0];
    }
    void set_acquire_ready(bool b){
        dut.L2Unit__io_outer_acquire_ready = LIT<1>(b);
    }
    bool get_finish(finish &a){
#if 0
        // No finish messages on uncached port!!!!
        int mid = dut.L2Unit__io_outer_finish_bits_manager_xact_id.values[0];
        a.id_ = mid;
        a.addr_hi = manager_txid_to_addr_hi[mid];
        a.word = manager_txid_to_word[mid];
        a.own = manager_txid_to_own[mid];
        return dut.L2Unit__io_outer_finish_valid.values[0];
#endif
        return false;
    }
    void set_finish_ready(bool b){
        // TODO: no such port -- ignore!!!
    }
    bool get_release(release &a){
        // No such port!
        return false;
    }
    void set_release_ready(bool b){
        // No such port!
    }
    void set_grant(bool send, const grant &a){
        dut.L2Unit__io_outer_grant_valid = LIT<1>(send);
        dut.L2Unit__io_outer_grant_bits_is_builtin_type = LIT<1>(a.own == 0);
        dut.L2Unit__io_outer_grant_bits_addr_beat = LIT<2>(a.word);
        dut.L2Unit__io_outer_grant_bits_client_xact_id = LIT<2>(a.clnt_txid);
        // TODO: this doesn't seem to exist in emulator code
        // dut.L2Unit__io_outer_grant_bits_client_id = LIT<2>(a.cid);        
        dut.L2Unit__io_outer_grant_bits_manager_xact_id = LIT<4>(a.mngr_txid);
        dut.L2Unit__io_outer_grant_bits_g_type = LIT<3>(to_g_type(a.own));
        dut.L2Unit__io_outer_grant_bits_data = LIT<128>(a.data_);
        if(send){
            manager_txid_to_addr_hi[a.mngr_txid] = a.addr_hi;
            manager_txid_to_word[a.mngr_txid] = a.word;
            manager_txid_to_own[a.mngr_txid] = a.own;
        }
    }
    bool get_grant_ready(){
        return dut.L2Unit__io_outer_grant_ready.values[0];
    }
    void set_probe(bool send, const probe &a){
        assert(!send && "there is no outer probe port!");
    }
    bool get_probe_ready(){
      return false;
    }
  };

  my_manager_port *m_mp;
  my_client_port *m_cp;
  // The chisel generated code
  L2Unit_t dut;

  
  virtual manager_port *mp(){
    return m_mp;
  }

  virtual client_port *cp(){
    return m_cp;
  }

  virtual void clock(){
      dut.clock_lo(LIT<1>(0),true);
      dut.clock_hi(LIT<1>(0));
  }

public:
  tilelink_coherence_manager(){
      m_mp = new my_manager_port(dut);
      m_cp = new my_client_port(dut);

      dut.init(rand());

      // reset a couple of clocks
      
      dut.clock_lo(LIT<1>(1),true);
      dut.clock_hi(LIT<1>(1));
      dut.clock_lo(LIT<1>(1),true);
      dut.clock_hi(LIT<1>(1));
  }  

  ~tilelink_coherence_manager(){
      delete m_mp;
      delete m_cp;
  }
};

tilelink_two_port_dut *create_tilelink_two_port_dut() {
  return new tilelink_coherence_manager();
}
