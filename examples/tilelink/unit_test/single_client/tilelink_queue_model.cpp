#include "tilelink_two_port_dut.h"
#include <vector>

#define QUEUE_SIZE 4

class tilelink_queue_model : public tilelink_two_port_dut {

  struct port_data {
    acquire acq;
    finish fns;
    release rls;
    grant gnt;
    probe prb;
    bool acq_send,fns_send,rls_send,gnt_send,prb_send;
    bool acq_ready,fns_ready,rls_ready,gnt_ready,prb_ready;
  };
  
  struct my_manager_port : public manager_port {
    port_data pd;
    void set_acquire(bool send, const acquire &a){
      pd.acq_send = send, pd.acq = a;
    }
    bool get_acquire_ready(){
      return pd.acq_ready;
    }
    void set_finish(bool send, const finish &a){
      pd.fns_send = send, pd.fns = a;
    }
    bool get_finish_ready(){
      return pd.fns_ready;
    }
    void set_release(bool send, const release &a){
      pd.rls_send = send, pd.rls = a;
    }
    bool get_release_ready(){
      return pd.rls_ready;
    }
    bool get_grant(grant &a){
      a = pd.gnt;
      return pd.gnt_send;
    }
    void set_grant_ready(bool b){
      pd.gnt_ready = b;
    }
    bool get_probe(probe &a){
      a = pd.prb;
      return pd.prb_send;
    }
    void set_probe_ready(bool b){
      pd.prb_ready = b;
    }
  };

  struct my_client_port : public client_port {
    port_data pd;

    bool get_acquire(acquire &a){
      a = pd.acq;
      return pd.acq_send;
    }
    void set_acquire_ready(bool b){
      pd.acq_ready = b;
    }
    bool get_finish(finish &a){
      a = pd.fns;
      return pd.fns_send;
    }
    void set_finish_ready(bool b){
      pd.fns_ready = b;
    }
    bool get_release(release &a){
      a = pd.rls;
      return pd.rls_send;
    }
    void set_release_ready(bool b){
      pd.rls_ready = b;
    }
    void set_grant(bool send, const grant &a){
      pd.gnt_send = send, pd.gnt = a;
    }
    bool get_grant_ready(){
      return pd.gnt_ready;
    }
    void set_probe(bool send, const probe &a){
      pd.prb_send = send, pd.prb = a;
    }
    bool get_probe_ready(){
      return pd.prb_ready;
    }
  };

  my_manager_port m_mp;
  my_client_port m_cp;

  std::vector<acquire> acq_q;
  std::vector<finish> fns_q;
  std::vector<release> rls_q;
  std::vector<grant> gnt_q;
  std::vector<probe> prb_q;
  
  virtual manager_port *mp(){
    return &m_mp;
  }

  virtual client_port *cp(){
    return &m_cp;
  }

  virtual void clock(){
    if(m_cp.pd.acq_send && m_cp.pd.acq_ready){
      acq_q.erase(acq_q.begin());
      m_cp.pd.acq_send = acq_q.size();
      m_mp.pd.acq_ready = true;
      if (acq_q.size()) m_cp.pd.acq = acq_q.front();
    }      
    if(m_cp.pd.fns_send && m_cp.pd.fns_ready){
      fns_q.erase(fns_q.begin());
      m_cp.pd.fns_send = fns_q.size();
      m_mp.pd.fns_ready = true;
      if (fns_q.size()) m_cp.pd.fns = fns_q.front();
    }      
    if(m_cp.pd.rls_send && m_cp.pd.rls_ready){
      rls_q.erase(rls_q.begin());
      m_cp.pd.rls_send = rls_q.size();
      m_mp.pd.rls_ready = true;
      if (rls_q.size()) m_cp.pd.rls = rls_q.front();
    }      
    if(m_mp.pd.gnt_send && m_mp.pd.gnt_ready){
      gnt_q.erase(gnt_q.begin());
      m_mp.pd.gnt_send = gnt_q.size();
      m_cp.pd.gnt_ready = true;
      if (gnt_q.size()) m_mp.pd.gnt = gnt_q.front();
    }      
    if(m_mp.pd.prb_send && m_mp.pd.prb_ready){
      prb_q.erase(prb_q.begin());
      m_mp.pd.prb_send = prb_q.size();
      m_cp.pd.prb_ready = true;
      if (prb_q.size()) m_mp.pd.prb = prb_q.front();
    }      
    if(m_mp.pd.acq_send && m_mp.pd.acq_ready){
      acq_q.push_back(m_mp.pd.acq);
      m_mp.pd.acq_ready = acq_q.size() < QUEUE_SIZE;
      m_cp.pd.acq_send = true;
      m_cp.pd.acq = acq_q[0];
    }      
    if(m_mp.pd.fns_send && m_mp.pd.fns_ready){
      fns_q.push_back(m_mp.pd.fns);
      m_mp.pd.fns_ready = fns_q.size() < QUEUE_SIZE;
      m_cp.pd.fns_send = true;
      m_cp.pd.fns = fns_q[0];
    }
    if(m_mp.pd.rls_send && m_mp.pd.rls_ready){
      rls_q.push_back(m_mp.pd.rls);
      m_mp.pd.rls_ready = rls_q.size() < QUEUE_SIZE;
      m_cp.pd.rls_send = true;
      m_cp.pd.rls = rls_q[0];
    }      
    if(m_cp.pd.gnt_send && m_cp.pd.gnt_ready){
      gnt_q.push_back(m_cp.pd.gnt);
      m_cp.pd.gnt_ready = gnt_q.size() < QUEUE_SIZE;
      m_mp.pd.gnt_send = true;
      m_mp.pd.gnt = gnt_q[0];
    }      
    if(m_cp.pd.prb_send && m_cp.pd.prb_ready){
      prb_q.push_back(m_cp.pd.prb);
      m_cp.pd.prb_ready = prb_q.size() < QUEUE_SIZE;
      m_mp.pd.prb_send = true;
      m_mp.pd.prb = prb_q[0];
    }      
  }

public:
  tilelink_queue_model(){
    m_mp.pd.acq_ready = true;
    m_mp.pd.fns_ready = true;
    m_mp.pd.rls_ready = true;
    m_cp.pd.gnt_ready = true;
    m_cp.pd.prb_ready = true;
    m_cp.pd.acq_send = false;
    m_cp.pd.fns_send = false;
    m_cp.pd.rls_send = false;
    m_mp.pd.gnt_send = false;
    m_mp.pd.prb_send = false;
  }  


};

tilelink_two_port_dut *create_tilelink_two_port_dut() {
  return new tilelink_queue_model();
}
