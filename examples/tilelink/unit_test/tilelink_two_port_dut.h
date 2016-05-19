#include<iostream>

struct tilelink_two_port_dut {

  struct acquire {
    int cid;
    int id_;
    int addr_hi;
    int word;
    int own;
    int op;
    int data_;
    int block;
    int ltime_;

    friend std::ostream & operator<<(std::ostream & out, acquire const &a) {
      out << "acquire{";
      out << "cid = " << a.cid << ", ";
      out << "id_ = " << a.id_ << ", ";
      out << "addr_hi = " << a.addr_hi << ", ";
      out << "word = " << a.word << ", ";
      out << "own = " << a.own << ", ";
      out << "op = " << a.op << ", ";
      out << "data_ = " << a.data_ << ", ";
      out << "block = " << a.block << ", ";
      out << "ltime_ = " << a.ltime_ << "";
      out << "}";
    }
  };

  struct finish {
    int cid;
    int id_;
    int addr_hi;
    int word;
    int own;

    friend std::ostream & operator<<(std::ostream & out, finish const &a) {
      out << "finish{";
      out << "cid = " << a.cid << ", ";
      out << "id_ = " << a.id_ << ", ";
      out << "addr_hi = " << a.addr_hi << ", ";
      out << "word = " << a.word << ", ";
      out << "own = " << a.own << "";
      out << "}";
    }
  };

  struct release {
    int cid;
    int id_;
    int voluntary;
    int addr_hi;
    int word;
    int dirty;
    int data_;

    friend std::ostream & operator<<(std::ostream & out, release const &a) {
      out << "release{";
      out << "cid = " << a.cid << ", ";
      out << "id_ = " << a.id_ << ", ";
      out << "voluntary = " << a.voluntary << ", ";
      out << "addr_hi = " << a.addr_hi << ", ";
      out << "word = " << a.word << ", ";
      out << "dirty = " << a.dirty << ", ";
      out << "data_ = " << a.data_ << "";
      out << "}";
    }
  };

  struct grant {
    int cid;
    int clnt_txid;
    int mngr_txid;
    int word;
    int own;
    int relack;
    int data_;
    int addr_hi;
    int ltime_;

    friend std::ostream & operator<<(std::ostream & out, grant const &a) {
      out << "grant{";
      out << "cid = " << a.cid << ", ";
      out << "clnt_txid = " << a.clnt_txid << ", ";
      out << "mngr_txid = " << a.mngr_txid << ", ";
      out << "word = " << a.word << ", ";
      out << "own = " << a.own << ", ";
      out << "relack = " << a.relack << ", ";
      out << "data_ = " << a.data_ << ", ";
      out << "addr_hi = " << a.addr_hi << ", ";
      out << "ltime_ = " << a.ltime_ << "";
      out << "}";
    }
  };

  struct probe {
    int cid;
    int id_;
    int addr_hi;

    friend std::ostream & operator<<(std::ostream & out, probe const &a) {
      out << "probe{";
      out << "cid = " << a.cid << ", ";
      out << "id_ = " << a.id_ << ", ";
      out << "addr_hi = " << a.addr_hi << "";
      out << "}";
    }

  };

  struct manager_port {
    virtual void set_acquire(bool send, const acquire &) = 0;
    virtual bool get_acquire_ready() = 0;
    virtual void set_finish(bool send, const finish &) = 0;
    virtual bool get_finish_ready() = 0;
    virtual void set_release(bool send, const release &) = 0;
    virtual bool get_release_ready() = 0;
    virtual bool get_grant(grant &) = 0;
    virtual void set_grant_ready(bool) = 0;
    virtual bool get_probe(probe &) = 0;
    virtual void set_probe_ready(bool) = 0;
  };

  struct client_port {
    virtual bool get_acquire(acquire &) = 0;
    virtual void set_acquire_ready(bool) = 0;
    virtual bool get_finish(finish &) = 0;
    virtual void set_finish_ready(bool) = 0;
    virtual bool get_release(release &) = 0;
    virtual void set_release_ready(bool) = 0;
    virtual void set_grant(bool send, const grant &) = 0;
    virtual bool get_grant_ready() = 0;
    virtual void set_probe(bool send, const probe &) = 0;
    virtual bool get_probe_ready() = 0;
  };    

  virtual client_port *cp() = 0;
  virtual manager_port *mp() = 0;
  virtual void clock() = 0;
  virtual unsigned cached_clients() = 0;
  virtual ~tilelink_two_port_dut() {};
};


tilelink_two_port_dut *create_tilelink_two_port_dut(int stride);

