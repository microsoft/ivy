#include<iostream>

struct tilelink_two_port_dut {

  struct acquire {
    int id_;
    int addr_hi;
    int word;
    int own;
    int op;
    int data_;
    int ltime_;

    friend std::ostream & operator<<(std::ostream & out, acquire const &a) {
      out << "acquire{";
      out << "ltime_ = " << a.ltime_ << ", ";
      out << "own = " << a.own << ", ";
      out << "word = " << a.word << ", ";
      out << "addr_hi = " << a.addr_hi << ", ";
      out << "id_ = " << a.id_ << ", ";
      out << "data_ = " << a.data_ << ", ";
      out << "op = " << a.op << "";
      out << "}";
    }
  };

  struct finish {
    int id_;
    int addr_hi;
    int word;
    int own;
  };

  struct release {
    int id_;
    int voluntary;
    int addr_hi;
    int word;
    int dirty;
    int data_;
  };

  struct grant {
    int id_;
    int word;
    int own;
    int relack;
    int data_;
    int addr_hi;
    int ltime_;

    friend std::ostream & operator<<(std::ostream & out, grant const &a) {
      out << "grant{";
      out << "id_ = " << a.id_ << ", ";
      out << "word = " << a.word << ", ";
      out << "own = " << a.own << ", ";
      out << "relack = " << a.relack << ", ";
      out << "data_ = " << a.data_ << ", ";
      out << "addr_hi = " << a.addr_hi << ", ";
      out << "ltime_ = " << a.ltime_ << "";
      out << "";
    }
  };

  struct probe {
    int id_;
    int addr_hi;
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
  virtual ~tilelink_two_port_dut() {};
};


tilelink_two_port_dut *create_tilelink_two_port_dut();

