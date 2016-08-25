#include "struct1.h"

#include <sstream>
#include <algorithm>

#include <iostream>
#include <stdlib.h>
#include <sys/types.h>          /* See NOTES */
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/ip.h> 
#include <sys/select.h>
#include <string.h>
#include <stdio.h>
#include <string>
#include <unistd.h>
typedef struct1 ivy_class;

class reader {
public:
    virtual int fdes() = 0;
    virtual void read() = 0;
};
void install_reader(reader *);
class timer {
public:
    virtual int ms_delay() = 0;
    virtual void timeout() = 0;
};
void install_timer(timer *);
int struct1::___ivy_choose(int rng,const char *name,int id) {
        return 0;
    }
void struct1::a(int c, int d){
    {
        v.first = c;
        v.second = d;
        ivy_assert(((v.first == c) && (v.second == d)), "struct1.ivy: line 16");
    }
}
int struct1::c(){
    int x;
    x = ___ivy_choose(65536,"fml:x",0);
    x = v.second;
    return x;
}
int struct1::b(){
    int x;
    x = ___ivy_choose(65536,"fml:x",0);
    x = v.first;
    return x;
}
struct1::t struct1::e(){
    t x;
    x.first = ___ivy_choose(65536,"fml:x",0);
    x.second = ___ivy_choose(65536,"fml:x",0);
    x = v;
    return x;
}
void struct1::d(t x){
    v = x;
}
void struct1::__init(){
    {
        ivy_assert(true, "");
    }
}
void struct1::__tick(int __timeout){
}
struct1::struct1(){
    __CARD__q = 65536;
    __CARD__r = 65536;
    v.first = 0;
    v.second = 0;
{
}
}


int ask_ret(int bound) {
    int res;
    while(true) {
        std::cout << "? ";
        std::cin >> res;
        if (res >= 0 && res < bound) 
            return res;
        std::cout << "value out of range" << std::endl;
    }
}



    class struct1_repl : public struct1 {

    public:

    virtual void ivy_assert(bool truth,const char *msg){
        if (!truth) {
            std::cerr << msg << ": assertion failed\n";
            exit(1);
        }
    }
    virtual void ivy_assume(bool truth,const char *msg){
        if (!truth) {
            std::cerr << msg << ": assumption failed\n";
            exit(1);
        }
    }
    struct1_repl() : struct1(){}

    };

// Override methods to implement low-level network service

bool is_white(int c) {
    return (c == ' ' || c == '\t' || c == '\n');
}

bool is_ident(int c) {
    return c == '_' || c == '.' || (c >= 'A' &&  c <= 'Z')
        || (c >= 'a' &&  c <= 'z')
        || (c >= '0' &&  c <= '9');
}

void skip_white(const std::string& str, int &pos){
    while (pos < str.size() && is_white(str[pos]))
        pos++;
}

struct syntax_error {
};

struct out_of_bounds {
    int idx;
    out_of_bounds(int _idx) : idx(_idx) {}
};

std::string get_ident(const std::string& str, int &pos) {
    std::string res = "";
    while (pos < str.size() && is_ident(str[pos])) {
        res.push_back(str[pos]);
        pos++;
    }
    if (res.size() == 0)
        throw syntax_error();
    return res;
}

struct ivy_value {
    std::string atom;
    std::vector<ivy_value> fields;
    bool is_member() const {
        return atom.size() && fields.size();
    }
};

ivy_value parse_value(const std::string& cmd, int &pos) {
    ivy_value res;
    skip_white(cmd,pos);
    if (pos < cmd.size() && cmd[pos] == '[') {
        while (true) {
            pos++;
            skip_white(cmd,pos);
            res.fields.push_back(parse_value(cmd,pos));
            skip_white(cmd,pos);
            if (pos < cmd.size() && cmd[pos] == ']')
                break;
            if (!(pos < cmd.size() && cmd[pos] == ','))
                throw syntax_error();
        }
        pos++;
    }
    else if (pos < cmd.size() && cmd[pos] == '{') {
        while (true) {
            ivy_value field;
            pos++;
            skip_white(cmd,pos);
            field.atom = get_ident(cmd,pos);
            skip_white(cmd,pos);
            if (!(pos < cmd.size() && cmd[pos] == ':'))
                 throw syntax_error();
            pos++;
            skip_white(cmd,pos);
            field.fields.push_back(parse_value(cmd,pos));
            res.fields.push_back(field);
            skip_white(cmd,pos);
            if (pos < cmd.size() && cmd[pos] == '}')
                break;
            if (!(pos < cmd.size() && cmd[pos] == ','))
                throw syntax_error();
        }
        pos++;
    }
    else 
        res.atom = get_ident(cmd,pos);
    return res;
}

void parse_command(const std::string &cmd, std::string &action, std::vector<ivy_value> &args) {
    int pos = 0;
    skip_white(cmd,pos);
    action = get_ident(cmd,pos);
    skip_white(cmd,pos);
    if (pos < cmd.size() && cmd[pos] == '(') {
        pos++;
        skip_white(cmd,pos);
        args.push_back(parse_value(cmd,pos));
        while(true) {
            skip_white(cmd,pos);
            if (!(pos < cmd.size() && cmd[pos] == ','))
                break;
            pos++;
            args.push_back(parse_value(cmd,pos));
        }
        if (!(pos < cmd.size() && cmd[pos] == ')'))
            throw syntax_error();
        pos++;
    }
    skip_white(cmd,pos);
    if (pos != cmd.size())
        throw syntax_error();
}

struct bad_arity {
    std::string action;
    int num;
    bad_arity(std::string &_action, unsigned _num) : action(_action), num(_num) {}
};

void check_arity(std::vector<ivy_value> &args, unsigned num, std::string &action) {
    if (args.size() != num)
        throw bad_arity(action,num);
}

int int_arg(std::vector<ivy_value> &args, unsigned idx, int bound) {
    int res = atoi(args[idx].atom.c_str());
    if (bound && (res < 0 || res >= bound) || args[idx].fields.size())
        throw out_of_bounds(idx);
    return res;
}

bool bool_arg(std::vector<ivy_value> &args, unsigned idx, int bound) {
    if (!(args[idx].atom == "true" || args[idx].atom == "false") || args[idx].fields.size())
        throw out_of_bounds(idx);
    return args[idx].atom == "true";
}

struct1::t t_arg(std::vector<ivy_value> &args, unsigned idx, int bound){
    struct1::t res;
    ivy_value &arg = args[idx];
    if (arg.atom.size() || arg.fields.size() != 2) throw out_of_bounds(idx);
    std::vector<ivy_value> tmp_args(1);
    if (arg.fields[0].is_member()){
        tmp_args[0] = arg.fields[0].fields[0];
        if (arg.fields[0].atom != "first") throw out_of_bounds(idx);
    }
    else{
        tmp_args[0] = arg.fields[0];
    }
    res.first = int_arg(tmp_args,0,65536);
;
    if (arg.fields[1].is_member()){
        tmp_args[0] = arg.fields[1].fields[0];
        if (arg.fields[1].atom != "second") throw out_of_bounds(idx);
    }
    else{
        tmp_args[0] = arg.fields[1];
    }
    res.second = int_arg(tmp_args,0,65536);
;
    return res;
}
std::ostream &operator <<(std::ostream &s, const struct1::t &t){
    s<<"{";
    s<< "first:" <<  t.first;
    s<<",";
    s<< "second:" <<  t.second;
    s<<"}";
    return s;
}


class stdin_reader: public reader {
    std::string buf;

    virtual int fdes(){
        return 0;
    }
    virtual void read() {
        char tmp[257];
        int chars = ::read(0,tmp,256);
        tmp[chars] = 0;
        buf += std::string(tmp);
        size_t pos;
        while ((pos = buf.find('\n')) != std::string::npos) {
            std::string line = buf.substr(0,pos+1);
            buf.erase(0,pos+1);
            process(line);
        }
    }
    virtual void process(const std::string &line) {
        std::cout << line;
    }
};

class cmd_reader: public stdin_reader {

public:
    struct1_repl &ivy;    

    cmd_reader(struct1_repl &_ivy) : ivy(_ivy) {
        std::cout << "> "; std::cout.flush();
    }

    virtual void process(const std::string &cmd) {
        std::string action;
        std::vector<ivy_value> args;
        try {
            parse_command(cmd,action,args);

            if (action == "a") {
                check_arity(args,2,action);
                ivy.a(int_arg(args,0,65536),int_arg(args,1,65536));
            }
            else

            if (action == "b") {
                check_arity(args,0,action);
                std::cout << ivy.b() << std::endl;
            }
            else

            if (action == "c") {
                check_arity(args,0,action);
                std::cout << ivy.c() << std::endl;
            }
            else

            if (action == "d") {
                check_arity(args,1,action);
                ivy.d(t_arg(args,0,0));
            }
            else

            if (action == "e") {
                check_arity(args,0,action);
                std::cout << ivy.e() << std::endl;
            }
            else

            {
                std::cout << "undefined action: " << action << std::endl;
            }
        }
        catch (syntax_error&) {
            std::cout << "syntax error" << std::endl;
        }
        catch (out_of_bounds &err) {
            std::cout << "argument " << err.idx + 1 << " out of bounds" << std::endl;
        }
        catch (bad_arity &err) {
            std::cout << "action " << err.action << " takes " << err.num  << " input parameters" << std::endl;
        }
        std::cout << "> "; std::cout.flush();
    }
};


std::vector<reader *> readers;

void install_reader(reader *r){
    readers.push_back(r);
}

std::vector<timer *> timers;

void install_timer(timer *r){
    timers.push_back(r);
}
int main(int argc, char **argv){
    if (argc != 1){
        std::cerr << "usage: struct1 \n";
        exit(1);
    }
    std::vector<std::string> args;
    for(int i = 1; i < argc;i++){args.push_back(argv[i]);}
    struct1_repl ivy;

    install_reader(new cmd_reader(ivy));

    while(true) {

        fd_set rdfds;
        FD_ZERO(&rdfds);
        int maxfds = 0;

        for (unsigned i = 0; i < readers.size(); i++) {
            reader *r = readers[i];
            int fds = r->fdes();
            FD_SET(fds,&rdfds);
            if (fds > maxfds)
                maxfds = fds;
        }

        struct timeval timeout;
        timeout.tv_sec = 1;
        timeout.tv_usec = 0;

        int foo = select(maxfds+1,&rdfds,0,0,&timeout);

        if (foo < 0)
            {perror("select failed"); exit(1);}
        
        if (foo == 0){
            // std::cout << "TIMEOUT\n";            
           for (unsigned i = 0; i < timers.size(); i++)
               timers[i]->timeout();
        }
        else {
            for (unsigned i = 0; i < readers.size(); i++) {
                reader *r = readers[i];
                if (FD_ISSET(r->fdes(),&rdfds))
                    r->read();
            }
        }            
    }
}
