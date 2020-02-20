#! /usr/bin/env python
#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

import ivy_init
import ivy_logic as il
import ivy_module as im
import ivy_utils as iu
import ivy_actions as ia
import logic as lg
import logic_util as lu
import ivy_solver as slv
import ivy_transrel as tr
import ivy_logic_utils as ilu
import ivy_compiler as ic
import ivy_isolate as iso
import ivy_ast
import itertools
import ivy_cpp
import ivy_cpp_types
import ivy_fragment as ifc
import sys
import os


from collections import defaultdict
from operator import mul
import re

hash_h = """
/*++
  Copyright (c) Microsoft Corporation

  This hash template is borrowed from Microsoft Z3
  (https://github.com/Z3Prover/z3).

  Simple implementation of bucket-list hash tables conforming roughly
  to SGI hash_map and hash_set interfaces, though not all members are
  implemented.

  These hash tables have the property that insert preserves iterators
  and references to elements.

  This package lives in namespace hash_space. Specializations of
  class "hash" should be made in this namespace.

  --*/

#pragma once

#ifndef HASH_H
#define HASH_H

#ifdef _WINDOWS
#pragma warning(disable:4267)
#endif

#include <string>
#include <vector>
#include <iterator>
#include <fstream>

namespace hash_space {

    unsigned string_hash(const char * str, unsigned length, unsigned init_value);

    template <typename T> class hash {
    public:
        size_t operator()(const T &s) const {
            return s.__hash();
        }
    };

    template <>
        class hash<int> {
    public:
        size_t operator()(const int &s) const {
            return s;
        }
    };

    template <>
        class hash<long long> {
    public:
        size_t operator()(const long long &s) const {
            return s;
        }
    };

    template <>
        class hash<unsigned> {
    public:
        size_t operator()(const unsigned &s) const {
            return s;
        }
    };

    template <>
        class hash<unsigned long long> {
    public:
        size_t operator()(const unsigned long long &s) const {
            return s;
        }
    };

    template <>
        class hash<bool> {
    public:
        size_t operator()(const bool &s) const {
            return s;
        }
    };

    template <>
        class hash<std::string> {
    public:
        size_t operator()(const std::string &s) const {
            return string_hash(s.c_str(), (unsigned)s.size(), 0);
        }
    };

    template <>
        class hash<std::pair<int,int> > {
    public:
        size_t operator()(const std::pair<int,int> &p) const {
            return p.first + p.second;
        }
    };

    template <typename T>
        class hash<std::vector<T> > {
    public:
        size_t operator()(const std::vector<T> &p) const {
            hash<T> h;
            size_t res = 0;
            for (unsigned i = 0; i < p.size(); i++)
                res += h(p[i]);
            return res;
        }
    };

    template <class T>
        class hash<std::pair<T *, T *> > {
    public:
        size_t operator()(const std::pair<T *,T *> &p) const {
            return (size_t)p.first + (size_t)p.second;
        }
    };

    template <class T>
        class hash<T *> {
    public:
        size_t operator()(T * const &p) const {
            return (size_t)p;
        }
    };

    enum { num_primes = 29 };

    static const unsigned long primes[num_primes] =
        {
            7ul,
            53ul,
            97ul,
            193ul,
            389ul,
            769ul,
            1543ul,
            3079ul,
            6151ul,
            12289ul,
            24593ul,
            49157ul,
            98317ul,
            196613ul,
            393241ul,
            786433ul,
            1572869ul,
            3145739ul,
            6291469ul,
            12582917ul,
            25165843ul,
            50331653ul,
            100663319ul,
            201326611ul,
            402653189ul,
            805306457ul,
            1610612741ul,
            3221225473ul,
            4294967291ul
        };

    inline unsigned long next_prime(unsigned long n) {
        const unsigned long* to = primes + (int)num_primes;
        for(const unsigned long* p = primes; p < to; p++)
            if(*p >= n) return *p;
        return primes[num_primes-1];
    }

    template<class Value, class Key, class HashFun, class GetKey, class KeyEqFun>
        class hashtable
    {
    public:

        typedef Value &reference;
        typedef const Value &const_reference;
    
        struct Entry
        {
            Entry* next;
            Value val;
      
        Entry(const Value &_val) : val(_val) {next = 0;}
        };
    

        struct iterator
        {      
            Entry* ent;
            hashtable* tab;

            typedef std::forward_iterator_tag iterator_category;
            typedef Value value_type;
            typedef std::ptrdiff_t difference_type;
            typedef size_t size_type;
            typedef Value& reference;
            typedef Value* pointer;

        iterator(Entry* _ent, hashtable* _tab) : ent(_ent), tab(_tab) { }

            iterator() { }

            Value &operator*() const { return ent->val; }

            Value *operator->() const { return &(operator*()); }

            iterator &operator++() {
                Entry *old = ent;
                ent = ent->next;
                if (!ent) {
                    size_t bucket = tab->get_bucket(old->val);
                    while (!ent && ++bucket < tab->buckets.size())
                        ent = tab->buckets[bucket];
                }
                return *this;
            }

            iterator operator++(int) {
                iterator tmp = *this;
                operator++();
                return tmp;
            }


            bool operator==(const iterator& it) const { 
                return ent == it.ent;
            }

            bool operator!=(const iterator& it) const {
                return ent != it.ent;
            }
        };

        struct const_iterator
        {      
            const Entry* ent;
            const hashtable* tab;

            typedef std::forward_iterator_tag iterator_category;
            typedef Value value_type;
            typedef std::ptrdiff_t difference_type;
            typedef size_t size_type;
            typedef const Value& reference;
            typedef const Value* pointer;

        const_iterator(const Entry* _ent, const hashtable* _tab) : ent(_ent), tab(_tab) { }

            const_iterator() { }

            const Value &operator*() const { return ent->val; }

            const Value *operator->() const { return &(operator*()); }

            const_iterator &operator++() {
                const Entry *old = ent;
                ent = ent->next;
                if (!ent) {
                    size_t bucket = tab->get_bucket(old->val);
                    while (!ent && ++bucket < tab->buckets.size())
                        ent = tab->buckets[bucket];
                }
                return *this;
            }

            const_iterator operator++(int) {
                const_iterator tmp = *this;
                operator++();
                return tmp;
            }


            bool operator==(const const_iterator& it) const { 
                return ent == it.ent;
            }

            bool operator!=(const const_iterator& it) const {
                return ent != it.ent;
            }
        };

    private:

        typedef std::vector<Entry*> Table;

        Table buckets;
        size_t entries;
        HashFun hash_fun ;
        GetKey get_key;
        KeyEqFun key_eq_fun;
    
    public:

    hashtable(size_t init_size) : buckets(init_size,(Entry *)0) {
            entries = 0;
        }
    
        hashtable(const hashtable& other) {
            dup(other);
        }

        hashtable& operator= (const hashtable& other) {
            if (&other != this)
                dup(other);
            return *this;
        }

        ~hashtable() {
            clear();
        }

        size_t size() const { 
            return entries;
        }

        bool empty() const { 
            return size() == 0;
        }

        void swap(hashtable& other) {
            buckets.swap(other.buckets);
            std::swap(entries, other.entries);
        }
    
        iterator begin() {
            for (size_t i = 0; i < buckets.size(); ++i)
                if (buckets[i])
                    return iterator(buckets[i], this);
            return end();
        }
    
        iterator end() { 
            return iterator(0, this);
        }

        const_iterator begin() const {
            for (size_t i = 0; i < buckets.size(); ++i)
                if (buckets[i])
                    return const_iterator(buckets[i], this);
            return end();
        }
    
        const_iterator end() const { 
            return const_iterator(0, this);
        }
    
        size_t get_bucket(const Value& val, size_t n) const {
            return hash_fun(get_key(val)) % n;
        }
    
        size_t get_key_bucket(const Key& key) const {
            return hash_fun(key) % buckets.size();
        }

        size_t get_bucket(const Value& val) const {
            return get_bucket(val,buckets.size());
        }

        Entry *lookup(const Value& val, bool ins = false)
        {
            resize(entries + 1);

            size_t n = get_bucket(val);
            Entry* from = buckets[n];
      
            for (Entry* ent = from; ent; ent = ent->next)
                if (key_eq_fun(get_key(ent->val), get_key(val)))
                    return ent;
      
            if(!ins) return 0;

            Entry* tmp = new Entry(val);
            tmp->next = from;
            buckets[n] = tmp;
            ++entries;
            return tmp;
        }

        Entry *lookup_key(const Key& key) const
        {
            size_t n = get_key_bucket(key);
            Entry* from = buckets[n];
      
            for (Entry* ent = from; ent; ent = ent->next)
                if (key_eq_fun(get_key(ent->val), key))
                    return ent;
      
            return 0;
        }

        const_iterator find(const Key& key) const {
            return const_iterator(lookup_key(key),this);
        }

        iterator find(const Key& key) {
            return iterator(lookup_key(key),this);
        }

        std::pair<iterator,bool> insert(const Value& val){
            size_t old_entries = entries;
            Entry *ent = lookup(val,true);
            return std::pair<iterator,bool>(iterator(ent,this),entries > old_entries);
        }
    
        iterator insert(const iterator &it, const Value& val){
            Entry *ent = lookup(val,true);
            return iterator(ent,this);
        }

        size_t erase(const Key& key)
        {
            Entry** p = &(buckets[get_key_bucket(key)]);
            size_t count = 0;
            while(*p){
                Entry *q = *p;
                if (key_eq_fun(get_key(q->val), key)) {
                    ++count;
                    *p = q->next;
                    delete q;
                }
                else
                    p = &(q->next);
            }
            entries -= count;
            return count;
        }

        void resize(size_t new_size) {
            const size_t old_n = buckets.size();
            if (new_size <= old_n) return;
            const size_t n = next_prime(new_size);
            if (n <= old_n) return;
            Table tmp(n, (Entry*)(0));
            for (size_t i = 0; i < old_n; ++i) {
                Entry* ent = buckets[i];
                while (ent) {
                    size_t new_bucket = get_bucket(ent->val, n);
                    buckets[i] = ent->next;
                    ent->next = tmp[new_bucket];
                    tmp[new_bucket] = ent;
                    ent = buckets[i];
                }
            }
            buckets.swap(tmp);
        }
    
        void clear()
        {
            for (size_t i = 0; i < buckets.size(); ++i) {
                for (Entry* ent = buckets[i]; ent != 0;) {
                    Entry* next = ent->next;
                    delete ent;
                    ent = next;
                }
                buckets[i] = 0;
            }
            entries = 0;
        }

        void dup(const hashtable& other)
        {
            clear();
            buckets.resize(other.buckets.size());
            for (size_t i = 0; i < other.buckets.size(); ++i) {
                Entry** to = &buckets[i];
                for (Entry* from = other.buckets[i]; from; from = from->next)
                    to = &((*to = new Entry(from->val))->next);
            }
            entries = other.entries;
        }
    };

    template <typename T> 
        class equal {
    public:
        bool operator()(const T& x, const T &y) const {
            return x == y;
        }
    };

    template <typename T>
        class identity {
    public:
        const T &operator()(const T &x) const {
            return x;
        }
    };

    template <typename T, typename U>
        class proj1 {
    public:
        const T &operator()(const std::pair<T,U> &x) const {
            return x.first;
        }
    };

    template <typename Element, class HashFun = hash<Element>, 
        class EqFun = equal<Element> >
        class hash_set
        : public hashtable<Element,Element,HashFun,identity<Element>,EqFun> {

    public:

    typedef Element value_type;

    hash_set()
    : hashtable<Element,Element,HashFun,identity<Element>,EqFun>(7) {}
    };

    template <typename Key, typename Value, class HashFun = hash<Key>, 
        class EqFun = equal<Key> >
        class hash_map
        : public hashtable<std::pair<Key,Value>,Key,HashFun,proj1<Key,Value>,EqFun> {

    public:

    hash_map()
    : hashtable<std::pair<Key,Value>,Key,HashFun,proj1<Key,Value>,EqFun>(7) {}

    Value &operator[](const Key& key) {
	std::pair<Key,Value> kvp(key,Value());
	return 
	hashtable<std::pair<Key,Value>,Key,HashFun,proj1<Key,Value>,EqFun>::
        lookup(kvp,true)->val.second;
    }
    };

    template <typename D,typename R>
        class hash<hash_map<D,R> > {
    public:
        size_t operator()(const hash_map<D,R> &p) const {
            hash<D > h1;
            hash<R > h2;
            size_t res = 0;
            
            for (typename hash_map<D,R>::const_iterator it=p.begin(), en=p.end(); it!=en; ++it)
                res += (h1(it->first)+h2(it->second));
            return res;
        }
    };

    template <typename D,typename R>
    inline bool operator ==(const hash_map<D,R> &s, const hash_map<D,R> &t){
        for (typename hash_map<D,R>::const_iterator it=s.begin(), en=s.end(); it!=en; ++it) {
            typename hash_map<D,R>::const_iterator it2 = t.find(it->first);
            if (it2 == t.end() || !(it->second == it2->second)) return false;
        }
        for (typename hash_map<D,R>::const_iterator it=t.begin(), en=t.end(); it!=en; ++it) {
            typename hash_map<D,R>::const_iterator it2 = s.find(it->first);
            if (it2 == t.end() || !(it->second == it2->second)) return false;
        }
        return true;
    }
}
#endif
"""

hash_cpp = """
/*++
Copyright (c) Microsoft Corporation

This string hash function is borrowed from Microsoft Z3
(https://github.com/Z3Prover/z3). 

--*/


#define mix(a,b,c)              \\
{                               \\
  a -= b; a -= c; a ^= (c>>13); \\
  b -= c; b -= a; b ^= (a<<8);  \\
  c -= a; c -= b; c ^= (b>>13); \\
  a -= b; a -= c; a ^= (c>>12); \\
  b -= c; b -= a; b ^= (a<<16); \\
  c -= a; c -= b; c ^= (b>>5);  \\
  a -= b; a -= c; a ^= (c>>3);  \\
  b -= c; b -= a; b ^= (a<<10); \\
  c -= a; c -= b; c ^= (b>>15); \\
}

#ifndef __fallthrough
#define __fallthrough
#endif

namespace hash_space {

// I'm using Bob Jenkin's hash function.
// http://burtleburtle.net/bob/hash/doobs.html
unsigned string_hash(const char * str, unsigned length, unsigned init_value) {
    register unsigned a, b, c, len;

    /* Set up the internal state */
    len = length;
    a = b = 0x9e3779b9;  /* the golden ratio; an arbitrary value */
    c = init_value;      /* the previous hash value */

    /*---------------------------------------- handle most of the key */
    while (len >= 12) {
        a += reinterpret_cast<const unsigned *>(str)[0];
        b += reinterpret_cast<const unsigned *>(str)[1];
        c += reinterpret_cast<const unsigned *>(str)[2];
        mix(a,b,c);
        str += 12; len -= 12;
    }

    /*------------------------------------- handle the last 11 bytes */
    c += length;
    switch(len) {        /* all the case statements fall through */
    case 11: 
        c+=((unsigned)str[10]<<24);
        __fallthrough;
    case 10: 
        c+=((unsigned)str[9]<<16);
        __fallthrough;
    case 9 : 
        c+=((unsigned)str[8]<<8);
        __fallthrough;
        /* the first byte of c is reserved for the length */
    case 8 : 
        b+=((unsigned)str[7]<<24);
        __fallthrough;
    case 7 : 
        b+=((unsigned)str[6]<<16);
        __fallthrough;
    case 6 : 
        b+=((unsigned)str[5]<<8);
        __fallthrough;
    case 5 : 
        b+=str[4];
        __fallthrough;
    case 4 : 
        a+=((unsigned)str[3]<<24);
        __fallthrough;
    case 3 : 
        a+=((unsigned)str[2]<<16);
        __fallthrough;
    case 2 : 
        a+=((unsigned)str[1]<<8);
        __fallthrough;
    case 1 : 
        a+=str[0];
        __fallthrough;
        /* case 0: nothing left to add */
    }
    mix(a,b,c);
    /*-------------------------------------------- report the result */
    return c;
}

}

"""

def all_state_symbols():
    syms = il.all_symbols()
    return [s for s in syms if s not in il.sig.constructors and slv.solver_name(il.normalize_symbol(s)) != None]

def sort_card(sort):
    if hasattr(sort,'card'):
        return sort.card
    if sort.is_relational():
        return 2
    if sort in sort_to_cpptype:
        return sort_to_cpptype[sort].card()
    card = slv.sort_card(sort)
#    if card and card > (2 ** 32):
#        card = None
    return card
    if hasattr(sort,'name'):
        name = sort.name
        if name in il.sig.interp:
            sort = il.sig.interp[name]
            if isinstance(sort,il.EnumeratedSort):
                return sort.card
            card = slv.sort_card(sort)
            if card != None:
                return card
    raise iu.IvyError(None,'sort {} has no finite interpretation'.format(sort))
    
indent_level = 0

def indent(header):
    header.append(indent_level * '    ')

def get_indent(line):
    lindent = 0
    for char in line:
        if char == ' ':
            lindent += 1
        elif char == '\t':
            lindent = (lindent + 8) / 8 * 8
        else:
            break
    return lindent

def indent_code(header,code):
    code = code.rstrip() # remove trailing whitespace
    nonempty_lines = [line for line in code.split('\n') if line.strip() != ""]
    indent = min(get_indent(line) for line in nonempty_lines) if nonempty_lines else 0
    for line in code.split('\n'):
        header.append((indent_level * 4 + get_indent(line) - indent) * ' ' + line.strip() + '\n')

def sym_decl(sym,c_type = None,skip_params=0,classname=None,isref=False,ival=None):
    name, sort = sym.name,sym.sort
    dims = []
    the_c_type,dims = ctype_function(sort,skip_params=skip_params,classname=classname)
    res = (c_type or the_c_type) + ' '
    if isref:
        res += '(&'
    res += memname(sym) if skip_params else varname(sym.name)
    if isref:
        res += ')'
    for d in dims:
        res += '[' + str(d) + ']'
    if ival is not None:
        res += ' = '+ival;
    return res
    
def declare_symbol(header,sym,c_type = None,skip_params=0,classname=None,isref=False,ival=None):
    if slv.solver_name(sym) == None:
        return # skip interpreted symbols
    header.append('    '+sym_decl(sym,c_type,skip_params,classname=classname,isref=isref,ival=ival)+';\n')

special_names = {
    '<' : '__lt',
    '<=' : '__le',
    '>' : '__gt',
    '>=' : '__ge',
}

puncs = re.compile('[\.\[\]]')

def varname(name):
    global special_names
    if not isinstance(name,str):
        name = name.name
    if name in special_names:
        return special_names[name]
    if name.startswith('"'):
        return name
    
    name = name.replace('loc:','loc__').replace('ext:','ext__').replace('___branch:','__branch__').replace('__prm:','prm__').replace('prm:','prm__').replace('__fml:','').replace('fml:','').replace('ret:','')
    name = re.sub(puncs,'__',name).replace('@@','.')
    return name.replace(':','__COLON__')
#    return name.split(':')[-1]

other_varname = varname

def funname(name):
    if not isinstance(name,str):
        name = name.name
    if name[0].isdigit():
        return '__num' + name
    if name[0] == '-':
        return '__negnum'+name
    if name[0] == '"':
        raise IvyError(None,"cannot compile a function whose name is a quoted string")
    return varname(name)
        

def mk_nondet(code,v,rng,name,unique_id):
    global nondet_cnt
    indent(code)
    ct = 'int' if isinstance(v,str) else ctype(v.sort)
    code.append(varname(v) + ' = ('+ct+')___ivy_choose(' + str(0) + ',"' + name + '",' + str(unique_id) + ');\n')

def is_native_sym(sym):
    assert hasattr(sym.sort,'rng'),sym
    return il.is_uninterpreted_sort(sym.sort.rng) and sym.sort.rng.name in im.module.native_types    


def mk_nondet_sym(code,sym,name,unique_id):
    global nondet_cnt
    if is_native_sym(sym) or ctype(sym.sort.rng) == '__strlit' or sym.sort.rng in sort_to_cpptype:
        return  # native classes have their own initializers
    if is_large_type(sym.sort):
        code_line(code,varname(sym) + ' = ' + make_thunk(code,variables(sym.sort.dom),HavocSymbol(sym.sort.rng,name,unique_id)))
        return
    fun = lambda v: (('('+ctype(v.sort)+')___ivy_choose(' + '0' + ',"' + name + '",' + str(unique_id) + ')')
                     if not (is_native_sym(v) or ctype(v.sort) == '__strlit' or v.sort in sort_to_cpptype) else None)
    dom = sym.sort.dom
    if dom:
        vs = variables(dom)
        open_loop(code,vs)
        term = sym(*(vs))
        ctext = varname(sym) + ''.join('['+varname(a)+']' for a in vs)
        assign_symbol_value(code,[ctext],fun,term,same=True)
        close_loop(code,vs)
    else:
        assign_symbol_value(code,[varname(sym)],fun,sym,same=True)

def field_eq(s,t,field):
    vs = [il.Variable('X{}'.format(idx),sort) for idx,sort in enumerate(field.sort.dom[1:])]
    if not vs:
        return il.Equals(field(s),field(t))
    return il.ForAll(vs,il.Equals(field(*([s]+vs)),field(*([t]+vs))))

def memname(sym):
    if not(isinstance(sym,str)):
        sym = sym.name
    return field_names.get(sym,sym.split('.')[-1])



def basename(name):
    return name.split('::')[-1]

def ctuple(dom,classname=None):
    if len(dom) == 1:
        return ctypefull(dom[0],classname=classname)
    return (classname+'::' if classname else '') + '__tup__' + '__'.join(basename(ctypefull(s).replace(" ","_")) for s in dom)

declared_ctuples = set()

def declare_ctuple(header,dom):
    if len(dom) == 1:
        return
    t = ctuple(dom)
    if t in declared_ctuples:
        return
    declared_ctuples.add(t)
    header.append('struct ' + t + ' {\n')
    for idx,sort in enumerate(dom):
        sym = il.Symbol('arg{}'.format(idx),sort)
        declare_symbol(header,sym)
    header.append(t+'(){}')
    header.append(t+'('+','.join('const '+ctypefull(d)+' &arg'+str(idx) for idx,d in enumerate(dom))
                  + ') : '+','.join('arg'+str(idx)+'(arg'+str(idx)+')' for idx,d in enumerate(dom))
                  + '{}\n')
    header.append("        size_t __hash() const { return "+struct_hash_fun(['arg{}'.format(n) for n in range(len(dom))],dom) + ";}\n")
    header.append('};\n')

def ctuple_hash(dom):
    if len(dom) == 1:
        return 'hash<'+ctypefull(dom[0])+'>'
    else:
        return 'hash__' + ctuple(dom)

def declare_ctuple_hash(header,dom,classname):
    t = ctuple(dom)
    the_type = classname+'::'+t
    header.append("""
class the_hash_type {
    public:
        size_t operator()(const the_type &__s) const {
            return the_val;
        }
    };
""".replace('the_hash_type',ctuple_hash(dom)).replace('the_type',the_type).replace('the_val','+'.join('hash_space::hash<{}>()(__s.arg{})'.format(hashtype(s),i,classname=classname) for i,s in enumerate(dom))))

                  
def declare_hash_thunk(header):
    header.append("""
template <typename D, typename R>
struct thunk {
    virtual R operator()(const D &) = 0;
    int ___ivy_choose(int rng,const char *name,int id) {
        return 0;
    }
};
template <typename D, typename R, class HashFun = hash_space::hash<D> >
struct hash_thunk {
    thunk<D,R> *fun;
    hash_space::hash_map<D,R,HashFun> memo;
    hash_thunk() : fun(0) {}
    hash_thunk(thunk<D,R> *fun) : fun(fun) {}
    ~hash_thunk() {
//        if (fun)
//            delete fun;
    }
    R &operator[](const D& arg){
        std::pair<typename hash_space::hash_map<D,R>::iterator,bool> foo = memo.insert(std::pair<D,R>(arg,R()));
        R &res = foo.first->second;
        if (foo.second && fun)
            res = (*fun)(arg);
        return res;
    }
};
""")        

def all_members():
    for sym in il.all_symbols():
        if sym_is_member(sym) and not slv.solver_name(sym) == None:
            yield sym

def all_ctuples():
    done = set()
    for sym in all_members():
        if hasattr(sym.sort,'dom') and len(sym.sort.dom) > 1 and is_large_type(sym.sort):
            res = tuple(sym.sort.dom)
            name = ctuple(res)
            if name in done:
                continue
            done.add(name)
            yield res
    
def all_hash_thunk_domains(classname):
    done = set()
    for sym in all_members():
        if hasattr(sym.sort,'dom') and len(sym.sort.dom) == 1 and is_large_type(sym.sort):
            res = sym.sort.dom[0]
            name = ctype(res,classname=classname)
            if name in done:
                continue
            done.add(name)
            yield name

def declare_all_ctuples(header):
    for dom in all_ctuples():
        declare_ctuple(header,dom)

def declare_all_ctuples_hash(header,classname):
    done = set()
    for dom in all_ctuples():
        name = ctuple(dom)
        if name in done:
            continue
        done.add(name)
        declare_ctuple_hash(header,dom,classname)

def hashtype(sort,classname=None):
    if isinstance(sort,il.EnumeratedSort):
        return 'int'
    return ctype(sort,classname)
    
def has_string_interp(sort):
    return il.sort_interp(sort) == 'strlit'    

def is_numeric_range(sort):
    s = sort.extension[0]
    return s[0].isdigit() or (s[0] == '-' and len(s) > 1 and s[1].isdigit)


def ctype_remaining_cases(sort,classname):
    if isinstance(sort,il.EnumeratedSort):
        if is_numeric_range(sort):
            return 'int'
        return ((classname+'::') if classname != None else '') + varname(sort.name)
    if sort.is_relational():
        return 'bool'
    if has_string_interp(sort):
        return '__strlit'
    if sort in sort_to_cpptype:
        sn = sort_to_cpptype[sort].short_name()
        return sn
        return ((classname+'::') if classname != None else '') + sn
    card = slv.sort_card(sort)
    if card is None:
        if hasattr(sort,'name'):
            name = sort.name
            if name in il.sig.interp:
                if il.sig.interp[name] == 'nat':
                    return 'unsigned long long'
        return 'int'   # for uninterpreted sorts, can be anything
    if card <= 2**32:
        return 'unsigned'
    if card <= 2**64:
       return 'unsigned long long'
    raise iu.IvyError(None,'sort {} is too large to represent with a machine integer'.format(sort))


global_classname = None

# Parameter passing types

class ValueType(object):  # by value
    def make(self,t):
        return t
class ConstRefType(object):  # by const reference
    def make(self,t):
        return 'const ' + t + '&'
class RefType(object): # by non-const reference
    def make(self,t):
        return t + '&'

class ReturnRefType(object): # return by reference in argument position "pos"
    def __init__(self,pos):
        self.pos = pos
    def make(self,t):
        return 'void'
    def __repr__(self):
        return "ReturnRefType({})".format(self.pos)

def ctype(sort,classname=None,ptype=None):
    ptype = ptype or ValueType()
    classname = classname or global_classname
    if il.is_uninterpreted_sort(sort):
        if sort.name in im.module.native_types or sort.name in im.module.sort_destructors:
            return ptype.make(((classname+'::') if classname != None else '') + varname(sort.name))
    return ptype.make(ctype_remaining_cases(sort,classname))
    
def ctypefull(sort,classname=None):
    classname = classname or global_classname
    if il.is_uninterpreted_sort(sort):
        if sort.name in im.module.native_types:
            if classname==None:
#                return native_type_full(im.module.native_types[sort.name])
                return varname(sort.name)
            return classname+'::'+varname(sort.name)
        if sort.name in im.module.sort_destructors:
            return ((classname+'::') if classname != None else '') + varname(sort.name)
    return ctype_remaining_cases(sort,classname)

def native_type_full(self):
    return self.args[0].inst(native_reference,self.args[1:])    

large_thresh = 1024

def is_large_type(sort):
    if hasattr(sort,'dom') and any(not is_any_integer_type(s) for s in sort.dom):
        return True
    cards = map(sort_card,sort.dom if hasattr(sort,'dom') else [])
    return not(all(cards) and reduce(mul,cards,1) <= large_thresh)

def is_large_lhs(term):
    freevars = lu.free_variables(term)
    if any(not is_any_integer_type(v.sort) for v in freevars):
        return True
    cards = [sort_card(v.sort) for v in lu.free_variables(term)]
    return not(all(cards) and reduce(mul,cards,1) <= large_thresh)
    

def ctype_function(sort,classname=None,skip_params=0):
    cards = map(sort_card,sort.dom[skip_params:] if hasattr(sort,'dom') else [])
    cty = ctypefull(sort.rng,classname)
    if all(cards) and reduce(mul,cards,1) <= large_thresh:
        if not(hasattr(sort,'dom') and any(not is_any_integer_type(s) for s in sort.dom[skip_params:])):
            return (cty,cards)
    cty = 'hash_thunk<'+ctuple(sort.dom[skip_params:],classname=classname)+','+cty+'>'
    return (cty,[])
    
native_expr_full = native_type_full

thunk_counter = 0


def expr_to_z3(expr):
    fmla = '(assert ' + slv.formula_to_z3(expr).sexpr().replace('|!1','!1|').replace('\\|','').replace('\n',' "\n"') + ')'
    return 'z3::expr(g.ctx,Z3_parse_smtlib2_string(ctx, "{}", sort_names.size(), &sort_names[0], &sorts[0], decl_names.size(), &decl_names[0], &decls[0]))'.format(fmla)



def gather_referenced_symbols(expr,res,ignore=[]):
    for sym in ilu.used_symbols_ast(expr):
        if (not sym.is_numeral() and not slv.solver_name(sym) == None
            and sym.name not in im.module.destructor_sorts and sym not in res and sym not in ignore):
            res.add(sym)
            if sym in is_derived:
                ldf = is_derived[sym]
                if ldf is not True:
                    gather_referenced_symbols(ldf.formula.args[1],res,ldf.formula.args[0].args)
                
skip_z3 = False

def is_numeric_or_enumerated_constant(s):
    return s.is_numeral() or il.is_constant(s) and il.is_enumerated(s)


def make_thunk(impl,vs,expr):
    global the_classname
    dom = [v.sort for v in vs]
    D = ctuple(dom,classname=the_classname)
    R = ctypefull(expr.sort,classname=the_classname)
    global thunk_counter
    name = '__thunk__{}'.format(thunk_counter)
    thunk_counter += 1
    thunk_class = 'z3_thunk' if target.get() in ["gen","test"] else 'thunk'
    open_scope(impl,line='struct {} : {}<{},{}>'.format(name,thunk_class,D,R))
    syms = set()
    gather_referenced_symbols(expr,syms)
    env = [sym for sym in syms if sym not in is_derived]
    funs = [sym for sym in syms if sym in is_derived]
    for sym in env:
        declare_symbol(impl,sym,classname=the_classname)
    for fun in funs:
        ldf = is_derived[fun]
        if ldf is True:
            emit_constructor(None,impl,fun,the_classname,inline=True)
        else:
            with ivy_ast.ASTContext(ldf):
                emit_derived(None,impl,ldf.formula,the_classname,inline=True)
    envnames = [varname(sym) for sym in env]
    open_scope(impl,line='{}({}) {} {}'.format(name,','.join(sym_decl(sym,classname=the_classname) for sym in env)
                                             ,':' if envnames else ''
                                             ,','.join('{}({})'.format(n,n) for n in envnames))),
    close_scope(impl)
    open_scope(impl,line='{} operator()(const {} &arg)'.format(R,D))
    subst = {vs[0].name:il.Symbol('arg',vs[0].sort)} if len(vs)==1 else dict((v.name,il.Symbol('arg@@arg{}'.format(idx),v.sort)) for idx,v in enumerate(vs))
    expr = ilu.substitute_ast(expr,subst)
    code_line(impl,'return ' + code_eval(impl,expr))
    close_scope(impl)
    if target.get() in ["gen","test"]:
        open_scope(impl,line = 'z3::expr to_z3(gen &g, const z3::expr &v)')
        if False and isinstance(expr,HavocSymbol) or skip_z3:
            code_line(impl,'return g.ctx.bool_val(true)')
        else:
            if lu.free_variables(expr):
                raise iu.IvyError(None,"cannot compile {}".format(expr))
            if all(is_numeric_or_enumerated_constant(s) for s in ilu.used_symbols_ast(expr)):
                if expr.sort in sort_to_cpptype or hasattr(expr.sort,'name') and (expr.sort.name in im.module.sort_destructors or
                                                                                  expr.sort.name in im.module.native_types):
                    code_line(impl,'z3::expr res = __to_solver(g,v,{})'.format(code_eval(impl,expr)))
                else:
                    cty = '__strlit' if has_string_interp(expr.sort) else 'int'
                    code_line(impl,'z3::expr res = v == g.int_to_z3(g.sort("{}"),({})({}))'.format(expr.sort.name,cty,code_eval(impl,expr)))
            else:
                raise iu.IvyError(None,"cannot compile {}".format(expr))
            code_line(impl,'return res')
        close_scope(impl)
    close_scope(impl,semi=True)
    return 'hash_thunk<{},{}>(new {}({}))'.format(D,R,name,','.join(envnames))

def struct_hash_fun(field_names,field_sorts):
    if len(field_names) == 0:
        return '0'
    return '+'.join('hash_space::hash<{}>()({})'.format(hashtype(s),varname(f)) for s,f in zip(field_sorts,field_names))

def emit_struct_hash(header,the_type,field_names,field_sorts):
    header.append("""
    template<> class hash<the_type> {
        public:
            size_t operator()(const the_type &__s) const {
                return the_val;
             }
    };
""".replace('the_type',the_type).replace('the_val',struct_hash_fun(['__s.'+n for n in field_names],field_sorts)))

def emit_cpp_sorts(header):
    for name in im.module.sort_order:
        if name in im.module.native_types:
            nt = native_type_full(im.module.native_types[name]).strip()
            if nt in ['int','bool']:
                header.append("    typedef " + nt + ' ' + varname(name) + ";\n");
            else:
                header.append("    class " + varname(name) + ' : public ' + nt +  "{\n")
                header.append("        public: size_t __hash() const { return hash_space::hash<"+nt+" >()(*this);};\n")
                header.append("    };\n");
        elif name in im.module.sort_destructors:
            header.append("    struct " + varname(name) + " {\n");
            destrs = im.module.sort_destructors[name]
            for destr in destrs:
                declare_symbol(header,destr,skip_params=1)
            header.append("        size_t __hash() const { return "+struct_hash_fun(map(memname,destrs),[d.sort.rng for d in destrs]) + ";}\n")
            header.append("    };\n");
        elif isinstance(il.sig.sorts[name],il.EnumeratedSort):
            sort = il.sig.sorts[name]
            if not is_numeric_range(sort):
                header.append('    enum ' + varname(name) + '{' + ','.join(varname(x) for x in sort.extension) + '};\n');
            elif name in il.sig.interp and isinstance(il.sig.interp[name],il.EnumeratedSort):
                sort = il.sig.interp[name]
                header.append('    enum ' + varname(name) + '{' + ','.join(varname(x) for x in sort.extension) + '};\n');
        elif name in im.module.variants:
            sort = il.sig.sorts[name]
            cpptype = ivy_cpp_types.VariantType(varname(name),sort,[(s,ctypefull(s,classname=the_classname)) for s in im.module.variants[name]])
            cpptypes.append(cpptype)
            sort_to_cpptype[il.sig.sorts[name]] = cpptype
        elif name in il.sig.interp:
            itp = il.sig.interp[name]
            if not (isinstance(itp,il.EnumeratedSort) or itp.startswith('{') or itp.startswith('bv[') or itp in ['int','nat','strlit']):
                cpptype = ivy_cpp_types.get_cpptype_constructor(itp)(varname(name))
                cpptypes.append(cpptype)
                sort_to_cpptype[il.sig.sorts[name]] = cpptype
        else:
            il.sig.interp[name] = 'int'


def emit_sorts(header):
    for name,sort in il.sig.sorts.iteritems():
        if name == "bool":
            continue
        if name in il.sig.interp:
            sortname = il.sig.interp[name]
            if isinstance(sortname,il.EnumeratedSort):
                sort = sortname
        if not isinstance(sort,il.EnumeratedSort):
            if name in il.sig.interp:
                sortname = il.sig.interp[name]
#            print "name: {} sortname: {}".format(name,sortname)
                if sortname.startswith('bv[') and sortname.endswith(']'):
                    width = int(sortname[3:-1])
                    indent(header)
                    header.append('mk_bv("{}",{});\n'.format(name,width))
                    continue
                if sortname in ['int','nat']:
                    indent(header)
                    header.append('mk_int("{}");\n'.format(name))
                    continue
                if sortname == 'strlit':
                    indent(header)
                    header.append('mk_string("{}");\n'.format(name))
                    continue
            if sort in sort_to_cpptype and sort.name not in im.module.variants:
                indent(header)
                header.append('enum_sorts.insert(std::pair<std::string, z3::sort>("'+ name + '",'+ctype(sort)+'::z3_sort(ctx)));\n')
                continue
            header.append('mk_sort("{}");\n'.format(name))
            continue
#            raise iu.IvyError(None,'sort {} has no finite interpretation'.format(name))
        card = sort.card
        cname = varname(name)
        indent(header)
        header.append("const char *{}_values[{}]".format(cname,card) +
                      " = {" + ','.join('"{}"'.format(slv.solver_name(il.Symbol(x,sort))) for x in sort.extension) + "};\n");
        indent(header)
        header.append('mk_enum("{}",{},{}_values);\n'.format(name,card,cname))

def emit_decl(header,symbol):
    name = symbol.name
    sname = slv.solver_name(symbol)
    if sname == None:  # this means the symbol is interpreted in some theory
        return 
    cname = '__pto__' + varname(symbol.sort.dom[0].name) + '__' + varname(symbol.sort.dom[1].name)  if symbol.name == '*>' else varname(name)
    sort = symbol.sort
    rng_name = "Bool" if sort.is_relational() else sort.rng.name
    domain = sort_domain(sort)
    if len(domain) == 0:
        indent(header)
        header.append('mk_const("{}","{}");\n'.format(sname,rng_name))
    else:
        card = len(domain)
        indent(header)
        header.append("const char *{}_domain[{}]".format(cname,card) + " = {"
                      + ','.join('"{}"'.format(s.name) for s in domain) + "};\n");
        indent(header)
        header.append('mk_decl("{}",{},{}_domain,"{}");\n'.format(sname,card,cname,rng_name))
        
def emit_sig(header):
    emit_sorts(header)
    for symbol in all_state_symbols():
        emit_decl(header,symbol)

def sort_domain(sort):
    if hasattr(sort,"domain"):
        return sort.domain
    return []

def int_to_z3(sort,val):
    if il.is_uninterpreted_sort(sort):
        raise iu.IvyError(None,"cannot produce test generator because sort {} is uninterpreted".format(sort))
    return 'int_to_z3(sort("'+sort.name+'"),'+val+')'

def emit_eval(header,symbol,obj=None,classname=None,lhs=None): 
    global indent_level
    name = symbol.name
    sname = slv.solver_name(symbol)
    cname = varname(name) if lhs is None else code_eval(header,lhs)
    sort = symbol.sort
    domain = sort_domain(sort)
    for idx,dsort in enumerate(domain):
        dcard = sort_card(dsort)
        indent(header)
        header.append("for (int X{} = 0; X{} < {}; X{}++)\n".format(idx,idx,dcard,idx))
        indent_level += 1
    indent(header)
    if sort.rng.name in im.module.sort_destructors or sort.rng.name in im.module.native_types or sort.rng in sort_to_cpptype:
        code_line(header,'__from_solver<'+classname+'::'+varname(sort.rng.name)+'>(*this,apply("'+sname+'"'+''.join(','+int_to_z3(s,'X{}'.format(idx)) for idx,s in enumerate(domain))+'),'+cname+''.join('[X{}]'.format(idx) for idx in range(len(domain)))+')')
    else:
        header.append((obj + '.' if obj else '')
                      + cname + ''.join("[X{}]".format(idx) for idx in range(len(domain)))
                      + ' = ({})eval_apply("{}"'.format(ctype(sort.rng,classname=classname),sname)
                      + ''.join(",X{}".format(idx) for idx in range(len(domain)))
                      + ");\n")
    for idx,dsort in enumerate(domain):
        indent_level -= 1    

def var_to_z3_val(v):
    return int_to_z3(v.sort,varname(v))

def emit_set_field(header,symbol,lhs,rhs,nvars=0):
    global indent_level
    name = symbol.name
    sname = slv.solver_name(symbol)
    cname = varname(name)
    sort = symbol.sort
    domain = sort.dom[1:]
    vs = variables(domain,start=nvars)
    open_loop(header,vs)
    lhs1 = 'apply("'+sname+'"'+''.join(','+s for s in ([lhs]+map(var_to_z3_val,vs))) + ')'
    rhs1 = rhs + ''.join('[{}]'.format(varname(v)) for v in vs) + '.' + memname(symbol)
    if sort.rng.name in im.module.sort_destructors:
        destrs = im.module.sort_destructors[sort.rng.name]
        for destr in destrs:
            emit_set_field(header,destr,lhs1,rhs1,nvars+len(vs))
    else:
#        code_line(header,'slvr.add('+lhs1+'=='+int_to_z3(sort.rng,rhs1)+')')
        code_line(header,'slvr.add(__to_solver(*this,'+lhs1+','+rhs1+'))')
    close_loop(header,vs)


def emit_set(header,symbol): 
    global indent_level
    name = symbol.name
    sname = slv.solver_name(symbol)
    cname = varname(name)
    sort = symbol.sort
    domain = sort_domain(sort)
    if sort.rng.name in im.module.sort_destructors and all(is_finite_iterable_sort(s) for s in domain):
        destrs = im.module.sort_destructors[sort.rng.name]
        for destr in destrs:
            vs = variables(domain)
            open_loop(header,vs)
            lhs = 'apply("'+sname+'"'+''.join(','+s for s in map(var_to_z3_val,vs)) + ')'
            rhs = 'obj.' + varname(symbol) + ''.join('[{}]'.format(varname(v)) for v in vs)
            emit_set_field(header,destr,lhs,rhs,len(vs))
            close_loop(header,vs)
        return
    if is_large_type(sort):
        vs = variables(sort.dom)
        cvars = ','.join('ctx.constant("{}",sort("{}"))'.format(varname(v),v.sort.name) for v in vs)
        code_line(header,'slvr.add(forall({},__to_solver(*this,apply("{}",{}),obj.{})))'.format(cvars,sname,cvars,cname))
        return
    for idx,dsort in enumerate(domain):
        dcard = sort_card(dsort)
        indent(header)
        header.append("for (int X{} = 0; X{} < {}; X{}++)\n".format(idx,idx,dcard,idx))
        indent_level += 1
    indent(header)
    header.append('slvr.add(__to_solver(*this,apply("{}"'.format(sname)
                  + ''.join(','+int_to_z3(domain[idx],'X{}'.format(idx)) for idx in range(len(domain)))
                  + '),obj.{}'.format(cname)+ ''.join("[X{}]".format(idx) for idx in range(len(domain)))
                  + '));\n')
    # header.append('set("{}"'.format(sname)
    #               + ''.join(",X{}".format(idx) for idx in range(len(domain)))
    #               + ",obj.{}".format(cname)+ ''.join("[X{}]".format(idx) for idx in range(len(domain)))
    #               + ");\n")
    for idx,dsort in enumerate(domain):
        indent_level -= 1    

def sym_is_member(sym):
    global is_derived
    res = sym not in is_derived and sym.name not in im.module.destructor_sorts
    return res

def emit_eval_sig(header,obj=None,used=None,classname=None):
    for symbol in all_state_symbols():
        if slv.solver_name(symbol) != None and symbol.name not in im.module.destructor_sorts: # skip interpreted symbols
            global is_derived
            if symbol not in is_derived:
                if used == None or symbol in used:
                    emit_eval(header,symbol,obj,classname=classname)

def emit_clear_progress(impl,obj=None):
    for df in im.module.progress:
        vs = list(lu.free_variables(df.args[0]))
        open_loop(impl,vs)
        code = []
        indent(code)
        if obj != None:
            code.append('obj.')
        df.args[0].emit(impl,code)
        code.append(' = 0;\n')
        impl.extend(code)
        close_loop(impl,vs)

def mk_rand(sort,classname=None):
    card = sort_card(sort)
    return '('+ctype(sort,classname=classname)+')' + ('(rand() % {})'.format(card) if card
                                                      else '((rand()%2) ? "a" : "b")' if has_string_interp(sort)
                                                      else sort_to_cpptype[sort].rand() if sort in sort_to_cpptype
                                                      else "0")

def emit_init_gen(header,impl,classname):
    global indent_level
    global global_classname
    global_classname = classname
    header.append("""
class init_gen : public gen {
public:
    init_gen();
""")
    header.append("    bool generate(" + classname + "&);\n")
    header.append("    void execute(" + classname + "&){}\n};\n")
    impl.append("init_gen::init_gen(){\n");
    indent_level += 1
    emit_sig(impl)
    indent(impl)
    impl.append('add("(assert (and\\\n')
    constraints = [im.module.init_cond.to_formula()]
    for a in im.module.axioms:
        constraints.append(a)
    for ldf in im.relevant_definitions(ilu.symbols_asts(constraints)):
        constraints.append(fix_definition(ldf.formula).to_constraint())
    for c in constraints:
        fmla = slv.formula_to_z3(c).sexpr().replace('|!1','!1|').replace('\\|','').replace('\n',' "\n"')
        indent(impl)
        impl.append("  {}\\\n".format(fmla))
    indent(impl)
    impl.append('))");\n')
    indent_level -= 1
    impl.append("}\n");
    used = ilu.used_symbols_asts(constraints)
    impl.append("bool init_gen::generate(" + classname + "& obj) {\n")
    indent_level += 1
    for cpptype in cpptypes:
        code_line(impl,cpptype.short_name()+'::prepare()')
    code_line(impl,'alits.clear()')
    for sym in all_state_symbols():
        if slv.solver_name(il.normalize_symbol(sym)) != None: # skip interpreted symbols
            global is_derived
            if sym_is_member(sym):
                if sym in used:
                    if sym in im.module.params:
                        emit_set(impl,sym)  # parameters are already set in constructor
                    else:
                        emit_randomize(impl,sym,classname=classname)
                else:
                    if sym not in im.module.params:
                        if is_large_type(sym.sort):
                            code_line(impl,'obj.'+varname(sym) + ' = ' + make_thunk(impl,variables(sym.sort.dom),HavocSymbol(sym.sort.rng,sym.name,0)))
                        elif not is_native_sym(sym):
                            fun = lambda v: (mk_rand(v.sort,classname=classname) if not is_native_sym(v) else None)
                            assign_array_from_model(impl,sym,'obj.',fun)
    indent_level -= 1
    impl.append("""
    // std::cout << slvr << std::endl;
    bool __res = solve();
    if (__res) {
""")
    indent_level += 2
    emit_eval_sig(impl,'obj',used = used,classname=classname)
    emit_clear_progress(impl,'obj')
    indent_level -= 2
    impl.append("""
    }
""")
    for cpptype in cpptypes:
        code_line(impl,cpptype.short_name()+'::cleanup()')
    impl.append("""
    obj.___ivy_gen = this;
    obj.__init();
    return __res;
}
""")
    global_classname = None
    
def emit_randomize(header,symbol,classname=None):

    global indent_level
    name = symbol.name
    sname = slv.solver_name(symbol)
    cname = varname(name)
    sort = symbol.sort
    domain = sort_domain(sort)
    for idx,dsort in enumerate(domain):
        dcard = sort_card(dsort)
        indent(header)
        header.append("for (int X{} = 0; X{} < {}; X{}++)\n".format(idx,idx,dcard,idx))
        indent_level += 1
    if sort.rng.name in im.module.sort_destructors or sort.rng.name in im.module.native_types or sort.rng in sort_to_cpptype:
        code_line(header,'__randomize<'+classname+'::'+varname(sort.rng.name)+'>(*this,apply("'+sname+'"'+''.join(','+int_to_z3(s,'X{}'.format(idx)) for idx,s in enumerate(domain))+'))')
    else:
        indent(header)
        if il.is_uninterpreted_sort(sort.rng):
            raise iu.IvyError(None,'cannot create test generator because type {} is uninterpreted'.format(sort.rng))
        header.append('randomize("{}"'.format(sname)
                      + ''.join(",X{}".format(idx) for idx in range(len(domain)))
                      + ");\n")
    for idx,dsort in enumerate(domain):
        indent_level -= 1    

#    indent(header)
#    header.append('randomize("{}");\n'.format(slv.solver_name(symbol)))


def is_local_sym(sym):
    sym = il.normalize_symbol(sym)
    return not il.sig.contains_symbol(sym) and slv.solver_name(il.normalize_symbol(sym)) != None and sym not in il.sig.constructors

def fix_definition(df):
    if all(il.is_variable(v) for v in df.args[0].args):
        return df
    subst = dict((s,il.Variable('X__{}'.format(idx),s.sort)) for idx,s in enumerate(df.args[0].args) if not il.is_variable(s))
    return ilu.substitute_constants_ast(df,subst)

# An action input x is 'defined' by the action's precondition if the precondition is
# of the form P & x = expr, where x does not occur in P. Here, we remove the defined inputs from
# the precondition, to improve the performance of the solver. We also return a list of
# the definitions, so the values of the defined inputs can be computed.

def extract_defined_parameters(pre_clauses,inputs):
    change = True
    inputset = set(inputs)
    defmap = {}
    for fmla in pre_clauses.fmlas:
        if il.is_eq(fmla) and fmla.args[0] in inputset:
            defmap[fmla.args[0]] = fmla
    inpdefs = []
    while change:
        change = False
        for input,fmla in list(defmap.iteritems()):
            if (all(input not in ilu.used_symbols_ast(f) or f == fmla for f in pre_clauses.fmlas)
                and all(input not in ilu.used_symbols_ast(d) for d in pre_clauses.defs)):
                pre_clauses = ilu.Clauses([f for f in pre_clauses.fmlas if f != fmla],pre_clauses.defs)
                del defmap[input]
                inpdefs.append(fmla)
                change = True
                pre_clauses = ilu.trim_clauses(pre_clauses)
    inpdefs.reverse()
    return pre_clauses,inpdefs

def collect_used_definitions(pre,inpdefs,ssyms):
    defmap = dict((d.defines(),d) for d in pre.defs)
    used = set()
    res = []
    usyms = []
    def recur(d):
        for sym in ilu.used_symbols_ast(d.args[1]):
            if sym not in used:
                used.add(sym)
                if sym in defmap:
                    d = defmap[sym]
                    recur(d)
                    res.append(d)
                elif sym in ssyms:
                    usyms.append(sym)
    for inpdef in inpdefs:
        recur(inpdef)
    return res,usyms
    

def emit_defined_inputs(pre,inpdefs,code,classname,ssyms,fsyms):
    global delegate_enums_to
    delegate_enums_to = classname
    udefs,usyms = collect_used_definitions(pre,inpdefs,ssyms)
    global is_derived
    for sym in usyms:
        if sym not in is_derived:
            declare_symbol(code,sym,classname=classname,isref=True,ival='obj.'+code_eval(code,sym))
    global skip_z3
    skip_z3 = True
    for dfn in udefs:
        sym = dfn.defines()
        declare_symbol(code,sym,classname=classname)
        emit_assign(dfn,code)
    skip_z3 = False
    global delegate_methods_to
    for param_def in inpdefs:
        lhs = param_def.args[0]
        lhs = fsyms.get(lhs,lhs)
        rhs = ilu.substitute_constants_ast(param_def.args[1],fsyms)
        delegate_methods_to = 'obj.'
        code_line(code,code_eval(code,lhs) + ' = ' + code_eval(code,rhs))
        delegate_methods_to = ''
    delegate_enums_to = ''
    
def minimal_field_references(fmla,inputs):
    inpset = set(inputs)
    res = defaultdict(set)
    def field_ref(f):
        if il.is_app(f):
            if f.rep.name in im.module.destructor_sorts and len(f.args) == 1:
                return field_ref(f.args[0])
            if f.rep in inpset:
                return f.rep
        return None
            
    def recur(f):
        if il.is_app(f):
            if f.rep.name in im.module.destructor_sorts and len(f.args) == 1:
                inp = field_ref(f.args[0])
                if inp is not None:
                    res[inp].add(f)
                    return
            if il.is_constant(f) and f.rep in inpset:
                res[f.rep].add(f.rep)
                return
        for x in f.args:
            recur(x)
        
    def get_minima(refs):
        def lt(x,y):
            return len(y.args) == 1 and (x == y.args[0] or lt(x,y.args[0]))
        return set(y for y in refs if all(not(lt(x,y)) for x in refs))
            
    recur(fmla)
    res = dict((inp,get_minima(refs)) for inp,refs in res.iteritems())
    return res
                
def minimal_field_siblings(inputs,mrefs):
    res = defaultdict(set)
    for inp in inputs:
        if inp in mrefs:
            for f in mrefs[inp]:
                if len(f.args) == 1:
                    sort = f.rep.sort.dom[0]
                    destrs = im.module.sort_destructors[sort.name]
                    for d in destrs:
                        res[inp].add(d(f.args[0]))
                else:
                    res[inp].add(inp)
        else:
            res[inp].add(inp)
    return res

def extract_input_fields(pre_clauses,inputs):
    mrefs = minimal_field_references(pre_clauses.to_formula(),inputs)
    mrefs = minimal_field_siblings(inputs,mrefs)
    def field_symbol_name(f):
        if len(f.args) == 1:
            return field_symbol_name(f.args[0]) + '__' + f.rep.name
        return f.rep.name
    fsyms = dict((il.Symbol(field_symbol_name(y),y.sort),y) for l in mrefs.values() for y in l)
    rfsyms  = dict((y,x) for x,y in fsyms.iteritems())
    def recur(f):
        if il.is_app(f):
            if f.rep in mrefs or f.rep.name in im.module.destructor_sorts and len(f.args) == 1:
                if f in rfsyms:
                    return rfsyms[f]
        return f.clone(map(recur,f.args))
    pre_clauses = ilu.Clauses(map(recur,pre_clauses.fmlas),map(recur,pre_clauses.defs))
    inputs = list(fsyms.keys())
    return pre_clauses,inputs,fsyms

def expand_field_references(pre_clauses):
    defmap = dict((x.args[0].rep,x.args[1]) for x in pre_clauses.defs
                  if len(x.args[0].args) == 0 and il.is_app(x.args[1])
                      and  (len(x.args[1].args) == 0 or
                            len(x.args[1].args) == 1 and
                                x.args[1].rep.name in im.module.destructor_sorts))
    def recur(f):
        if il.is_app(f) and f.rep in defmap:
            return recur(defmap[f.rep])
        return f.clone(map(recur,f.args))
    def recur_def(d):
        return d.clone([d.args[0],recur(d.args[1])])
    dfs = map(recur,pre_clauses.defs)
    dfs = [df for df in dfs if df.args[0] != df.args[1]]
    return ilu.Clauses(map(recur,pre_clauses.fmlas),dfs)

def emit_action_gen(header,impl,name,action,classname):
    global indent_level
    global global_classname
    global_classname = classname
    caname = varname(name)
    if name in im.module.before_export:
        action = im.module.before_export[name]
    def card(sort):
#        res = sort_card(sort)
#        if res is not None:
#            return res
        if hasattr(sort,'name') and iu.compose_names(sort.name,'cardinality') in im.module.attributes:
            return int(im.module.attributes[iu.compose_names(sort.name,'cardinality')].rep)
        return sort_card(sort)
        
#    action = action.unroll_loops(card)
    if name in im.module.ext_preconds:
        orig_action = action
        action = ia.Sequence(ia.AssumeAction(im.module.ext_preconds[name]),action)
        action.lineno = orig_action.lineno
        action.formal_params = orig_action.formal_params
        action.formal_returns = orig_action.formal_returns

    with ia.UnrollContext(card):
        upd = action.update(im.module,None)
    pre = tr.reverse_image(ilu.true_clauses(),ilu.true_clauses(),upd)
    orig_pre = pre
    pre_clauses = ilu.trim_clauses(pre)
    pre_clauses = expand_field_references(pre_clauses)
    inputs = [x for x in ilu.used_symbols_clauses(pre_clauses) if is_local_sym(x) and not x.is_numeral()]
    inputset = set(inputs)
    for p in action.formal_params:
        p = p.prefix('__')
        if p not in inputset:
            inputs.append(p)
    pre_clauses, inputs, fsyms = extract_input_fields(pre_clauses,inputs)
    old_pre_clauses = pre_clauses
    pre_clauses, param_defs = extract_defined_parameters(pre_clauses,inputs)
    rdefs = im.relevant_definitions(ilu.symbols_clauses(pre_clauses))
    pre_clauses = ilu.and_clauses(pre_clauses,ilu.Clauses([fix_definition(ldf.formula).to_constraint() for ldf in rdefs]))
    pre_clauses = ilu.and_clauses(pre_clauses,ilu.Clauses(im.module.variant_axioms()))
    pre = pre_clauses.to_formula()
    used = set(ilu.used_symbols_ast(pre))
    used_names = set(varname(s) for s in used)
    defed_params = set(f.args[0] for f in param_defs)
    for x in used:
        if x.is_numeral() and il.is_uninterpreted_sort(x.sort):
            raise iu.IvyError(None,'Cannot compile numeral {} of uninterpreted sort {}'.format(x,x.sort))
    syms = inputs
    header.append("class " + caname + "_gen : public gen {\n  public:\n")
    decld = set()
    def get_root(f):
        return get_root(f.args[0]) if len(f.args) == 1 else f
    for sym in syms:
        if sym in fsyms:
            sym = get_root(fsyms[sym])
        if sym not in decld:
            if not sym.name.startswith('__ts') and sym not in old_pre_clauses.defidx and sym.name != '*>':
                declare_symbol(header,sym,classname=classname)
            decld.add(sym)
    header.append("    {}_gen();\n".format(caname))
    header.append("    bool generate(" + classname + "&);\n");
    header.append("    void execute(" + classname + "&);\n};\n");
    impl.append(caname + "_gen::" + caname + "_gen(){\n");
    indent_level += 1
    emit_sig(impl)
    to_decl = set(syms)
    to_decl.update(s for s in used if s.name == '*>')
    for sym in to_decl:
        emit_decl(impl,sym)
    indent(impl)
    import platform
    if platform.system() == 'Windows':
        winfmla = slv.formula_to_z3(pre).sexpr().replace('|!1','!1|').replace('\\|','')
        impl.append('std::string winfmla = "(assert ";\n');
        for winline in winfmla.split('\n'):
            impl.append('winfmla.append("{} ");\n'.format(winline))
        impl.append('winfmla.append(")");\n')
        impl.append('add(winfmla);\n')
    else:
        impl.append('add("(assert {})");\n'.format(slv.formula_to_z3(pre).sexpr().replace('|!1','!1|').replace('\\|','').replace('\n',' "\n"')))
#    impl.append('__ivy_modelfile << slvr << std::endl;\n')
    indent_level -= 1
    impl.append("}\n");
    impl.append("bool " + caname + "_gen::generate(" + classname + "& obj) {\n    push();\n")
    indent_level += 1
    for cpptype in cpptypes:
        code_line(impl,cpptype.short_name()+'::prepare()')
    pre_used = ilu.used_symbols_ast(pre)
    for sym in all_state_symbols():
        if sym in pre_used and sym not in old_pre_clauses.defidx: # skip symbols not used in constraint
            if slv.solver_name(il.normalize_symbol(sym)) != None: # skip interpreted symbols
                if sym_is_member(sym):
                    emit_set(impl,sym)
    code_line(impl,'alits.clear()')
    for sym in syms:
        if not sym.name.startswith('__ts') and sym not in old_pre_clauses.defidx  and sym.name != '*>':
            emit_randomize(impl,sym,classname=classname)
#    impl.append('    std::cout << "generating {}" << std::endl;\n'.format(caname))
    impl.append("""
    // std::cout << slvr << std::endl;
    bool __res = solve();
    if (__res) {
""")
    indent_level += 1
    for sym in syms:
        if not sym.name.startswith('__ts') and sym not in old_pre_clauses.defidx and sym.name != '*>':
            if sym not in defed_params:
                emit_eval(impl,sym,classname=classname,lhs=fsyms.get(sym,sym))
    ssyms = set()
    for sym in all_state_symbols():
#        if sym_is_member(sym):
        if sym.name not in im.module.destructor_sorts:
            ssyms.add(sym)
    emit_defined_inputs(orig_pre,param_defs,impl,classname,ssyms,fsyms)
    indent_level -= 2
    impl.append("""
    }""")
    for cpptype in cpptypes:
        code_line(impl,cpptype.short_name()+'::cleanup()')
    impl.append("""
    pop();
    obj.___ivy_gen = this;
    return __res;
}
""")
    open_scope(impl,line="void " + caname + "_gen::execute(" + classname + "& obj)")
    if action.formal_params:
        code_line(impl,'__ivy_out << "> {}("'.format(name.split(':')[-1]) + ' << "," '.join(' << {}'.format(varname(p)) for p in action.formal_params) + ' << ")" << std::endl')
    else:
        code_line(impl,'__ivy_out << "> {}"'.format(name.split(':')[-1]) + ' << std::endl')
    if opt_trace.get():
        code_line(impl,'__ivy_out << "{" << std::endl')
    call = 'obj.{}('.format(caname) + ','.join(varname(p) for p in action.formal_params) + ')'
    if len(action.formal_returns) == 0:
        code_line(impl,call)
        if opt_trace.get():
            code_line(impl,'__ivy_out << "}" << std::endl')
    else:
        if opt_trace.get():
            code_line(impl,ctypefull(action.formal_returns[0].sort,classname=classname)+' __res = '+call)
            code_line(impl,'__ivy_out << "}" << std::endl')
            code_line(impl,'__ivy_out << "= " << __res <<  std::endl')
        else:
            code_line(impl,'__ivy_out << "= " << ' + call + ' <<  std::endl')
    close_scope(impl)
    global_classname = None


def emit_derived(header,impl,df,classname,inline=False):
    name = df.defines().name
    sort = df.defines().sort.rng
    retval = il.Symbol("ret:val",sort)
    vs = df.args[0].args
    ps = [ilu.var_to_skolem('fml:',v) for v in vs]
    mp = dict(zip(vs,ps))
    rhs = ilu.substitute_ast(df.args[1],mp)
    action = ia.AssignAction(retval,rhs)
    action.formal_params = ps
    action.formal_returns = [retval]
    emit_some_action(header,impl,name,action,classname,inline)

def emit_constructor(header,impl,cons,classname,inline=False):
    name = cons.name
    sort = cons.sort.rng
    retval = il.Symbol("ret:val",sort)
    vs = [il.Variable('X{}'.format(idx),s) for idx,s in enumerate(cons.sort.dom)]
    ps = [ilu.var_to_skolem('fml:',v) for v in vs]
    destrs = im.module.sort_destructors[sort.name]
    asgns = [ia.AssignAction(d(retval),p) for idx,(d,p) in enumerate(zip(destrs,ps))]
    action = ia.Sequence(*asgns);
    action.formal_params = ps
    action.formal_returns = [retval]
    emit_some_action(header,impl,name,action,classname,inline)


def native_split(string):
    split = string.split('\n',1)
    if len(split) == 2:
        tag = split[0].strip()
        return ("member" if not tag else tag),split[1]
    return "member",split[0]

def native_type(native):
    tag,code = native_split(native.args[1].code)
    return tag

def native_declaration(atom):
    if atom.rep in im.module.sig.sorts:
        res = ctype(im.module.sig.sorts[atom.rep],classname=native_classname)
#        print 'type(atom): {} atom.rep: {} res: {}'.format(type(atom),atom.rep,res)
        return res
    vname = varname(atom.rep)
    res = ((native_classname + '::') if (native_classname and not vname[0].isdigit() and not vname[0] == '"') else '') + vname
    for arg in atom.args:
        sort = arg.sort if isinstance(arg.sort,str) else arg.sort.name
        card = sort_card(im.module.sig.sorts[sort])
        if card is None:
            raise iu.IvyError(atom,'cannot allocate an array over sort {} because it is not finite'.format(im.module.sig.sorts[sort]))
        res += '[' + str(card) + ']'
    return res

thunk_counter = 0

def action_return_type(action):
    return ctype(action.formal_returns[0].sort) if action.formal_returns else 'void'

def thunk_name(actname):
    return 'thunk__' + varname(actname)

def create_thunk(impl,actname,action,classname):
    tc = thunk_name(actname)
    impl.append('struct ' + tc + '{\n')
    impl.append('    ' + classname + ' *__ivy' + ';\n')
    
    params = [p for p in action.formal_params if p.name.startswith('prm:')]
    inputs = [p for p in action.formal_params if not p.name.startswith('prm:')]
    for p in params:
        declare_symbol(impl,p,classname=classname)
    impl.append('    ')
    emit_param_decls(impl,tc,params,extra = [ classname + ' *__ivy'],classname=classname)
    impl.append(': __ivy(__ivy)' + ''.join(',' + varname(p) + '(' + varname(p) + ')' for p in params) + '{}\n')
    impl.append('    ' + action_return_type(action) + ' ')
    emit_param_decls(impl,'operator()',inputs,classname=classname);
    impl.append(' const {\n        __ivy->' + varname(actname)
                + '(' + ','.join(varname(p.name) for p in action.formal_params) + ');\n    }\n};\n')

def native_typeof(arg):
    if isinstance(arg,ivy_ast.Atom):
        if arg.rep in im.module.actions:
            return thunk_name(arg.rep)
        raise iu.IvyError(arg,'undefined action: ' + arg.rep)
    return int + len(arg.sort.dom) * '[]'

def native_z3name(arg):
    if il.is_variable(arg):
        return arg.sort.name
    rep = arg.rep
    if isinstance(rep,str):
        return rep
    return arg.rep.name

def native_to_str(native,reference=False,code=None):
    if code is None:
        tag,code = native_split(native.args[1].code)
    fields = code.split('`')
    f = native_reference if reference else native_declaration
    def nfun(idx):
        return native_typeof if fields[idx-1].endswith('%') else native_z3name if fields[idx-1].endswith('"') else f
    def dm(s):
        return s[:-1] if s.endswith('%') else s
    fields = [(nfun(idx)(native.args[int(s)+2]) if idx % 2 == 1 else dm(s)) for idx,s in enumerate(fields)]
    return ''.join(fields)

def emit_native(header,impl,native,classname):
    with ivy_ast.ASTContext(native):
        header.append(native_to_str(native))


# This determines the parameter passing type of each input and output
# of an action (value, const reference, or no-const reference, return
# by reference). The rules are as follows: 
#
# If an output parameter is the same as an input parameter, that
# parameter is returned by reference, and the input parameter is
# passed by reference. Other input parameters are passed by const
# reference, except if the parameter is assigned on the action body,
# in which case it is passed by value. Other output parameters are
# returned by value.
#
# Output parameters beyond the first are always return by reference.
# If they do not match any input parameter, they are added to the
# end of the input parameters.
#
# Notwithstanding the above, all exported actions use call and return
# by value so as not to confused external callers.

def annotate_action(name,action):

    if name in im.module.public_actions:
        action.param_types = [ValueType() for p in action.formal_params]
        action.return_types = [ValueType() for p in action.formal_returns]
        return

    def action_assigns(p):
        return any(p in sub.modifies() for sub in action.iter_subactions())

    def is_struct(sort):
       return (il.is_uninterpreted_sort(sort) and
               (sort.name in im.module.native_types or sort.name in im.module.sort_destructors))

    action.param_types = [RefType() if any(p == q for q in action.formal_returns)
                          else ValueType() if action_assigns(p) or not is_struct(p.sort) else ConstRefType()
                          for p in action.formal_params]
    next_arg_pos = len(action.formal_params)
    action.return_types = []
    def matches_input(p,action):
        for idx,q in enumerate(action.formal_params):
            if p == q:
                return idx
        return None
    for pos,p in enumerate(action.formal_returns):
        idx = matches_input(p,action)
        if idx is not None:
            thing = ReturnRefType(idx)
        elif pos > 0:
            thing = ReturnRefType(next_arg_pos)
            next_arg_pos = next_arg_pos + 1
        else:
            thing = ValueType()
        action.return_types.append(thing)

def get_param_types(name,action):
    if not hasattr(action,"param_types"):
        annotate_action(name,action)
    return (action.param_types, action.return_types)

# Estimate if two expressions may alias. We say conservatively that expressions may alias
# if they have the same root variable.

def is_destructor(symbol):
    return symbol.name in im.module.destructor_sorts

def may_alias(x,y):
    def root_var(x):
        while il.is_app(x) and is_destructor(x.rep):
            x = x.args[0]
        return x
    return root_var(x) == root_var(y)

# emit parameter declarations of the approriate parameter types

def emit_param_decls(header,name,params,extra=[],classname=None,ptypes=None):
    header.append(funname(name) + '(')
    for p in params:
        if il.is_function_sort(p.sort):
            raise(iu.IvyError(None,'Cannot compile parameter {} with function sort'.format(p)))
    header.append(', '.join(extra + [ctype(p.sort,classname=classname,ptype = ptypes[idx] if ptypes else None) + ' ' + varname(p.name) for idx,p in enumerate(params)]))
    header.append(')')

def emit_param_decls_with_inouts(header,name,params,classname,ptypes,returns,return_ptypes):
    extra_params = []
    extra_ptypes = []
    for (r,rp) in zip(returns,return_ptypes):
        if isinstance(rp,ReturnRefType) and rp.pos >= len(params):
            extra_params.append(r)
            extra_ptypes.append(RefType())
    emit_param_decls(header,name,params+extra_params,classname=classname,ptypes=ptypes+extra_ptypes)

def emit_method_decl(header,name,action,body=False,classname=None,inline=False):
    if not hasattr(action,"formal_returns"):
        print "bad name: {}".format(name)
        print "bad action: {}".format(action)
    rs = action.formal_returns
    ptypes,rtypes = get_param_types(name,action)
    if not body:
        header.append('    ')
    if not body and target.get() != "gen" and not inline:
        header.append('virtual ')
    if len(rs) == 0:
        header.append('void ')
    else:
        header.append(ctype(rs[0].sort,classname=classname,ptype=rtypes[0]) + ' ')
    if len(rs) > 1:
        if any(not isinstance(p,ReturnRefType) for p in rtypes[1:]):
            raise iu.IvyError(action,'cannot handle multiple output in exported actions: {}'.format(name))
    if body and not inline:
        header.append(classname + '::')
    emit_param_decls_with_inouts(header,name,action.formal_params,classname if inline else None,ptypes,rs,rtypes)
    
def emit_action(header,impl,name,classname):
    action = im.module.actions[name]
    emit_some_action(header,impl,name,action,classname)

def trace_action(impl,name,action):
    indent(impl)
    if name.startswith('ext:'):
        name = name[4:]
    impl.append('__ivy_out ' + number_format + ' << "< ' + name + '"')
    if action.formal_params:
        impl.append(' << "("')
        first = True
        for arg in action.formal_params:
            if not first:
                impl.append(' << ","')
            first = False
            impl.append(' << {}'.format(varname(arg.rep.name)))
        impl.append(' << ")"')
    impl.append(' << std::endl;\n')

def emit_some_action(header,impl,name,action,classname,inline=False):
    global indent_level
    global import_callers
    if not inline:
        emit_method_decl(header,name,action)
        header.append(';\n')
    global thunks
    thunks = impl
    code = []
    emit_method_decl(code,name,action,body=True,classname=classname,inline=inline)
    code.append('{\n')
    indent_level += 1
    if name in import_callers:
        trace_action(code,name,action)
        if opt_trace.get():
            code_line(code,'__ivy_out ' + number_format + ' << "{" << std::endl')
    pt,rt = get_param_types(name,action)
    if len(action.formal_returns) >= 1 and not isinstance(rt[0],ReturnRefType):
        indent(code)
        p = action.formal_returns[0]
        if p not in action.formal_params:
            code.append(ctypefull(p.sort,classname=classname) + ' ' + varname(p.name) + ';\n')
            mk_nondet_sym(code,p,p.name,0)
    with ivy_ast.ASTContext(action):
        action.emit(code)
    if name in import_callers:
        if opt_trace.get():
            code_line(code,'__ivy_out ' + number_format + ' << "}" << std::endl')
    if len(action.formal_returns) >= 1 and not isinstance(rt[0],ReturnRefType):
        indent(code)
        code.append('return ' + varname(action.formal_returns[0].name) + ';\n')
    indent_level -= 1
    code.append('}\n')
    impl.extend(code)

def init_method():
    asserts = []
    # for ini in im.module.labeled_inits + im.module.labeled_axioms:
    #     act = ia.AssertAction(ini.formula)
    #     act.lineno = ini.lineno
    #     asserts.append(act)
    
    for name,ini in im.module.initializers:
        asserts.append(ini)

    res = ia.Sequence(*asserts)
    res.formal_params = []
    res.formal_returns = []
    return res

int_ctypes = ["bool","int","long long","unsigned","unsigned long long"]

def is_iterable_sort(sort):
    return ctype(sort) in int_ctypes

def is_finite_iterable_sort(sort):
    return is_iterable_sort(sort) and sort_card(sort) is not None

def is_any_integer_type(sort):
    if ctype(sort) not in int_ctypes:
        if il.is_uninterpreted_sort(sort) and sort.name in im.module.native_types:
            nt = native_type_full(im.module.native_types[sort.name]).strip()
            if nt in int_ctypes:
                return True
        if isinstance(sort,il.EnumeratedSort):
            return True
        return False
    return True

def check_iterable_sort(sort):
    if not is_any_integer_type(sort):
        raise iu.IvyError(None,"cannot iterate over non-integer sort {}".format(sort))
    

def open_loop(impl,vs,declare=True,bounds=None):
    global indent_level
    for num,idx in enumerate(vs):
        check_iterable_sort(idx.sort)
        indent(impl)
        bds = bounds[num] if bounds else ["0",str(sort_card(idx.sort))]
        vn = varname(idx.name)
        ct = ctype(idx.sort)
        ct = 'int' if ct == 'bool' else ct if ct in int_ctypes else 'int'
        if isinstance(idx.sort,il.EnumeratedSort):
            ct = ctype(idx.sort)
            impl.append('for ('+ ((ct + ' ') if declare else '') + vn + ' = (' + ct + ')' +  bds[0] + '; (int) ' + vn + ' < ' + bds[1] + '; ' + vn + ' = (' + ct + ')(((int)' + vn + ') + 1)) {\n')
        else:
            impl.append('for ('+ ((ct + ' ') if declare else '') + vn + ' = ' + bds[0] + '; ' + vn + ' < ' + bds[1] + '; ' + vn + '++) {\n')
        indent_level += 1

def close_loop(impl,vs):
    global indent_level
    for idx in vs:
        indent_level -= 1    
        indent(impl)
        impl.append('}\n')
        
def open_scope(impl,newline=False,line=None):
    global indent_level
    if line != None:
        indent(impl)
        impl.append(line)
    if newline:
        impl.append('\n')
        indent(impl)
    impl.append('{\n')
    indent_level += 1

def open_if(impl,cond):
    open_scope(impl,line='if('+(''.join(cond) if isinstance(cond,list) else cond)+')')
    
def close_scope(impl,semi=False):
    global indent_level
    indent_level -= 1
    indent(impl)
    impl.append('}'+(';' if semi else '')+'\n')

# This generates the "tick" method, called by the test environment to
# represent passage of time. For each progress property, if it is not
# satisfied the counter is incremented else it is set to zero. For each
# property the maximum of the counter values for all its relies is
# computed and the test environment's ivy_check_progress function is called.

# This is currently a bit bogus, since we could miss satisfaction of
# the progress property occurring between ticks.

def emit_tick(header,impl,classname):
    global indent_level
    indent_level += 1
    indent(header)
    header.append('void __tick(int timeout);\n')
    indent_level -= 1
    indent(impl)
    impl.append('void ' + classname + '::__tick(int __timeout){\n')
    indent_level += 1

    rely_map = defaultdict(list)
    for df in im.module.rely:
        key = df.args[0] if isinstance(df,il.Implies) else df
        rely_map[key.rep].append(df)

    for df in im.module.progress:
        vs = list(lu.free_variables(df.args[0]))
        open_loop(impl,vs)
        code = []
        indent(code)
        df.args[0].emit(impl,code)
        code.append(' = ')
        df.args[1].emit(impl,code)
        code.append(' ? 0 : ')
        df.args[0].emit(impl,code)
        code.append(' + 1;\n')
        impl.extend(code)
        close_loop(impl,vs)


    for df in im.module.progress:
        if any(not isinstance(r,il.Implies) for r in rely_map[df.defines()]):
            continue
        vs = list(lu.free_variables(df.args[0]))
        open_loop(impl,vs)
        maxt = new_temp(impl)
        indent(impl)
        impl.append(maxt + ' = 0;\n') 
        for r in rely_map[df.defines()]:
            if not isinstance(r,il.Implies):
                continue
            rvs = list(lu.free_variables(r.args[0]))
            assert len(rvs) == len(vs)
            subs = dict(zip(rvs,vs))

            ## TRICKY: If there are any free variables on rhs of
            ## rely not occuring on left, we must prevent their capture
            ## by substitution

            xvs = set(lu.free_variables(r.args[1]))
            xvs = xvs - set(rvs)
            for xv in xvs:
                subs[xv.name] = xv.rename(xv.name + '__')
            xvs = [subs[xv.name] for xv in xvs]
    
            e = ilu.substitute_ast(r.args[1],subs)
            open_loop(impl,xvs)
            indent(impl)
            impl.append('{} = std::max({},'.format(maxt,maxt))
            e.emit(impl,impl)
            impl.append(');\n')
            close_loop(impl,xvs)
        indent(impl)
        impl.append('if (' + maxt + ' > __timeout)\n    ')
        indent(impl)
        df.args[0].emit(impl,impl)
        impl.append(' = 0;\n')
        indent(impl)
        impl.append('ivy_check_progress(')
        df.args[0].emit(impl,impl)
        impl.append(',{});\n'.format(maxt))
        close_loop(impl,vs)

    indent_level -= 1
    indent(impl)
    impl.append('}\n')

def csortcard(s):
    card = sort_card(s)
    return str(card) if card else "0"

def check_member_names(classname):
    names = map(varname,(list(il.sig.symbols) + list(il.sig.sorts) + list(im.module.actions)))
    if classname in names:
        raise iu.IvyError(None,'Cannot create C++ class {} with member {}.\nUse command line option classname=... to change the class name.'
                          .format(classname,classname))

def emit_ctuple_to_solver(header,dom,classname):
    ct_name = classname + '::' + ctuple(dom)
    ch_name = classname + '::' + ctuple_hash(dom)
    emit_hash_thunk_to_solver(header,dom,classname,ct_name,ch_name)
    
def emit_hash_thunk_to_solver(header,dom,classname,ct_name,ch_name):
    open_scope(header,line='template<typename R> class to_solver_class<hash_thunk<D,R> >'.replace('D',ct_name).replace('H',ch_name))
    code_line(header,'public:')
    open_scope(header,line='z3::expr operator()( gen &g, const  z3::expr &v, hash_thunk<D,R> &val)'.replace('D',ct_name).replace('H',ch_name))
    code_line(header,'z3::expr res = g.ctx.bool_val(true)')
    code_line(header,'z3::expr disj = g.ctx.bool_val(false)')
    code_line(header,'z3::expr bg = dynamic_cast<z3_thunk<D,R> *>(val.fun)->to_z3(g,v)'.replace('D',ct_name))
    open_scope(header,line='for(typename hash_map<D,R>::iterator it=val.memo.begin(), en = val.memo.end(); it != en; it++)'.replace('D',ct_name).replace('H',ch_name))
#    code_line(header,'if ((*val.fun)(it->first) == it->second) continue;')
    code_line(header,'z3::expr asgn = __to_solver(g,v,it->second)')
#    code_line(header,'if (eq(bg,asgn)) continue')
    if dom is not None:
        code_line(header,'z3::expr cond = '+' && '.join('__to_solver(g,v.arg('+str(n)+'),it->first.arg'+str(n)+')' for n in range(len(dom))))
    else:
        code_line(header,'z3::expr cond = __to_solver(g,v.arg(0),it->first)')
    code_line(header,'res = res && implies(cond,asgn)')
    code_line(header,'disj = disj || cond')
    close_scope(header)
    code_line(header,'res = res && (disj || bg)')
    code_line(header,'return res')
    close_scope(header)
    close_scope(header,semi=True)

def emit_all_ctuples_to_solver(header,classname):
#    emit_hash_thunk_to_solver(header,None,classname,'__strlit','hash<__strlit>')
#    for cpptype in cpptypes:
#        emit_hash_thunk_to_solver(header,None,classname,cpptype.short_name(),'hash<'+cpptype.short_name()+'>')
    for cname in all_hash_thunk_domains(classname):
        emit_hash_thunk_to_solver(header,None,classname,cname,'hash<'+cname+'>')
    for dom in all_ctuples():
        emit_ctuple_to_solver(header,dom,classname)

def emit_ctuple_equality(header,dom,classname):
    t = ctuple(dom)
    open_scope(header,line = 'bool operator==(const {}::{} &x, const {}::{} &y)'.format(classname,t,classname,t))
    code_line(header,'return '+' && '.join('x.arg{} == y.arg{}'.format(n,n) for n in range(len(dom))))
    close_scope(header)

def is_really_uninterpreted_sort(sort):
    return il.is_uninterpreted_sort(sort) and not (
        sort.name in im.module.sort_destructors or sort.name in im.module.native_types)

# find the actions that wrap imports and flaf them so the we output a
# trace. This is so that the trace of the action will appear before 
# any assert failure in the precondition. To get the name of the caller
# from the import, we remove the prefic 'imp__'.

def find_import_callers():
    global import_callers
    import_callers = set()
    if target.get() != "test":
        return
    for imp in im.module.imports:
        name = imp.imported()
        if not imp.scope() and name in im.module.actions:
            import_callers.add('ext:' + name[5:])
            import_callers.add(name[5:])
            
def module_to_cpp_class(classname,basename):
    global the_classname
    the_classname = classname
    global encoded_sorts
    encoded_sorts = set()
    check_member_names(classname)
    global is_derived
    is_derived = dict()
    for ldf in im.module.definitions + im.module.native_definitions:
        is_derived[ldf.formula.defines()] = ldf
    for sortname, conss in im.module.sort_constructors.iteritems():
        for cons in conss:
            is_derived[cons] = True
    global cpptypes
    cpptypes = []
    global sort_to_cpptype
    sort_to_cpptype = {}
    global field_names
    field_names = dict()
    for destrs in im.module.sort_destructors.values():
        if destrs: # paranoia
            dest_base,_ = iu.parent_child_name(destrs[0].name)
            if not all(iu.parent_child_name(d.name)[0] == dest_base for d in destrs):
                for d in destrs:
                    field_names[d.name] = varname(d.name)

    if target.get() in ["gen","test"]:
        for t in list(il.sig.interp):
            attr = iu.compose_names(t,'override')
            if attr in im.module.attributes:
                print 'override: interpreting {} as {}'.format(t,im.module.attributes[attr].rep)
                il.sig.interp[t] = im.module.attributes[attr].rep

    global number_format
    number_format = ''
    if 'radix' in im.module.attributes and im.module.attributes['radix'].rep == '16':
        number_format = ' << std::hex << std::showbase '
        
    # remove the actions not reachable from exported
        
# TODO: may want to call internal actions from testbench

#    ra = iu.reachable(im.module.public_actions,lambda name: im.module.actions[name].iter_calls())
#    im.module.actions = dict((name,act) for name,act in im.module.actions.iteritems() if name in ra)

    header = ivy_cpp.context.globals.code
    import platform
    if platform.system() == 'Windows':
        header.append('#define WIN32_LEAN_AND_MEAN\n')
        header.append("#include <windows.h>\n")
    header.append("#define _HAS_ITERATOR_DEBUGGING 0\n")
    if target.get() == "gen":
        header.append('extern void ivy_assert(bool,const char *);\n')
        header.append('extern void ivy_assume(bool,const char *);\n')
        header.append('extern void ivy_check_progress(int,int);\n')
        header.append('extern int choose(int,int);\n')
    if target.get() in ["gen","test"]:
        header.append('struct ivy_gen {virtual int choose(int rng,const char *name) = 0;};\n')
#    header.append('#include <vector>\n')

    if target.get() in ["gen","test"]:
         header.append('#include "z3++.h"\n')


    header.append(hash_h)

    header.append("typedef std::string __strlit;\n")
    header.append("extern std::ofstream __ivy_out;\n")
    header.append("void __ivy_exit(int);\n")
    
    declare_hash_thunk(header)

    once_memo = set()
    for native in im.module.natives:
        tag = native_type(native)
        if tag == "header":
            code = native_to_str(native)
            if code not in once_memo:
                once_memo.add(code)
                header.append(code)

    header.append("""

    class reader;
    class timer;

""")

    ivy_cpp.context.members = ivy_cpp.CppText()
    header = ivy_cpp.context.members.code
    header.append('class ' + classname + ' {\n  public:\n')
    header.append("    typedef {} ivy_class;\n".format(classname))
    header.append("""
    std::vector<std::string> __argv;
#ifdef _WIN32
    void *mutex;  // forward reference to HANDLE
#else
    pthread_mutex_t mutex;
#endif
    void __lock();
    void __unlock();
""")
    header.append("""
#ifdef _WIN32
    std::vector<HANDLE> thread_ids;\n
#else
    std::vector<pthread_t> thread_ids;\n
#endif
""")
    header.append('    void install_reader(reader *);\n')
    header.append('    void install_thread(reader *);\n')
    header.append('    void install_timer(timer *);\n')
    header.append('    virtual ~{}();\n'.format(classname))

    header.append('    std::vector<int> ___ivy_stack;\n')
    if target.get() in ["gen","test"]:
        header.append('    ivy_gen *___ivy_gen;\n')
    header.append('    int ___ivy_choose(int rng,const char *name,int id);\n')
    if target.get() != "gen":
        header.append('    virtual void ivy_assert(bool,const char *){}\n')
        header.append('    virtual void ivy_assume(bool,const char *){}\n')
        header.append('    virtual void ivy_check_progress(int,int){}\n')
    
    with ivy_cpp.CppClassName(classname):
        emit_cpp_sorts(header)

        
    impl = ivy_cpp.context.impls.code
    if opt_stdafx.get():
        impl.append('#include "stdafx.h"\n')
    impl.append('#include "' + basename + '.h"\n\n')
    impl.append("#include <sstream>\n")
    impl.append("#include <algorithm>\n")
    impl.append("""
#include <iostream>
#include <stdlib.h>
#include <sys/types.h>          /* See NOTES */
#include <sys/stat.h>
#include <fcntl.h>
#ifdef _WIN32
#include <winsock2.h>
#include <WS2tcpip.h>
#include <io.h>
#define isatty _isatty
#else
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/ip.h> 
#include <sys/select.h>
#include <unistd.h>
#define _open open
#define _dup2 dup2
#endif
#include <string.h>
#include <stdio.h>
#include <string>
#if __cplusplus < 201103L
#else
#include <cstdint>
#endif
""")
    impl.append("typedef {} ivy_class;\n".format(classname))
    impl.append("std::ofstream __ivy_out;\n")
    impl.append("std::ofstream __ivy_modelfile;\n")
    impl.append("void __ivy_exit(int code){exit(code);}\n")

    impl.append("""
class reader {
public:
    virtual int fdes() = 0;
    virtual void read() = 0;
    virtual void bind() {}
    virtual bool running() {return fdes() >= 0;}
    virtual ~reader() {}
};

class timer {
public:
    virtual int ms_delay() = 0;
    virtual void timeout(int) = 0;
    virtual ~timer() {}
};

#ifdef _WIN32
DWORD WINAPI ReaderThreadFunction( LPVOID lpParam ) 
{
    reader *cr = (reader *) lpParam;
    cr->bind();
    while (true)
        cr->read();
    return 0;
} 

DWORD WINAPI TimerThreadFunction( LPVOID lpParam ) 
{
    timer *cr = (timer *) lpParam;
    while (true) {
        int ms = cr->ms_delay();
        Sleep(ms);
        cr->timeout(ms);
    }
    return 0;
} 
#else
void * _thread_reader(void *rdr_void) {
    reader *rdr = (reader *) rdr_void;
    rdr->bind();
    while(rdr->running()) {
        rdr->read();
    }
    delete rdr;
    return 0; // just to stop warning
}

void * _thread_timer( void *tmr_void ) 
{
    timer *tmr = (timer *) tmr_void;
    while (true) {
        int ms = tmr->ms_delay();
        struct timespec ts;
        ts.tv_sec = ms/1000;
        ts.tv_nsec = (ms % 1000) * 1000000;
        nanosleep(&ts,NULL);
        tmr->timeout(ms);
    }
    return 0;
} 
#endif 
""")

    if target.get() == "repl":
        impl.append("""
void CLASSNAME::install_reader(reader *r) {
    #ifdef _WIN32

        DWORD dummy;
        HANDLE h = CreateThread( 
            NULL,                   // default security attributes
            0,                      // use default stack size  
            ReaderThreadFunction,   // thread function name
            r,                      // argument to thread function 
            0,                      // use default creation flags 
            &dummy);                // returns the thread identifier 
        if (h == NULL) {
            std::cerr << "failed to create thread" << std::endl;
            exit(1);
        }
        thread_ids.push_back(h);
    #else
        pthread_t thread;
        int res = pthread_create(&thread, NULL, _thread_reader, r);
        if (res) {
            std::cerr << "failed to create thread" << std::endl;
            exit(1);
        }
        thread_ids.push_back(thread);
    #endif
}      

void CLASSNAME::install_thread(reader *r) {
    install_reader(r);
}

void CLASSNAME::install_timer(timer *r) {
    #ifdef _WIN32

        DWORD dummy;
        HANDLE h = CreateThread( 
            NULL,                   // default security attributes
            0,                      // use default stack size  
            TimersThreadFunction,   // thread function name
            r,                      // argument to thread function 
            0,                      // use default creation flags 
            &dummy);                // returns the thread identifier 
        if (h == NULL) {
            std::cerr << "failed to create thread" << std::endl;
            exit(1);
        }
        thread_ids.push_back(h);
    #else
        pthread_t thread;
        int res = pthread_create(&thread, NULL, _thread_timer, r);
        if (res) {
            std::cerr << "failed to create thread" << std::endl;
            exit(1);
        }
        thread_ids.push_back(thread);
    #endif
}      

""".replace('CLASSNAME',classname))

    if target.get() == "test":
        impl.append("""
std::vector<reader *> threads;
std::vector<reader *> readers;
std::vector<timer *> timers;
bool initializing = false;

void CLASSNAME::install_reader(reader *r) {
    readers.push_back(r);
    if (!::initializing)
        r->bind();
}

void CLASSNAME::install_thread(reader *r) {
    #ifdef _WIN32

        DWORD dummy;
        HANDLE h = CreateThread( 
            NULL,                   // default security attributes
            0,                      // use default stack size  
            ReaderThreadFunction,   // thread function name
            r,                      // argument to thread function 
            0,                      // use default creation flags 
            &dummy);                // returns the thread identifier 
        if (h == NULL) {
            std::cerr << "failed to create thread" << std::endl;
            exit(1);
        }
        thread_ids.push_back(h);
    #else
        pthread_t thread;
        int res = pthread_create(&thread, NULL, _thread_reader, r);
        if (res) {
            std::cerr << "failed to create thread" << std::endl;
            exit(1);
        }
        thread_ids.push_back(thread);
    #endif
}      

void CLASSNAME::install_timer(timer *r) {
    timers.push_back(r);
}
""".replace('CLASSNAME',classname))

    impl.append("""
#ifdef _WIN32
    void CLASSNAME::__lock() { WaitForSingleObject(mutex,INFINITE); }
    void CLASSNAME::__unlock() { ReleaseMutex(mutex); }
#else
    void CLASSNAME::__lock() { pthread_mutex_lock(&mutex); }
    void CLASSNAME::__unlock() { pthread_mutex_unlock(&mutex); }
#endif
""".replace('CLASSNAME',classname))
    native_exprs = []
    for n in im.module.natives:
        native_exprs.extend(n.args[2:])
    for actn,actb in im.module.actions.iteritems():
        for n in actb.iter_subactions():
            if isinstance(n,ia.NativeAction):
                native_exprs.extend(n.args[1:])
    callbacks = set()
    for e in native_exprs:
        if isinstance(e,ivy_ast.Atom) and e.rep in im.module.actions:
            callbacks.add(e.rep)
    for actname in sorted(callbacks):
        action = im.module.actions[actname]
        create_thunk(impl,actname,action,classname)

    if target.get() in ["test"]:
        sf = header if target.get() == "gen" else impl
        emit_boilerplate1(sf,impl,classname)

    impl.append(hash_cpp)

    impl.append("""


struct ivy_value {
    int pos;
    std::string atom;
    std::vector<ivy_value> fields;
    bool is_member() const {
        return atom.size() && fields.size();
    }
};
struct deser_err {
};

struct ivy_ser {
    virtual void  set(long long) = 0;
    virtual void  set(bool) = 0;
    virtual void  setn(long long inp, int len) = 0;
    virtual void  set(const std::string &) = 0;
    virtual void  open_list(int len) = 0;
    virtual void  close_list() = 0;
    virtual void  open_list_elem() = 0;
    virtual void  close_list_elem() = 0;
    virtual void  open_struct() = 0;
    virtual void  close_struct() = 0;
    virtual void  open_field(const std::string &) = 0;
    virtual void  close_field() = 0;
    virtual void  open_tag(int, const std::string &) {throw deser_err();}
    virtual void  close_tag() {}
    virtual ~ivy_ser(){}
};
struct ivy_binary_ser : public ivy_ser {
    std::vector<char> res;
    void setn(long long inp, int len) {
        for (int i = len-1; i >= 0 ; i--)
            res.push_back((inp>>(8*i))&0xff);
    }
    void set(long long inp) {
        setn(inp,sizeof(long long));
    }
    void set(bool inp) {
        set((long long)inp);
    }
    void set(const std::string &inp) {
        for (unsigned i = 0; i < inp.size(); i++)
            res.push_back(inp[i]);
        res.push_back(0);
    }
    void open_list(int len) {
        set((long long)len);
    }
    void close_list() {}
    void open_list_elem() {}
    void close_list_elem() {}
    void open_struct() {}
    void close_struct() {}
    virtual void  open_field(const std::string &) {}
    void close_field() {}
    virtual void  open_tag(int tag, const std::string &) {
        set((long long)tag);
    }
    virtual void  close_tag() {}
};

struct ivy_deser {
    virtual void  get(long long&) = 0;
    virtual void  get(std::string &) = 0;
    virtual void  getn(long long &res, int bytes) = 0;
    virtual void  open_list() = 0;
    virtual void  close_list() = 0;
    virtual bool  open_list_elem() = 0;
    virtual void  close_list_elem() = 0;
    virtual void  open_struct() = 0;
    virtual void  close_struct() = 0;
    virtual void  open_field(const std::string &) = 0;
    virtual void  close_field() = 0;
    virtual int   open_tag(const std::vector<std::string> &) {throw deser_err();}
    virtual void  close_tag() {}
    virtual void  end() = 0;
    virtual ~ivy_deser(){}
};

struct ivy_binary_deser : public ivy_deser {
    std::vector<char> inp;
    int pos;
    std::vector<int> lenstack;
    ivy_binary_deser(const std::vector<char> &inp) : inp(inp),pos(0) {}
    virtual bool more(unsigned bytes) {return inp.size() >= pos + bytes;}
    virtual bool can_end() {return pos == inp.size();}
    void get(long long &res) {
       getn(res,8);
    }
    void getn(long long &res, int bytes) {
        if (!more(bytes))
            throw deser_err();
        res = 0;
        for (int i = 0; i < bytes; i++)
            res = (res << 8) | (((long long)inp[pos++]) & 0xff);
    }
    void get(std::string &res) {
        while (more(1) && inp[pos]) {
//            if (inp[pos] == '\"')
//                throw deser_err();
            res.push_back(inp[pos++]);
        }
        if(!(more(1) && inp[pos] == 0))
            throw deser_err();
        pos++;
    }
    void open_list() {
        long long len;
        get(len);
        lenstack.push_back(len);
    }
    void close_list() {
        lenstack.pop_back();
    }
    bool open_list_elem() {
        return lenstack.back();
    }
    void close_list_elem() {
        lenstack.back()--;
    }
    void open_struct() {}
    void close_struct() {}
    virtual void  open_field(const std::string &) {}
    void close_field() {}
    int open_tag(const std::vector<std::string> &tags) {
        long long res;
        get(res);
        if (res >= tags.size())
            throw deser_err();
        return res;
    }
    void end() {
        if (!can_end())
            throw deser_err();
    }
};
struct ivy_socket_deser : public ivy_binary_deser {
      int sock;
    public:
      ivy_socket_deser(int sock, const std::vector<char> &inp)
          : ivy_binary_deser(inp), sock(sock) {}
    virtual bool more(unsigned bytes) {
        while (inp.size() < pos + bytes) {
            int oldsize = inp.size();
            int get = pos + bytes - oldsize;
            get = (get < 1024) ? 1024 : get;
            inp.resize(oldsize + get);
            int newbytes;
	    if ((newbytes = read(sock,&inp[oldsize],get)) < 0)
		 { std::cerr << "recvfrom failed\\n"; exit(1); }
            inp.resize(oldsize + newbytes);
            if (newbytes == 0)
                 return false;
        }
        return true;
    }
    virtual bool can_end() {return true;}
};

struct out_of_bounds {
    std::string txt;
    int pos;
    out_of_bounds(int _idx, int pos = 0) : pos(pos){
        std::ostringstream os;
        os << "argument " << _idx+1;
        txt = os.str();
    }
    out_of_bounds(const std::string &s, int pos = 0) : txt(s), pos(pos) {}
};

template <class T> T _arg(std::vector<ivy_value> &args, unsigned idx, long long bound);
template <class T> T __lit(const char *);

template <>
bool _arg<bool>(std::vector<ivy_value> &args, unsigned idx, long long bound) {
    if (!(args[idx].atom == "true" || args[idx].atom == "false") || args[idx].fields.size())
        throw out_of_bounds(idx,args[idx].pos);
    return args[idx].atom == "true";
}

template <>
int _arg<int>(std::vector<ivy_value> &args, unsigned idx, long long bound) {
    std::istringstream s(args[idx].atom.c_str());
    s.unsetf(std::ios::dec);
    s.unsetf(std::ios::hex);
    s.unsetf(std::ios::oct);
    long long res;
    s  >> res;
    // int res = atoi(args[idx].atom.c_str());
    if (bound && (res < 0 || res >= bound) || args[idx].fields.size())
        throw out_of_bounds(idx,args[idx].pos);
    return res;
}

template <>
long long _arg<long long>(std::vector<ivy_value> &args, unsigned idx, long long bound) {
    std::istringstream s(args[idx].atom.c_str());
    s.unsetf(std::ios::dec);
    s.unsetf(std::ios::hex);
    s.unsetf(std::ios::oct);
    long long res;
    s  >> res;
//    long long res = atoll(args[idx].atom.c_str());
    if (bound && (res < 0 || res >= bound) || args[idx].fields.size())
        throw out_of_bounds(idx,args[idx].pos);
    return res;
}

template <>
unsigned long long _arg<unsigned long long>(std::vector<ivy_value> &args, unsigned idx, long long bound) {
    std::istringstream s(args[idx].atom.c_str());
    s.unsetf(std::ios::dec);
    s.unsetf(std::ios::hex);
    s.unsetf(std::ios::oct);
    unsigned long long res;
    s  >> res;
//    unsigned long long res = atoll(args[idx].atom.c_str());
    if (bound && (res < 0 || res >= bound) || args[idx].fields.size())
        throw out_of_bounds(idx,args[idx].pos);
    return res;
}

template <>
unsigned _arg<unsigned>(std::vector<ivy_value> &args, unsigned idx, long long bound) {
    std::istringstream s(args[idx].atom.c_str());
    s.unsetf(std::ios::dec);
    s.unsetf(std::ios::hex);
    s.unsetf(std::ios::oct);
    unsigned res;
    s  >> res;
//    unsigned res = atoll(args[idx].atom.c_str());
    if (bound && (res < 0 || res >= bound) || args[idx].fields.size())
        throw out_of_bounds(idx,args[idx].pos);
    return res;
}


std::ostream &operator <<(std::ostream &s, const __strlit &t){
    s << "\\"" << t.c_str() << "\\"";
    return s;
}

template <>
__strlit _arg<__strlit>(std::vector<ivy_value> &args, unsigned idx, long long bound) {
    if (args[idx].fields.size())
        throw out_of_bounds(idx,args[idx].pos);
    return args[idx].atom;
}

template <class T> void __ser(ivy_ser &res, const T &inp);

template <>
void __ser<int>(ivy_ser &res, const int &inp) {
    res.set((long long)inp);
}

template <>
void __ser<long long>(ivy_ser &res, const long long &inp) {
    res.set(inp);
}

template <>
void __ser<unsigned long long>(ivy_ser &res, const unsigned long long &inp) {
    res.set((long long)inp);
}

template <>
void __ser<unsigned>(ivy_ser &res, const unsigned &inp) {
    res.set((long long)inp);
}

template <>
void __ser<bool>(ivy_ser &res, const bool &inp) {
    res.set(inp);
}

template <>
void __ser<__strlit>(ivy_ser &res, const __strlit &inp) {
    res.set(inp);
}

template <class T> void __deser(ivy_deser &inp, T &res);

template <>
void __deser<int>(ivy_deser &inp, int &res) {
    long long temp;
    inp.get(temp);
    res = temp;
}

template <>
void __deser<long long>(ivy_deser &inp, long long &res) {
    inp.get(res);
}

template <>
void __deser<unsigned long long>(ivy_deser &inp, unsigned long long &res) {
    long long temp;
    inp.get(temp);
    res = temp;
}

template <>
void __deser<unsigned>(ivy_deser &inp, unsigned &res) {
    long long temp;
    inp.get(temp);
    res = temp;
}

template <>
void __deser<__strlit>(ivy_deser &inp, __strlit &res) {
    inp.get(res);
}

template <>
void __deser<bool>(ivy_deser &inp, bool &res) {
    long long thing;
    inp.get(thing);
    res = thing;
}

class gen;

""")
    if target.get() in ["gen","test"]:
        impl.append("""
template <class T> void __from_solver( gen &g, const  z3::expr &v, T &res);

template <>
void __from_solver<int>( gen &g, const  z3::expr &v, int &res) {
    res = g.eval(v);
}

template <>
void __from_solver<long long>( gen &g, const  z3::expr &v, long long &res) {
    res = g.eval(v);
}

template <>
void __from_solver<unsigned long long>( gen &g, const  z3::expr &v, unsigned long long &res) {
    res = g.eval(v);
}

template <>
void __from_solver<unsigned>( gen &g, const  z3::expr &v, unsigned &res) {
    res = g.eval(v);
}

template <>
void __from_solver<bool>( gen &g, const  z3::expr &v, bool &res) {
    res = g.eval(v);
}

template <>
void __from_solver<__strlit>( gen &g, const  z3::expr &v, __strlit &res) {
    res = g.eval_string(v);
}

template <class T>
class to_solver_class {
};

template <class T> z3::expr __to_solver( gen &g, const  z3::expr &v, T &val) {
    return to_solver_class<T>()(g,v,val);
}


template <>
z3::expr __to_solver<int>( gen &g, const  z3::expr &v, int &val) {
    return v == g.int_to_z3(v.get_sort(),val);
}

template <>
z3::expr __to_solver<long long>( gen &g, const  z3::expr &v, long long &val) {
    return v == g.int_to_z3(v.get_sort(),val);
}

template <>
z3::expr __to_solver<unsigned long long>( gen &g, const  z3::expr &v, unsigned long long &val) {
    return v == g.int_to_z3(v.get_sort(),val);
}

template <>
z3::expr __to_solver<unsigned>( gen &g, const  z3::expr &v, unsigned &val) {
    return v == g.int_to_z3(v.get_sort(),val);
}

template <>
z3::expr __to_solver<bool>( gen &g, const  z3::expr &v, bool &val) {
    return v == g.int_to_z3(v.get_sort(),val);
}

template <>
z3::expr __to_solver<__strlit>( gen &g, const  z3::expr &v, __strlit &val) {
//    std::cout << v << ":" << v.get_sort() << std::endl;
    return v == g.int_to_z3(v.get_sort(),val);
}

template <class T>
class __random_string_class {
public:
    std::string operator()() {
        std::string res;
        res.push_back('a' + (rand() % 26)); // no empty strings for now
        while (rand() %2)
            res.push_back('a' + (rand() % 26));
        return res;
    }
};

template <class T> std::string __random_string(){
    return __random_string_class<T>()();
}

template <class T> void __randomize( gen &g, const  z3::expr &v);

template <>
void __randomize<int>( gen &g, const  z3::expr &v) {
    g.randomize(v);
}

template <>
void __randomize<long long>( gen &g, const  z3::expr &v) {
    g.randomize(v);
}

template <>
void __randomize<unsigned long long>( gen &g, const  z3::expr &v) {
    g.randomize(v);
}

template <>
void __randomize<unsigned>( gen &g, const  z3::expr &v) {
    g.randomize(v);
}

template <>
void __randomize<bool>( gen &g, const  z3::expr &v) {
    g.randomize(v);
}

template <>
        void __randomize<__strlit>( gen &g, const  z3::expr &apply_expr) {
    z3::sort range = apply_expr.get_sort();
    __strlit value = (rand() % 2) ? "a" : "b";
    z3::expr val_expr = g.int_to_z3(range,value);
    z3::expr pred = apply_expr == val_expr;
    g.add_alit(pred);
}

template<typename D, typename R>
class z3_thunk : public thunk<D,R> {
    public:
       virtual z3::expr to_z3(gen &g, const  z3::expr &v) = 0;
};

""")

    for sort_name in [s for s in sorted(il.sig.sorts) if isinstance(il.sig.sorts[s],il.EnumeratedSort)]:
        csname = varname(sort_name)
        cfsname = classname + '::' + csname
        if sort_name not in encoded_sorts:
            impl.append('std::ostream &operator <<(std::ostream &s, const {} &t);\n'.format(cfsname))
            impl.append('template <>\n')
            impl.append(cfsname + ' _arg<' + cfsname + '>(std::vector<ivy_value> &args, unsigned idx, long long bound);\n')
            impl.append('template <>\n')
            impl.append('void  __ser<' + cfsname + '>(ivy_ser &res, const ' + cfsname + '&);\n')
            impl.append('template <>\n')
            impl.append('void  __deser<' + cfsname + '>(ivy_deser &inp, ' + cfsname + ' &res);\n')                
        if target.get() in ["test","gen"]:
            impl.append('template <>\n')
            impl.append('void __from_solver<' + cfsname + '>( gen &g, const  z3::expr &v, ' + cfsname + ' &res);\n')
            impl.append('template <>\n')
            impl.append('z3::expr __to_solver<' + cfsname + '>( gen &g, const  z3::expr &v, ' + cfsname + ' &val);\n')
            impl.append('template <>\n')
            impl.append('void __randomize<' + cfsname + '>( gen &g, const  z3::expr &v);\n')
        
    if True or target.get() == "repl":
        for sort_name in sorted(im.module.sort_destructors):
            csname = varname(sort_name)
            cfsname = classname + '::' + csname
            if sort_name not in encoded_sorts:
                impl.append('std::ostream &operator <<(std::ostream &s, const {} &t);\n'.format(cfsname))
                impl.append('template <>\n')
                impl.append(cfsname + ' _arg<' + cfsname + '>(std::vector<ivy_value> &args, unsigned idx, long long bound);\n')
                impl.append('template <>\n')
                impl.append('void  __ser<' + cfsname + '>(ivy_ser &res, const ' + cfsname + '&);\n')
                impl.append('template <>\n')
                impl.append('void  __deser<' + cfsname + '>(ivy_deser &inp, ' + cfsname + ' &res);\n')                

    if target.get() in ["test","gen"]:
        for sort_name in sorted(im.module.sort_destructors):
            csname = varname(sort_name)
            cfsname = classname + '::' + csname
            impl.append('template <>\n')
            impl.append('void __from_solver<' + cfsname + '>( gen &g, const  z3::expr &v, ' + cfsname + ' &res);\n')
            impl.append('template <>\n')
            impl.append('z3::expr __to_solver<' + cfsname + '>( gen &g, const  z3::expr &v, ' + cfsname + ' &val);\n')
            impl.append('template <>\n')
            impl.append('void __randomize<' + cfsname + '>( gen &g, const  z3::expr &v);\n')

    for dom in all_ctuples():
        emit_ctuple_equality(impl,dom,classname)

    for cpptype in cpptypes:
        cpptype.emit_templates()

    global native_classname
    once_memo = set()
    for native in im.module.natives:
        tag = native_type(native)
        if tag == "impl" or tag.startswith('encode'):
            native_classname = classname
#            print 'native_classname:{}'.format(native_classname)
            code = native_to_str(native)
            native_classname = None
            if code not in once_memo:
                once_memo.add(code)
                impl.append(code)


    impl.append("int " + classname)
    if target.get() in ["gen","test"]:
        impl.append(
"""::___ivy_choose(int rng,const char *name,int id) {
        std::ostringstream ss;
        ss << name << ':' << id;;
        for (unsigned i = 0; i < ___ivy_stack.size(); i++)
            ss << ':' << ___ivy_stack[i];
        return ___ivy_gen->choose(rng,ss.str().c_str());
    }
""")
    else:
        impl.append(
"""::___ivy_choose(int rng,const char *name,int id) {
        return 0;
    }
""")

    with ivy_cpp.CppClassName(classname):
        declare_all_ctuples(header)
        declare_all_ctuples_hash(header,classname)
        for sym in all_state_symbols():
            if sym_is_member(sym):
                declare_symbol(header,sym)
#    for sym in il.sig.constructors:
#        declare_symbol(header,sym)
    for sname in il.sig.interp:
        header.append('    long long __CARD__' + varname(sname) + ';\n')
    find_import_callers()
    for ldf in im.module.definitions + im.module.native_definitions:
        with ivy_ast.ASTContext(ldf):
            emit_derived(header,impl,ldf.formula,classname)
    for sortname, conss in im.module.sort_constructors.iteritems():
        for cons in conss:
            emit_constructor(header,impl,cons,classname)
    for native in im.module.natives:
        tag = native_type(native)
        if tag.startswith('encode'):
            tag = native_to_str(native,code=tag) # do the anti-quoting
            tag = tag[6:].strip().replace('__','.')
            if tag not in il.sig.sorts:
                raise iu.IvyError(native,"{} is not a declared sort".format(tag))
            if tag in encoded_sorts:
                raise iu.IvyError(native,"duplicate encoding for sort {}".format(tag))
            encoded_sorts.add(tag)
            continue
        if tag not in ["member","init","header","impl","inline"]:
            raise iu.IvyError(native,"syntax error at token {}".format(tag))
        if tag == "member":
            emit_native(header,impl,native,classname)

    # declare one counter for each progress obligation
    # TRICKY: these symbols are boolean but we create a C++ int
    for df in im.module.progress:
        declare_symbol(header,df.args[0].rep,c_type = 'int')

    header.append('    ');
    emit_param_decls(header,classname,im.module.params)
    header.append(';\n');
    im.module.actions['.init'] = init_method()
    for a in im.module.actions:
        emit_action(header,impl,a,classname)
    emit_tick(header,impl,classname)
    header.append('};\n')

    impl.append(classname + '::')
    emit_param_decls(impl,classname,im.module.params)
    impl.append('{\n')
    impl.append('#ifdef _WIN32\n');
    impl.append('mutex = CreateMutex(NULL,FALSE,NULL);\n')
    impl.append('#else\n');
    impl.append('pthread_mutex_init(&mutex,NULL);\n')
    impl.append('#endif\n');
    impl.append('__lock();\n');
    enums = set(sym.sort.name for sym in il.sig.constructors)  
#    for sortname in enums:
#        for i,n in enumerate(il.sig.sorts[sortname].extension):
#            impl.append('    {} = {};\n'.format(varname(n),i))
    for sortname in il.sig.interp:
        if sortname in il.sig.sorts:
            impl.append('    __CARD__{} = {};\n'.format(varname(sortname),csortcard(il.sig.sorts[sortname])))
    for native in im.module.natives:
        tag = native_type(native)
        if tag == "init":
            vs = [il.Symbol(v.rep,im.module.sig.sorts[v.sort]) for v in native.args[0].args] if native.args[0] is not None else []
            global indent_level
            indent_level += 1
            open_loop(impl,vs)
            code = native_to_str(native,reference=True)
            indent_code(impl,code)
            close_loop(impl,vs)
            indent_level -= 1
    if target.get() not in ["gen","test"]:
        emit_one_initial_state(impl)
    else:
        emit_parameter_assignments(impl)

    impl.append('}\n')

    impl.append("""CLASSNAME::~CLASSNAME(){
    __lock(); // otherwise, thread may die holding lock!
    for (unsigned i = 0; i < thread_ids.size(); i++){
#ifdef _WIN32
       // No idea how to cancel a thread on Windows. We just suspend it
       // so it can't cause any harm as we destruct this object.
       SuspendThread(thread_ids[i]);
#else
        pthread_cancel(thread_ids[i]);
        pthread_join(thread_ids[i],NULL);
#endif
    }
    __unlock();
}
""".replace('CLASSNAME',classname))

    for native in im.module.natives:
        tag = native_type(native)
        if tag == "inline":
            native_classname = classname
            code = native_to_str(native)
            native_classname = None
            if code not in once_memo:
                once_memo.add(code)
                header.append(code)


    ivy_cpp.context.globals.code.extend(header)
    ivy_cpp.context.members.code = []
    header = ivy_cpp.context.globals.code

    if target.get() in ["gen","test"]:
        sf = header if target.get() == "gen" else impl
        if target.get() == "gen":
            emit_boilerplate1(sf,impl,classname)
        emit_init_gen(sf,impl,classname)
        for name,action in im.module.actions.iteritems():
            if name in im.module.public_actions:
                emit_action_gen(sf,impl,name,action,classname)

    enum_sort_names = [s for s in sorted(il.sig.sorts) if isinstance(il.sig.sorts[s],il.EnumeratedSort)]
    if True or target.get() == "repl":

        # forward declare all the equality operations for variant types

        for sort_name in im.module.sort_order:
            if sort_name in im.module.variants:
                csname = varname(sort_name)
                cfsname = classname + '::' + csname
                code_line(header,'inline bool operator ==(const {} &s, const {} &t);'.format(cfsname,cfsname))


        # Tricky: inlines for for supertypes have to come *after* the inlines
        # for the subtypes. So we re-sort the types accordingly.
        arcs = [(x,s) for s in im.module.sort_order for x in im.sort_dependencies(im.module,s,with_variants=True)]
        variant_of = set((x.name,y) for y,l in im.module.variants.iteritems() for x in l)
        arcs = [a for a in arcs if a in variant_of]
        inline_sort_order = iu.topological_sort(im.module.sort_order,arcs)
        for sort_name in inline_sort_order:
            if sort_name in im.module.variants:
                sort = im.module.sig.sorts[sort_name] 
                assert sort in sort_to_cpptype
                if sort in sort_to_cpptype:
                    sort_to_cpptype[sort].emit_inlines()
                continue
            if sort_name not in sorted(im.module.sort_destructors):
                continue
            destrs = im.module.sort_destructors[sort_name]
            sort = im.module.sig.sorts[sort_name]
            csname = varname(sort_name)
            cfsname = classname + '::' + csname
            if sort_name not in encoded_sorts:
                open_scope(impl,line='std::ostream &operator <<(std::ostream &s, const {} &t)'.format(cfsname))
                code_line(impl,'s<<"{"')
                for idx,sym in enumerate(destrs):
                    if idx > 0:
                        code_line(impl,'s<<","')
                    code_line(impl,'s<< "' + memname(sym) + ':"')
                    dom = sym.sort.dom[1:]
                    vs = variables(dom)
                    for d,v in zip(dom,vs):
                        code_line(impl,'s << "["')
                        open_loop(impl,[v])
                        code_line(impl,'if ({}) s << ","'.format(varname(v)))
                    code_line(impl,'s << t.' + memname(sym) + subscripts(vs))
                    for d,v in zip(dom,vs):
                        close_loop(impl,[v])
                        code_line(impl,'s << "]"')
                code_line(impl,'s<<"}"')
                code_line(impl,'return s')
                close_scope(impl)

            open_scope(header,line='inline bool operator ==(const {} &s, const {} &t)'.format(cfsname,cfsname))
            s = il.Symbol('s',sort)
            t = il.Symbol('t',sort)
            code_line(header,'return ' + code_eval(header,il.And(*[field_eq(s,t,sym) for sym in destrs])))
            close_scope(header)

            if sort_name not in encoded_sorts:
                impl.append('template <>\n')
                open_scope(impl,line='void  __ser<' + cfsname + '>(ivy_ser &res, const ' + cfsname + '&t)')
                code_line(impl,"res.open_struct()")
                for idx,sym in enumerate(destrs):
                    dom = sym.sort.dom[1:]
                    vs = variables(dom)
                    for d,v in zip(dom,vs):
                        open_loop(impl,[v])
                    code_line(impl,'res.open_field("'+memname(sym)+'")')
                    code_line(impl,'__ser<' + ctype(sym.sort.rng,classname=classname) + '>(res,t.' + memname(sym) + subscripts(vs) + ')')
                    code_line(impl,'res.close_field()')
                    for d,v in zip(dom,vs):
                        close_loop(impl,[v])
                code_line(impl,"res.close_struct()")
                close_scope(impl)


        for sort_name in enum_sort_names:
            sort = im.module.sig.sorts[sort_name]
            csname = varname(sort_name)
            cfsname = classname + '::' + csname
            if sort_name not in encoded_sorts:
                open_scope(impl,line='std::ostream &operator <<(std::ostream &s, const {} &t)'.format(cfsname))
                for idx,sym in enumerate(sort.extension):
                    code_line(impl,'if (t == {}) s<<"{}"'.format(classname + '::' + varname(sym),memname(sym)))
                code_line(impl,'return s')
                close_scope(impl)
                impl.append('template <>\n')
                open_scope(impl,line='void  __ser<' + cfsname + '>(ivy_ser &res, const ' + cfsname + '&t)')
                code_line(impl,'__ser(res,(int)t)')
                close_scope(impl)


        if target.get() in ["repl","test"]:

            if  emit_main:
                emit_repl_imports(header,impl,classname)
                emit_repl_boilerplate1(header,impl,classname)

            for sort_name in sorted(im.module.sort_destructors):
                destrs = im.module.sort_destructors[sort_name]
                sort = im.module.sig.sorts[sort_name]
                csname = varname(sort_name)
                cfsname = classname + '::' + csname
                if sort_name not in encoded_sorts:
                    impl.append('template <>\n')
                    open_scope(impl,line=cfsname + ' _arg<' + cfsname + '>(std::vector<ivy_value> &args, unsigned idx, long long bound)')
                    code_line(impl,cfsname + ' res')
                    code_line(impl,'ivy_value &arg = args[idx]')
                    code_line(impl,'if (arg.atom.size() || arg.fields.size() != {}) throw out_of_bounds("wrong number of fields",args[idx].pos)'.format(len(destrs)))
                    code_line(impl,'std::vector<ivy_value> tmp_args(1)')
                    for idx,sym in enumerate(destrs):
                        open_scope(impl,line='if (arg.fields[{}].is_member())'.format(idx))
                        code_line(impl,'tmp_args[0] = arg.fields[{}].fields[0]'.format(idx))
                        fname = memname(sym)
                        code_line(impl,'if (arg.fields[{}].atom != "{}") throw out_of_bounds("unexpected field: " + arg.fields[{}].atom,arg.fields[{}].pos)'.format(idx,fname,idx,idx))
                        close_scope(impl)
                        open_scope(impl,line='else')
                        code_line(impl,'tmp_args[0] = arg.fields[{}]'.format(idx))
                        close_scope(impl)
                        vs = variables(sym.sort.dom[1:])
                        for v in vs:
                            open_scope(impl)
                            code_line(impl,'ivy_value tmp = tmp_args[0]')
                            code_line(impl,'if(tmp.atom.size() || tmp.fields.size() != {}) throw out_of_bounds(idx,tmp.pos)'.format(csortcard(v.sort)))
                            open_loop(impl,[v])
                            code_line(impl,'std::vector<ivy_value> tmp_args(1)')
                            code_line(impl,'tmp_args[0] = tmp.fields[{}]'.format(varname(v)))
                        open_scope(impl,line='try')
                        code_line(impl,'res.'+fname+''.join('[{}]'.format(varname(v)) for v in vs) + ' = _arg<'+ctype(sym.sort.rng,classname=classname)
                                  +'>(tmp_args,0,{});\n'.format(csortcard(sym.sort.rng)))
                        close_scope(impl)
                        open_scope(impl,line='catch(const out_of_bounds &err)')
                        code_line(impl,'throw out_of_bounds("in field {}: " + err.txt,err.pos)'.format(fname))
                        close_scope(impl)
                        for v in vs:
                            close_loop(impl,[v])
                            close_scope(impl)
                    code_line(impl,'return res')
                    close_scope(impl)

                    impl.append('template <>\n')
                    open_scope(impl,line='void __deser<' + cfsname + '>(ivy_deser &inp, ' + cfsname + ' &res)')
                    code_line(impl,"inp.open_struct()")
                    for idx,sym in enumerate(destrs):
                        fname = memname(sym)
                        vs = variables(sym.sort.dom[1:])
                        code_line(impl,'inp.open_field("'+fname+'")')
                        for v in vs:
                            card = sort_card(v.sort)
                            code_line(impl,'inp.open_list('+str(card)+')')
                            open_loop(impl,[v])
                        code_line(impl,'__deser(inp,res.'+fname+''.join('[{}]'.format(varname(v)) for v in vs) + ')')
                        for v in vs:
                            close_loop(impl,[v])
                            code_line(impl,'inp.close_list()')
                        code_line(impl,'inp.close_field()')
                    code_line(impl,"inp.close_struct()")
                    close_scope(impl)
                if target.get() in ["gen","test"]:
                    impl.append('template <>\n')
                    open_scope(impl,line='void  __from_solver<' + cfsname + '>( gen &g, const  z3::expr &v,' + cfsname + ' &res)')
                    for idx,sym in enumerate(destrs):
                        fname = memname(sym)
                        vs = variables(sym.sort.dom[1:])
                        for v in vs:
                            open_loop(impl,[v])
                        sname = slv.solver_name(sym)
                        code_line(impl,'__from_solver(g,g.apply("'+sname+'",v'+ ''.join(',g.int_to_z3(g.sort("'+v.sort.name+'"),'+varname(v)+')' for v in vs)+'),res.'+fname+''.join('[{}]'.format(varname(v)) for v in vs) + ')')
                        for v in vs:
                            close_loop(impl,[v])
                    close_scope(impl)
                    impl.append('template <>\n')
                    open_scope(impl,line='z3::expr  __to_solver<' + cfsname + '>( gen &g, const  z3::expr &v,' + cfsname + ' &val)')
                    code_line(impl,'z3::expr res = g.ctx.bool_val(1)')
                    for idx,sym in enumerate(destrs):
                        fname = memname(sym)
                        vs = variables(sym.sort.dom[1:])
                        for v in vs:
                            open_loop(impl,[v])
                        sname = slv.solver_name(sym)
                        code_line(impl,'res = res && __to_solver(g,g.apply("'+sname+'",v'+ ''.join(',g.int_to_z3(g.sort("'+v.sort.name+'"),'+varname(v)+')' for v in vs)+'),val.'+fname+''.join('[{}]'.format(varname(v)) for v in vs) + ')')
                        for v in vs:
                            close_loop(impl,[v])
                    code_line(impl,'return res')
                    close_scope(impl)
                    impl.append('template <>\n')
                    open_scope(impl,line='void  __randomize<' + cfsname + '>( gen &g, const  z3::expr &v)')
                    for idx,sym in enumerate(destrs):
                        # we can't randomize a type that z3 is representing with an uninterpreted sort,
                        # because z3 has no numerals for these sorts. Rather than throwing an error, however,
                        # we just don't randomize, in case randomization for this type is not actually needed.
                        # In principle, we should check whether randomiation is needed but this is pretty tricky.
                        if is_really_uninterpreted_sort(sym.sort.rng):
                            continue
#                            raise iu.IvyError(None,'cannot create test generator because type {} is uninterpreted'.format(sym.sort.rng))
                        fname = memname(sym)
                        vs = variables(sym.sort.dom[1:])
                        for v in vs:
                            open_loop(impl,[v])
                        sname = slv.solver_name(sym)
                        code_line(impl,'__randomize<'+ctypefull(sym.sort.rng,classname=classname)+'>(g,g.apply("'+sname+'",v'+ ''.join(',g.int_to_z3(g.sort("'+v.sort.name+'"),'+varname(v)+')' for v in vs)+'))')
                        for v in vs:
                            close_loop(impl,[v])
                    close_scope(impl)


            for sort_name in enum_sort_names:
                sort = im.module.sig.sorts[sort_name]
                csname = varname(sort_name)
                cfsname = classname + '::' + csname
                if sort_name not in encoded_sorts:
                    impl.append('template <>\n')
                    open_scope(impl,line=cfsname + ' _arg<' + cfsname + '>(std::vector<ivy_value> &args, unsigned idx, long long bound)')
                    code_line(impl,'ivy_value &arg = args[idx]')
                    code_line(impl,'if (arg.atom.size() == 0 || arg.fields.size() != 0) throw out_of_bounds(idx,arg.pos)')
                    for idx,sym in enumerate(sort.extension):
                        code_line(impl,'if(arg.atom == "{}") return {}'.format(memname(sym),classname + '::' + varname(sym)))
                    code_line(impl,'throw out_of_bounds("bad value: " + arg.atom,arg.pos)')
                    close_scope(impl)
                    impl.append('template <>\n')
                    open_scope(impl,line='void __deser<' + cfsname + '>(ivy_deser &inp, ' + cfsname + ' &res)')
                    code_line(impl,'int __res')
                    code_line(impl,'__deser(inp,__res)')
                    code_line(impl,'res = ({})__res'.format(cfsname))
                    close_scope(impl)
                if target.get() in ["test","gen"]:
                    impl.append('template <>\n')
                    open_scope(impl,line='z3::expr  __to_solver<' + cfsname + '>( gen &g, const  z3::expr &v,' + cfsname + ' &val)')
                    code_line(impl,'int thing = val')
                    code_line(impl,'return __to_solver<int>(g,v,thing)')
                    close_scope(impl)
                    impl.append('template <>\n')
                    open_scope(impl,line='void  __from_solver<' + cfsname + '>( gen &g, const  z3::expr &v,' + cfsname + ' &res)')
                    code_line(impl,'int temp')
                    code_line(impl,'__from_solver<int>(g,v,temp)')
                    code_line(impl,'res = ('+cfsname+')temp')
                    close_scope(impl)
                    impl.append('template <>\n')
                    open_scope(impl,line='void  __randomize<' + cfsname + '>( gen &g, const  z3::expr &v)')
                    code_line(impl,'__randomize<int>(g,v)')
                    close_scope(impl)


            if emit_main:
                if target.get() in ["gen","test"]:
                    emit_all_ctuples_to_solver(impl,classname)


                emit_repl_boilerplate1a(header,impl,classname)
                for actname in sorted(im.module.public_actions):
                    username = actname[4:] if actname.startswith("ext:") else actname
                    action = im.module.actions[actname]
                    argstrings = ['_arg<{}>(args,{},{})'.format(ctype(x.sort,classname=classname),idx,csortcard(x.sort)) for idx,x in enumerate(action.formal_params)]
                    getargs = ','.join(argstrings)
                    thing = "ivy.methodname(getargs)"
                    if action.formal_returns:
                        thing = '__ivy_out ' + number_format + ' << "= " << ' + thing + " << std::endl"
                    if target.get() == "repl" and opt_trace.get():
                        if action.formal_params:
                            trace_code = '__ivy_out ' + number_format + ' << "{}("'.format(actname.split(':')[-1]) + ' << "," '.join(' << {}'.format(arg) for arg in argstrings) + ' << ") {" << std::endl'
                        else:
                            trace_code = '__ivy_out ' + number_format + ' << "{} {{"'.format(actname.split(':')[-1]) + ' << std::endl'
                        thing = trace_code + ';\n                    ' + thing + ';\n                    __ivy_out << "}" << std::endl' 
                    impl.append("""
                if (action == "actname") {
                    check_arity(args,numargs,action);
                    thing;
                }
                else
    """.replace('thing',thing).replace('actname',username).replace('methodname',varname(actname)).replace('numargs',str(len(action.formal_params))).replace('getargs',getargs))
                emit_repl_boilerplate2(header,impl,classname)


                impl.append("int "+ opt_main.get() + "(int argc, char **argv){\n")
                impl.append("        int test_iters = TEST_ITERS;\n".replace('TEST_ITERS',opt_test_iters.get()))
                impl.append("        int runs = TEST_RUNS;\n".replace('TEST_RUNS',opt_test_runs.get()))
                for p,d in zip(im.module.params,im.module.param_defaults):
                    impl.append('    {} p__'.format(ctypefull(p.sort,classname=classname))+varname(p)+';\n')
                    if d is not None:
                        emit_value_parser(impl,p,'"{}"'.format(d.rep),classname,lineno=d.lineno)
                impl.append("""
    int seed = 1;
    int sleep_ms = 10;
    int final_ms = 0; 
    
    std::vector<char *> pargs; // positional args
    pargs.push_back(argv[0]);
    for (int i = 1; i < argc; i++) {
        std::string arg = argv[i];
        size_t p = arg.find('=');
        if (p == std::string::npos)
            pargs.push_back(argv[i]);
        else {
            std::string param = arg.substr(0,p);
            std::string value = arg.substr(p+1);
""")
                pos_params = []
                for p,d in zip(im.module.params,im.module.param_defaults):
                    if d is None:
                        pos_params.append(p)
                    else:
                        impl.append('            if (param == "{}") {{\n'.format(str(p)))
                        emit_value_parser(impl,p,"value",classname)
                        impl.append('                continue;\n')
                        impl.append('            }\n')
                
                impl.append("""
            if (param == "out") {
                __ivy_out.open(value.c_str());
                if (!__ivy_out) {
                    std::cerr << "cannot open to write: " << value << std::endl;
                    return 1;
                }
            }
            else if (param == "iters") {
                test_iters = atoi(value.c_str());
            }
            else if (param == "runs") {
                runs = atoi(value.c_str());
            }
            else if (param == "seed") {
                seed = atoi(value.c_str());
            }
            else if (param == "delay") {
                sleep_ms = atoi(value.c_str());
            }
            else if (param == "wait") {
                final_ms = atoi(value.c_str());
            }
            else if (param == "modelfile") {
                __ivy_modelfile.open(value.c_str());
                if (!__ivy_modelfile) {
                    std::cerr << "cannot open to write: " << value << std::endl;
                    return 1;
                }
            }
            else {
                std::cerr << "unknown option: " << param << std::endl;
                return 1;
            }
        }
    }
    srand(seed);
    if (!__ivy_out.is_open())
        __ivy_out.basic_ios<char>::rdbuf(std::cout.rdbuf());
    argc = pargs.size();
    argv = &pargs[0];
""")
                impl.append("    if (argc == "+str(len(pos_params)+2)+"){\n")
                impl.append("        argc--;\n")
                impl.append("        int fd = _open(argv[argc],0);\n")
                impl.append("        if (fd < 0){\n")
                impl.append('            std::cerr << "cannot open to read: " << argv[argc] << "\\n";\n')
                impl.append('            __ivy_exit(1);\n')
                impl.append('        }\n')
                impl.append("        _dup2(fd, 0);\n")
                impl.append("    }\n")
                impl.append("    if (argc != "+str(len(pos_params)+1)+"){\n")
                impl.append('        std::cerr << "usage: {} {}\\n";\n'
                            .format(classname,' '.join(map(str,pos_params))))
                impl.append('        __ivy_exit(1);\n    }\n')
                impl.append('    std::vector<std::string> args;\n')
                impl.append('    std::vector<ivy_value> arg_values({});\n'.format(len(pos_params)))
                impl.append('    for(int i = 1; i < argc;i++){args.push_back(argv[i]);}\n')
                for idx,s in enumerate(pos_params):
                    impl.append('    try {\n')
                    impl.append('        int pos = 0;\n')
                    impl.append('        arg_values[{}] = parse_value(args[{}],pos);\n'.format(idx,idx))
                    impl.append('        p__'+varname(s)+' =  _arg<{}>(arg_values,{},{});\n'
                                .format(ctype(s.sort,classname=classname),idx,csortcard(s.sort)))
                    impl.append('    }\n    catch(out_of_bounds &) {\n')
                    impl.append('        std::cerr << "parameter {} out of bounds\\n";\n'.format(varname(s)))
                    impl.append('        __ivy_exit(1);\n    }\n')
                    impl.append('    catch(syntax_error &) {\n')
                    impl.append('        std::cerr << "syntax error in command argument\\n";\n')
                    impl.append('        __ivy_exit(1);\n    }\n')
                cp = '(' + ','.join('p__'+varname(s) for s in im.module.params) + ')' if im.module.params else ''
                emit_winsock_init(impl)
                if target.get() == "test":
                    impl.append('    for(int runidx = 0; runidx < runs; runidx++) {\n')
                    impl.append('    initializing = true;\n')
                impl.append('    {}_repl ivy{};\n'
                            .format(classname,cp))
                impl.append('    for(unsigned i = 0; i < argc; i++) {ivy.__argv.push_back(argv[i]);}\n')
                if target.get() == "test":
                    impl.append('    ivy._generating = false;\n')
                    emit_repl_boilerplate3test(header,impl,classname)
                else:
                    impl.append("    ivy.__init();\n");
                    if im.module.public_actions:
                        emit_repl_boilerplate3(header,impl,classname)
                    else:
                        emit_repl_boilerplate3server(header,impl,classname)
                if target.get() == "test":
                    impl.append('    }\n')
                impl.append("    return 0;\n}\n")


        
    return ivy_cpp.context.globals.get_file(), ivy_cpp.context.impls.get_file()

def emit_value_parser(impl,s,arg,classname,lineno=None):
    impl.append('    try {\n')
    impl.append('        int pos = 0;\n')
    impl.append('        std::vector<ivy_value> arg_values; arg_values.resize(1); arg_values[0] = parse_value({},pos);\n'.format(arg))
    impl.append('        p__'+varname(s)+' =  _arg<{}>(arg_values,{},{});\n'
                                .format(ctype(s.sort,classname=classname),0,csortcard(s.sort)))
    impl.append('    }\n    catch(out_of_bounds &) {\n')
    impl.append('        std::cerr << "{}parameter {} out of bounds\\n";\n'.format(str(lineno) if lineno else "",str(s)))
    impl.append('        __ivy_exit(1);\n    }\n')
    impl.append('    catch(syntax_error &) {\n')
    impl.append('        std::cerr << "{}syntax error in parameter value {}\\n";\n'.format(str(lineno) if lineno else "",str(s)))
    impl.append('        __ivy_exit(1);\n    }\n')


def check_representable(sym,ast=None,skip_args=0):
    return True

def really_check_representable(sym,ast=None,skip_args=0):
    sort = sym.sort
    if hasattr(sort,'dom'):
        for domsort in sort.dom[skip_args:]:
            card = sort_card(domsort)
            if card == None or card > large_thresh:
                raise iu.IvyError(ast,'cannot compile initial constraint on "{}" because type {} is large. suggest using "after init"'.format(sym,domsort))

def cstr(term):
    if isinstance(term,il.Symbol):
        return varname(term).split('!')[-1]
    return il.fmla_to_str_ambiguous(term)

def subscripts(vs):
    return ''.join('['+varname(v)+']' for v in vs)

def variables(sorts,start=0):
    return [il.Variable('X__'+str(idx+start),s) for idx,s in enumerate(sorts)]


def assign_symbol_value(header,lhs_text,m,v,same=False):
    sort = v.sort
    if hasattr(sort,'name') and sort.name in im.module.sort_destructors:
        for sym in im.module.sort_destructors[sort.name]:
            check_representable(sym,skip_args=1)
            dom = sym.sort.dom[1:]
            if dom:
                if same:
                    vs = variables(dom)
                    open_loop(header,vs)
                    term = sym(*([v] + vs))
                    ctext = memname(sym) + ''.join('['+varname(a)+']' for a in vs)
                    assign_symbol_value(header,lhs_text+[ctext],m,term,same)
                    close_loop(header,vs)
                else:
                    for args in itertools.product(*[range(sort_card(s)) for s in dom]):
                        term = sym(*([v] + [il.Symbol(str(a),s) for a,s in zip(args,dom)]))
                        ctext = memname(sym) + ''.join('['+str(a)+']' for a in args)
                        assign_symbol_value(header,lhs_text+[ctext],m,term,same)
            else:
                assign_symbol_value(header,lhs_text+[memname(sym)],m,sym(v),same)
    else:
        mv = m(v)
        if mv != None:           
            header.append('    ' + '.'.join(lhs_text) + ' = ' + m(v) + ';\n')
        

def assign_symbol_from_model(header,sym,m):
    if slv.solver_name(sym) == None:
        return # skip interpreted symbols
    if sym.name in im.module.destructor_sorts:
        return # skip structs
    name, sort = sym.name,sym.sort
    really_check_representable(sym)
    fun = lambda v: cstr(m.eval_to_constant(v))
    if hasattr(sort,'dom'):
        for args in itertools.product(*[range(sort_card(s)) for s in sym.sort.dom]):
            term = sym(*[il.Symbol(str(a),s) for a,s in zip(args,sym.sort.dom)])
            ctext = varname(sym.name) + ''.join('['+str(a)+']' for a in args)
            assign_symbol_value(header,[ctext],fun,term)
    else:
        assign_symbol_value(header,[varname(sym.name)],fun,sym)

def assign_array_from_model(impl,sym,prefix,fun):
    name, sort = sym.name,sym.sort
    if hasattr(sort,'dom'):
        vs = variables(sym.sort.dom)
        for v in vs:
            open_loop(impl,[v])
        term = sym(*vs)
        ctext = prefix + varname(sym.name) + ''.join('['+v.name+']' for v in vs)
        assign_symbol_value(impl,[ctext],fun,term)
        for v in vs:
            close_loop(impl,[v])
    else:
        assign_symbol_value(impl,[prefix+varname(sym.name)],fun,sym)
        
def check_init_cond(kind,lfmlas):
    params = set(im.module.params)
    for lfmla in lfmlas:
        if any(c in params for c in ilu.used_symbols_ast(lfmla.formula)):
            raise iu.IvyError(lfmla,"{} depends on stripped parameter".format(kind))
        
    
def emit_one_initial_state(header):
    check_init_cond("initial condition",im.module.labeled_inits)
    check_init_cond("axiom",im.module.labeled_axioms)
        
    constraints = [ilu.clauses_to_formula(im.module.init_cond)]
    for a in im.module.axioms:
        constraints.append(a)
    for ldf in im.relevant_definitions(ilu.symbols_asts(constraints)):
        constraints.append(fix_definition(ldf.formula).to_constraint())
    clauses = ilu.formula_to_clauses(il.And(*constraints))
#    clauses = ilu.and_clauses(im.module.init_cond,im.module.background_theory())
    m = slv.get_model_clauses(clauses)
    if m == None:
        print clauses
        if iu.version_le(iu.get_string_version(),"1.6"):
            raise iu.IvyError(None,'Initial condition and/or axioms are inconsistent')
        else:
            raise iu.IvyError(None,'Axioms are inconsistent')
    used = ilu.used_symbols_clauses(clauses)
    for sym in all_state_symbols():
        if sym.name in im.module.destructor_sorts:
            continue
        if sym in im.module.params:
            name = varname(sym)
            header.append('    this->{} = {};\n'.format(name,name))
        elif sym not in is_derived and not is_native_sym(sym):
            if sym in used:
                assign_symbol_from_model(header,sym,m)
            else:
                mk_nondet_sym(header,sym,'init',0)
#    action = ia.Sequence(*[a for n,a in im.module.initializers])
#    action.emit(header)

def emit_parameter_assignments(impl):
    for sym in im.module.params:
        name = varname(sym)
        impl.append('    this->{} = {};\n'.format(name,name))
    

def emit_constant(self,header,code):
    if self in is_derived:
        code.append(funname(self.name)+'()')
        return
    if isinstance(self,il.Symbol) and self.is_numeral():
        if is_native_sym(self):
            code.append('__lit<'+varname(self.sort)+'>(' + self.name + ')')
            return
        if self.sort.name in im.module.sort_destructors:
            raise iu.IvyError(None,"cannot compile symbol {} of sort {}".format(self.name,self.sort))
        if self.sort.name in il.sig.interp and il.sig.interp[self.sort.name].startswith('bv['):
            sname,sparms = parse_int_params(il.sig.interp[self.sort.name])
            code.append('(' + varname(self.name) + ' & ' + str((1 << sparms[0]) -1) + ')')
            return
        if self.sort in sort_to_cpptype: 
            code.append(sort_to_cpptype[self.sort].literal(self.name))
            return
    if isinstance(self,il.Symbol) and self in il.sig.constructors:
        if delegate_enums_to:
            code.append(delegate_enums_to+'::')
    code.append(varname(self.name))
    if self in is_derived:
        code.append('()')

il.Symbol.emit = emit_constant
il.Variable.emit = emit_constant

def emit_native_expr(self,header,code):
    code.append(native_expr_full(self))

ivy_ast.NativeExpr.emit = emit_native_expr

def parse_int_params(name):
    spl = name.split('[')
    name,things = spl[0],spl[1:]
#    print "things:".format(things)
    if not all(t.endswith(']') for t in things):
        raise SyntaxError()
    return name,[int(t[:-1]) for t in things]

def emit_special_op(self,op,header,code):
    if op == 'concat':
        sort_name = il.sig.interp[self.args[1].sort.name]
        sname,sparms = parse_int_params(sort_name)
        if sname == 'bv' and len(sparms) == 1:
            code.append('(')
            self.args[0].emit(header,code)
            code.append(' << {} | '.format(sparms[0]))
            self.args[1].emit(header,code)
            code.append(')')
            return
    if op.startswith('bfe['):
        opname,opparms = parse_int_params(op)
        mask = (1 << (opparms[0]-opparms[1]+1)) - 1
        code.append('(')
        self.args[0].emit(header,code)
        code.append(' >> {} & {})'.format(opparms[1],mask))
        return
    raise iu.IvyError(self,"operator {} cannot be emitted as C++".format(op))

bv_ops = {
    'bvand' : '&',
    'bvor' : '|',
    'bvnot' : '~',
}

def emit_bv_op(self,header,code):
    sname,sparms = parse_int_params(il.sig.interp[self.sort.name])
    code.append('(')
    code.append('(')
    if len(self.args) == 2:
        self.args[0].emit(header,code)
    if self.func.name.startswith('bfe['):
        fname,fparams = parse_int_params(self.func.name)
        if (len(fparams) != 2):
            iu.IvyError(None,'malformed operator: {}'.format(self.func.name))
        self.args[-1].emit(header,code)
        code.append(' >> {}) & {})'.format(fparams[0],2**(fparams[1]-fparams[0]+1)-1))
        return
    code.append(' {} '.format(bv_ops.get(self.func.name,self.func.name)))
    self.args[-1].emit(header,code)
    code.append(') & {})'.format((1 << sparms[0])-1))

def is_bv_term(self):
    return (il.is_first_order_sort(self.sort)
            and (self.sort.name in il.sig.interp
                 and il.sig.interp[self.sort.name].startswith('bv[')
                 or self.rep.name.startswith('bfe[') and ctype(self.args[0].sort) in int_ctypes))

def capture_emit(a,header,code,capture_args):
    if capture_args != None:
        tmp = []
        a.emit(header,tmp)
        code.extend(tmp)
        capture_args.append(''.join(tmp))
    else:
        a.emit(header,code)

delegate_methods_to = ''
delegate_enums_to = ''

def emit_app(self,header,code,capture_args=None):
    # handle macros
    if il.is_macro(self):
        return il.expand_macro(self).emit(header,code)
    # handle interpreted ops
    if slv.solver_name(self.func) == None:
        if self.func.name in il.sig.interp:
            op = il.sig.interp[self.func.name]
            emit_special_op(self,op,header,code)
            return
        if is_bv_term(self):
            emit_bv_op(self,header,code)
            return
        if self.func.name == '-' and il.sig.interp.get(self.func.sort.rng.name,None) == 'nat':
            x = new_temp(header,self.func.sort.rng)
            code_line(header,x + ' = ' + code_eval(header,self.args[0]))
            y = new_temp(header,self.func.sort.rng)
            code_line(header,y + ' = ' + code_eval(header,self.args[1]))
            code.append('( {} < {} ? 0 : {} - {})'.format(x,y,x,y))
            return
        assert len(self.args) == 2 # handle only binary ops for now
        code.append('(')
        self.args[0].emit(header,code)
        code.append(' {} '.format(self.func.name))
        self.args[1].emit(header,code)
        code.append(')')
        return 
    global is_derived
    # no way to deal with polymorphic ops if not derived, give up here
    if il.symbol_is_polymorphic(self.func) and self.func not in is_derived:
        raise iu.IvyError(None,"symbol has no interpretation: {}".format(il.typed_symbol(self.func)))
    # handle destructors
    skip_params = 0
    if self.func.name in im.module.destructor_sorts:
        if capture_args != None and isinstance(self.args[0],lg.Apply):
            self.args[0].emit(header,code,capture_args)
        else:
            self.args[0].emit(header,code)
        code.append('.'+memname(self.func))
        skip_params = 1
    # handle uninterpreted ops
    else:
        if self.func in is_derived:
            code.append(delegate_methods_to)
        code.append(funname(self.func.name))
    if self.func in is_derived:
        code.append('(')
        first = True
        for a in self.args:
            if not first:
                code.append(',')
            a.emit(header,code)
            first = False
        code.append(')')
    elif is_large_type(self.rep.sort) and len(self.args[skip_params:]) > 1:
        code.append('[' + ctuple(self.rep.sort.dom[skip_params:],classname=the_classname) + '(')
        first = True
        for a in self.args[skip_params:]:
            if not first:
                code.append(',')
            capture_emit(a,header,code,capture_args)
            first = False
        code.append(')]')
    else: 
        for a in self.args[skip_params:]:
            code.append('[')
            capture_emit(a,header,code,capture_args)
            code.append(']')

lg.Apply.emit = emit_app

class HavocSymbol(object):
    def __init__(self,sort,name,unique_id):
        self.sort,self.name,self.unique_id = sort,name,unique_id
        self.args = []
    def clone(self,args):
        return HavocSymbol(self.sort,self.name,self.unique_id)

def emit_havoc_symbol(self,header,code):
    sym = il.Symbol(new_temp(header,sort=self.sort),self.sort)
    mk_nondet_sym(header,sym,self.name,self.unique_id)
    code.append(sym.name)
    

HavocSymbol.emit = emit_havoc_symbol


temp_ctr = 0

def new_temp(header,sort=None):
    global temp_ctr
    name = '__tmp' + str(temp_ctr)
    temp_ctr += 1
    indent(header)
    header.append(('int' if sort == None else ctype(sort)) + ' ' + name + ';\n')
    return name


def find_definition(sym):
    for ldf in im.module.definitions:
        if ldf.formula.defines() == sym:
            return ldf
    return None

def get_bound_exprs(v0,variables,body,exists,res):
    global is_derived
    if isinstance(body,il.Not):
        return get_bound_exprs(v0,variables,body.args[0],not exists,res)
    if il.is_app(body) and body.rep.name in ['<','<=','>','>=']:
        res.append((body,not exists))
    if isinstance(body,il.Implies) and not exists:
        get_bound_exprs(v0,variables,body.args[0],not exists,res)
        get_bound_exprs(v0,variables,body.args[1],exists,res)
        return
    if isinstance(body,il.Or) and not exists:
        for arg in body.args:
            get_bound_exprs(v0,variables,arg,exists,res)
        return
    if isinstance(body,il.And) and exists:
        for arg in body.args:
            get_bound_exprs(v0,variables,arg,exists,res)
        return
    if il.is_app(body) and body.rep in is_derived and v0 in body.args:
        ldf = find_definition(body.rep)
        if ldf is None:  # happens for native definitions
            return
        if all(il.is_variable(v) for v in ldf.formula.args[0].args):
            subst = dict((v.name,a) for v,a in zip(ldf.formula.args[0].args,body.args))
            thing = ilu.substitute_ast(ldf.formula.args[1],subst)
            get_bound_exprs(v0,variables,thing,exists,res)
    
def sort_has_negative_values(sort):
    return sort.name in il.sig.interp and il.sig.interp[sort.name] == 'int'

def get_bounds(header,v0,variables,body,exists,varname=None):
    bes = []
    get_bound_exprs(v0,variables,body,exists,bes)
    los = []
    his = []
    for be in bes:
        expr,neg = be
        op = expr.rep.name
        strict = op in ['<','>']
        args = expr.args if op in ['<','<='] else [expr.args[1],expr.args[0]]
        if neg:
            strict = not strict
            args = [args[1],args[0]]
        if args[0] == v0 and args[1] != v0 and args[1] not in variables:
            e = code_eval(header,args[1])
            his.append('('+e+')+1' if not strict else e)
        if args[1] == v0 and args[0] != v0 and args[0] not in variables:
            e = code_eval(header,args[0])
            los.append('('+e+')+1' if strict else e)
    if not sort_has_negative_values(v0.sort):
        los.append("0")
    if sort_card(v0.sort) != None:
        his.append(csortcard(v0.sort))
    varname = varname if varname != None else v0
    if not los:
        raise iu.IvyError(None,'cannot find a lower bound for {}'.format(varname))
    if not his:
        if il.is_uninterpreted_sort(v0.sort) and iu.compose_names(v0.sort.name,'cardinality') in im.module.attributes:
            his.append(other_varname(iu.compose_names(v0.sort.name,im.module.attributes[iu.compose_names(v0.sort.name,'cardinality')].rep)))
        else:
            raise iu.IvyError(None,'cannot find an upper bound for {}'.format(varname))
    return los[0],his[0]

def get_all_bounds(header,variables,body,exists,varnames):
    if not variables:
        return []
    v0 = variables[0]
    variables = variables[1:]
    varname = varnames[0]
    varnames = varnames[1:]
    b = get_bounds(header,v0,variables,body,exists,varname=varname)
    return [b] + get_all_bounds(header,variables,body,exists,varnames)


def emit_quant(variables,body,header,code,exists=False):
    global indent_level
    if len(variables) == 0:
        body.emit(header,code)
        return

    if (exists and len(variables) == 1 and il.is_app(body)
        and body.func.name == '*>' and body.args[1] == variables[0]):
        vsort = body.args[0].sort
        vsortname = vsort.name
        if vsortname not in im.module.variants:
            raise iu.IvyError(None,'type {} is not a variant type but used as first argument of *>'.format(vsortname))
        variants = im.module.variants[vsortname]
        rsort = variables[0].sort
        for idx, sort in enumerate(variants):
            if sort == rsort:
                cpptype = sort_to_cpptype[vsort]
                lhs = code_eval(header,body.args[0])
                isa = cpptype.isa(idx,lhs)
                code.append(isa)
                return
        raise iu.IvyError(None,'type {} is not a variant of type {}'.format(vsortname,rsort))

    v0 = variables[0]
    variables = variables[1:]
    has_iter = il.is_uninterpreted_sort(v0.sort) and iu.compose_names(v0.sort.name,'iterable') in im.module.attributes
    if has_iter:
        iter = iu.compose_names(v0.sort.name,'iter')
    else:
        check_iterable_sort(v0.sort)
    res = new_temp(header)
    idx = v0.name
    indent(header)
    header.append(res + ' = ' + str(0 if exists else 1) + ';\n')
    indent(header)
    if has_iter:
        iter_sort_name = iter
        if iter_sort_name not in il.sig.sorts:
            iter_sort_name = iu.compose_names(iter,'t')
        if iter_sort_name not in il.sig.sorts:
            print iter_sort_name
            raise iu.IvyError(None,'sort {} has iterable attribute but no iterator'.format(v0.sort))
        iter_sort = il.sig.sorts[iter_sort_name]
        zero = []
        emit_constant(il.Symbol('0',v0.sort),header,zero)
        header.append('for (' + ctypefull(iter_sort) + ' ' + idx + ' = '
                          + varname(iu.compose_names(iter,'create') + '('))
        header.extend(zero)
        header.append('); !' + varname(iu.compose_names(iter,'is_end')) + '(' + idx + ');' 
                       + idx + '=' + varname(iu.compose_names(iter,'next')) + '(' + idx + ')) {\n')
    else:
        lo,hi = get_bounds(header,v0,variables,body,exists)
        ct = ctype(v0.sort)
        ct = 'int' if ct == 'bool' else ct if ct in int_ctypes else 'int'
        header.append('for (' + ct + ' ' + idx + ' = ' + lo + '; ' + idx + ' < ' + hi + '; ' + idx + '++) {\n')
    indent_level += 1
    subcode = []
    emit_quant(variables,body,header,subcode,exists)
    indent(header)
    header.append('if (' + ('!' if not exists else ''))
    header.extend(subcode)
    header.append(') '+ res + ' = ' + str(1 if exists else 0) + ';\n')
    indent_level -= 1
    indent(header)
    header.append('}\n')
    code.append(res)    


lg.ForAll.emit = lambda self,header,code: emit_quant(list(self.variables),self.body,header,code,False)
lg.Exists.emit = lambda self,header,code: emit_quant(list(self.variables),self.body,header,code,True)

def code_line(impl,line):
    indent(impl)
    impl.append(line+';\n')

def code_asgn(impl,lhs,rhs):
    code_line(impl,lhs + ' = ' + rhs)

def code_decl(impl,sort,name):
    code_line(impl,ctype(sort) + ' ' + name)

def code_eval(impl,expr):
    code = []
    expr.emit(impl,code)
    return ''.join(code)

def emit_some(self,header,code):
    if isinstance(self,ivy_ast.Some):
        fmla = self.fmla()
        if len(self.params()) == 1 and il.is_app(fmla) and fmla.func.name == '*>' and fmla.args[1] == self.params()[0]:
            if fmla.args[0].sort.name in im.module.variants:
                cpptype = sort_to_cpptype[fmla.args[0].sort]
                for idx,sort in enumerate(im.module.variants[fmla.args[0].sort.name]):
                    if sort == fmla.args[1].sort:
                        lhs = code_eval(header,fmla.args[0])
                        isa = cpptype.isa(idx,lhs)
                        code_line(header,'if ({}) {} = {}'.format(isa,varname(fmla.args[1].name),cpptype.downcast(idx,lhs)))
                        code.append(isa)
                        return
                code.append('false')
                return
            
        vs = [il.Variable('X__'+str(idx),p.sort) for idx,p in enumerate(self.params())]
        subst = dict(zip(self.params(),vs))
        fmla = ilu.substitute_constants_ast(self.fmla(),subst)
        params = self.params()
    else:
        vs = self.params()
        params = [new_temp(header)]
        code_line(header,params[0] + ' = ___ivy_choose(' + csortcard(vs[0].sort) + ',"' + str(vs[0]) + '",0)')
        fmla = self.fmla()
    for v in vs:
        check_iterable_sort(v.sort)
    some = new_temp(header)
    code_asgn(header,some,'0')
    if isinstance(self,ivy_ast.SomeMinMax):
        minmax = new_temp(header)
    open_loop(header,vs,bounds=get_all_bounds(header,vs,fmla,True,self.params()))
    open_if(header,code_eval(header,fmla))
    if isinstance(self,ivy_ast.SomeMinMax):
        index = new_temp(header)
        idxfmla =  ilu.substitute_constants_ast(self.index(),subst)
        code_asgn(header,index,code_eval(header,idxfmla))
        open_if(header,some)
        sort = self.index().sort
        op = il.Symbol('<',il.RelationSort([sort,sort]))
        idx = il.Symbol(index,sort)
        mm = il.Symbol(minmax,sort)
        pred = op(idx,mm) if isinstance(self,ivy_ast.SomeMin) else op(mm,idx)
        open_if(header,code_eval(header,il.Not(pred)))
        code_line(header,'continue')
        close_scope(header)
        close_scope(header)
        code_asgn(header,minmax,index)
    for p,v in zip(params,vs):
        code_asgn(header,varname(p),varname(v))
    code_line(header,some+'= 1')
    # optimization: if minimizing first params, first hit is minimum, so exit loop
    # this is particularly helpful when searching a big type like int!
    if isinstance(self,ivy_ast.SomeMinMax) and self.params()[0] == self.index():
        code_line(header,'break')
    close_scope(header)
    close_loop(header,vs)
    if isinstance(self,ivy_ast.Some):
        code.append(some)
       
    else:
        iv = self.if_value()
        if iv == None:
            code.append(varname(params[0]))
        else:
            thing = il.Symbol(params[0],vs[0].sort)
            ot = ilu.substitute_ast(iv,{vs[0].name:thing})
            code.append('(' + some + ' ? (' + code_eval(header,ot) + ') : ('
                        + code_eval(header,self.else_value()) + '))')
            

ivy_ast.Some.emit = emit_some

il.Some.emit = emit_some

def emit_unop(self,header,code,op):
    code.append(op)
    self.args[0].emit(header,code)

lg.Not.emit = lambda self,header,code: emit_unop(self,header,code,'!')

def emit_binop(self,header,code,op,ident=None):
    if len(self.args) == 0:
        assert ident != None
        code.append(ident)
        return
    code.append('(')
    self.args[0].emit(header,code)
    for a in self.args[1:]:
        code.append(' ' + op + ' ')
        a.emit(header,code)
    code.append(')')
    
def emit_implies(self,header,code):
    code.append('(')
    code.append('!')
    self.args[0].emit(header,code)
    code.append(' || ')
    self.args[1].emit(header,code)
    code.append(')')
    

lg.Eq.emit = lambda self,header,code: emit_binop(self,header,code,'==')
lg.Iff.emit = lambda self,header,code: emit_binop(self,header,code,'==')
lg.Implies.emit = emit_implies
lg.And.emit = lambda self,header,code: emit_binop(self,header,code,'&&','true')
lg.Or.emit = lambda self,header,code: emit_binop(self,header,code,'||','false')

def emit_ternop(self,header,code):
    code.append('(')
    self.args[0].emit(header,code)
    code.append(' ? ')
    self.args[1].emit(header,code)
    code.append(' : ')
    self.args[2].emit(header,code)
    code.append(')')
    
lg.Ite.emit = emit_ternop

def emit_traced_lhs(self,trace,captured_args):
    trace.append('<< "{}"'.format(self.rep))
    if il.is_constant(self):
        return
    if self.args:
        trace.append(' << "("')
    num_args = len(self.args)
    if self.func.name in im.module.destructor_sorts:
        captured_args = emit_traced_lhs(self.args[0],trace,captured_args)
        if num_args > 1:
            trace.append(' << ","')
        num_args -= 1
    if captured_args is None:
        captured_args = []
    trace.append(' << ","'.join(' << ' + a for a in captured_args[:num_args]))
    if self.args:
        trace.append(' << ")"')
    return captured_args[num_args:]

def emit_assign_simple(self,header):
    code = []
    indent(code)
    if opt_trace.get() and ':' not in self.args[0].rep.name:
        trace = []
        indent(trace)
        trace.append('__ivy_out ' + number_format + ' << "  write("')
        cargs = []
        if il.is_constant(self.args[0]):
            self.args[0].emit(header,code)
        else:
            emit_app(self.args[0],header,code,cargs)
        emit_traced_lhs(self.args[0],trace,cargs)
        code.append(' = ')
        rhs = []
        self.args[1].emit(header,rhs)
        code.extend(rhs)
        trace.extend(' << "," << (' + ''.join(rhs) + ') << ")" << std::endl;\n')
        header.extend(trace)
    else:
        self.args[0].emit(header,code)
        code.append(' = ')
        lsort,rsort = [a.sort for a in self.args]
        if im.module.is_variant(lsort,rsort):
            code.append(sort_to_cpptype[lsort].upcast(im.module.variant_index(lsort,rsort),code_eval(header,self.args[1])))
        else:
            self.args[1].emit(header,code)
    code.append(';\n')    
    header.extend(code)

def emit_assign_large(self,header):
    dom = self.args[0].rep.sort.dom
    vs = variables(dom)
    vs = [x if isinstance(x,il.Variable) else y for x,y in zip(self.args[0].args,vs)]
    eqs = [il.Equals(x,y) for x,y in zip(self.args[0].args,vs) if not isinstance(x,il.Variable)]
    expr = il.Ite(il.And(*eqs),self.args[1],self.args[0].rep(*vs)) if eqs else self.args[1]
    global thunks

    code_line(header,varname(self.args[0].rep)+' = ' + make_thunk(thunks,vs,expr))

def emit_assign(self,header):
    global indent_level
    with ivy_ast.ASTContext(self):
#        if is_large_type(self.args[0].rep.sort) and lu.free_variables(self.args[0]):
        if is_large_lhs(self.args[0]):
            emit_assign_large(self,header)
            return
        vs = list(lu.free_variables(self.args[0]))
        for v in vs:
            check_iterable_sort(v.sort)
        if len(vs) == 0:
            emit_assign_simple(self,header)
            return
        global temp_ctr
        tmp = '__tmp' + str(temp_ctr)
        temp_ctr += 1
        indent(header)
        header.append(ctype(self.args[1].sort) + '  ' + tmp)
        for v in vs:
            header.append('[' + str(sort_card(v.sort)) + ']')
        header.append(';\n')
        for idx in vs:
            indent(header)
            vn = varname(idx.name)
            header.append('for (int ' + vn + ' = 0; ' + vn + ' < ' + str(sort_card(idx.sort)) + '; ' + vn + '++) {\n')
            indent_level += 1
        code = []
        indent(code)
        code.append(tmp + ''.join('['+varname(v.name)+']' for v in vs) + ' = ')
        self.args[1].emit(header,code)
        code.append(';\n')    
        header.extend(code)
        for idx in vs:
            indent_level -= 1
            indent(header)
            header.append('}\n')
        for idx in vs:
            indent(header)
            vn = varname(idx.name)
            header.append('for (int ' + vn + ' = 0; ' + vn + ' < ' + str(sort_card(idx.sort)) + '; ' + vn + '++) {\n')
            indent_level += 1
        code = []
        indent(code)
        self.args[0].emit(header,code)
        code.append(' = ' + tmp + ''.join('['+varname(v.name)+']' for v in vs) + ';\n')
        header.extend(code)
        for idx in vs:
            indent_level -= 1
            indent(header)
            header.append('}\n')
    
ia.AssignAction.emit = emit_assign

def emit_havoc(self,header):
    print self
    print self.lineno
    assert False

ia.HavocAction.emit = emit_havoc

def emit_sequence(self,header):
    global indent_level
    indent(header)
    header.append('{\n')
    indent_level += 1
    for a in self.args:
        a.emit(header)
    indent_level -= 1 
    indent(header)
    header.append('}\n')

ia.Sequence.emit = emit_sequence

def emit_assert(self,header):
    code = []
    indent(code)
    code.append('ivy_assert(')
    with ivy_ast.ASTContext(self):
        il.close_formula(self.args[0]).emit(header,code)
    code.append(', "{}");\n'.format(iu.lineno_str(self).replace('\\','\\\\')))
    header.extend(code)

ia.AssertAction.emit = emit_assert

def emit_assume(self,header):
    code = []
    indent(code)
    code.append('ivy_assume(')
    with ivy_ast.ASTContext(self):
        il.close_formula(self.args[0]).emit(header,code)
    code.append(', "{}");\n'.format(iu.lineno_str(self).replace('\\','\\\\')))
    header.extend(code)

ia.AssumeAction.emit = emit_assume


def emit_call(self,header):
    # tricky: a call can have variables on the lhs. we lower this to
    # a call with temporary return actual followed by assignment 
    if len(self.args) == 2 and list(ilu.variables_ast(self.args[1])):
        sort = self.args[1].sort
        sym = il.Symbol(new_temp(header,sort=sort),sort)
        emit_call(self.clone([self.args[0],sym]),header)
        ac = ia.AssignAction(self.args[1],sym)
        if hasattr(self,'lineno'):
            ac.lineno = self.lineno
        emit_assign(ac,header)
        return
    if target.get() in ["gen","test"]:
        indent(header)
        header.append('___ivy_stack.push_back(' + str(self.unique_id) + ');\n')
    code = []
    indent(code)
    retvals = []
    args = list(self.args[0].args)
    nargs = len(args)
    name = self.args[0].rep
    action = im.module.actions[name]
    fmls = list(action.formal_params)
    if len(self.args) >= 2:
        pt,rt = get_param_types(name,action)
        for rpos in range(len(rt)):
            rv = self.args[1 + rpos]
            pos = rt[rpos].pos if isinstance(rt[rpos],ReturnRefType) else None
            if pos is not None:
                if pos < nargs:
                    iparg = self.args[0].args[pos]
                    if (iparg != rv or
                        any(j != pos and may_alias(arg,iparg) for j,arg in enumerate(self.args[0].args))):
                        retval = new_temp(header,rv.sort)
                        code.append(retval + ' = ')
                        self.args[0].args[pos].emit(header,code)
                        code.append('; ')
                        retvals.append((rv,retval))
                        args = [il.Symbol(retval,self.args[1].sort) if idx == pos else a for idx,a in enumerate(args)]
                else:
                    args.append(self.args[1+rpos])
                    fmls.append(rv)
        if not isinstance(rt[0],ReturnRefType):
            self.args[1].emit(header,code)
            code.append(' = ')
    code.append(varname(str(self.args[0].rep)) + '(')
    first = True
    for p,fml in zip(args,fmls):
        if not first:
            code.append(', ')
        lsort,rsort = fml.sort,p.sort
        if im.module.is_variant(lsort,rsort):
            code.append(sort_to_cpptype[lsort].upcast(im.module.variant_index(lsort,rsort),code_eval(header,p)))
        else:
            p.emit(header,code)
        first = False
    code.append(');\n')    
    for (rv,retval) in retvals:
        indent(code) 
        rv.emit(header,code)
        code.append(' = ' + retval + ';\n')
    header.extend(code)
    if target.get() in ["gen","test"]:
        indent(header)
        header.append('___ivy_stack.pop_back();\n')

ia.CallAction.emit = emit_call

def emit_crash(self,header):
    pass

ia.CrashAction.emit = emit_crash

def local_start(header,params,nondet_id=None):
    global indent_level
    indent(header)
    header.append('{\n')
    indent_level += 1
    for p in params:
        indent(header)
        header.append(ctype(p.sort) + ' ' + varname(p.name) + ';\n')
        if nondet_id != None:
            mk_nondet_sym(header,p,p.name,nondet_id)

def local_end(header):
    global indent_level
    indent_level -= 1
    indent(header)
    header.append('}\n')


def emit_local(self,header):
    local_start(header,self.args[0:-1],self.unique_id)
    self.args[-1].emit(header)
    local_end(header)

ia.LocalAction.emit = emit_local

def emit_if(self,header):
    global indent_level
    code = []
    if isinstance(self.args[0],ivy_ast.Some):
        local_start(header,self.args[0].params())
    indent(code)
    code.append('if(');
    self.args[0].emit(header,code)
    header.extend(code)
    header.append('){\n')
    indent_level += 1
    self.args[1].emit(header)
    indent_level -= 1
    indent(header)
    header.append('}\n')
    if len(self.args) == 3:
        indent(header)
        header.append('else {\n')
        indent_level += 1
        self.args[2].emit(header)
        indent_level -= 1
        indent(header)
        header.append('}\n')
    if isinstance(self.args[0],ivy_ast.Some):
        local_end(header)


ia.IfAction.emit = emit_if

def emit_while(self,header):
    global indent_level
    code = []
    if isinstance(self.args[0],ivy_ast.Some):
        local_start(header,self.args[0].params())

    cond = code_eval(code,self.args[0])
    if len(code) == 0:
        open_scope(header,line='while('+cond+')')
        self.args[1].emit(header)
        close_scope(header)
    else:
        open_scope(header,line='while(true)')
        header.extend(code);
        open_scope(header,line='if('+cond+')')
        self.args[1].emit(header)
        close_scope(header)
        open_scope(header,line='else')
        code_line(header,'break')
        close_scope(header)
        close_scope(header)
    if isinstance(self.args[0],ivy_ast.Some):
        local_end(header)
        


ia.WhileAction.emit = emit_while

def emit_choice(self,header):
    global indent_level
    if len(self.args) == 1:
        self.args[0].emit(header)
        return
    tmp = new_temp(header)
    mk_nondet(header,tmp,len(self.args),"___branch",self.unique_id)
    for idx,arg in enumerate(self.args):
        indent(header)
        if idx != 0:
            header.append('else ')
        if idx != len(self.args)-1:
            header.append('if(' + tmp + ' == ' + str(idx) + ')');
        header.append('{\n')
        indent_level += 1
        arg.emit(header)
        indent_level -= 1
        indent(header)
        header.append('}\n')

ia.ChoiceAction.emit = emit_choice

native_classname = None


def native_reference(atom):
    if isinstance(atom,ivy_ast.Atom) and atom.rep in im.module.actions:
        res = thunk_name(atom.rep) + '(this'
        res += ''.join(', ' + varname(arg.rep) for arg in atom.args) + ')'
        return res
    if atom.rep in im.module.sig.sorts:
        res = ctype(im.module.sig.sorts[atom.rep],classname=native_classname)
#        print 'type(atom): {} atom.rep: {} res: {}'.format(type(atom),atom.rep,res)
        return res
    res = varname(atom.rep)
    for arg in atom.args:
        n = arg.name if hasattr(arg,'name') else arg.rep
        res += '[' + varname(n) + ']'
    return res


def emit_native_action(self,header):
    fields = self.args[0].code.split('`')
    def nfun(idx):
        return native_typeof if fields[idx-1].endswith('%') else native_z3name if fields[idx-1].endswith('"') else native_reference
    def dm(s):
        return s[:-1] if s.endswith('%') else s
    fields = [(nfun(idx)(self.args[int(s)+1]) if idx % 2 == 1 else dm(s)) for idx,s in enumerate(fields)]
    indent_code(header,''.join(fields))

ia.NativeAction.emit = emit_native_action

def emit_repl_imports(header,impl,classname):
    pass

def emit_repl_boilerplate1(header,impl,classname):
    impl.append("""

int ask_ret(long long bound) {
    int res;
    while(true) {
        __ivy_out << "? ";
        std::cin >> res;
        if (res >= 0 && res < bound) 
            return res;
        std::cerr << "value out of range" << std::endl;
    }
}

""")

    impl.append("""

    class classname_repl : public classname {

    public:

    virtual void ivy_assert(bool truth,const char *msg){
        if (!truth) {
            __ivy_out << "assertion_failed(\\"" << msg << "\\")" << std::endl;
            std::cerr << msg << ": error: assertion failed\\n";
            CLOSE_TRACE
            __ivy_exit(1);
        }
    }
    virtual void ivy_assume(bool truth,const char *msg){
        if (!truth) {
            __ivy_out << "assumption_failed(\\"" << msg << "\\")" << std::endl;
            std::cerr << msg << ": error: assumption failed\\n";
            CLOSE_TRACE
            __ivy_exit(1);
        }
    }
    """.replace('classname',classname).replace('CLOSE_TRACE','__ivy_out << "}" << std::endl;' if opt_trace.get() else ''))

    emit_param_decls(impl,classname+'_repl',im.module.params)
    impl.append(' : '+classname+'('+','.join(map(varname,im.module.params))+'){}\n')
    
    for imp in im.module.imports:
        name = imp.imported()
        if not imp.scope() and name in im.module.actions:
            action = im.module.actions[name]
            emit_method_decl(impl,name,action);
            if target.get() == "test":
                impl.append("{}\n")
                continue
            impl.append('{\n    __ivy_out ' + number_format + ' << "< ' + name[5:] + '"')
            if action.formal_params:
                impl.append(' << "("')
                first = True
                for arg in action.formal_params:
                    if not first:
                        impl.append(' << ","')
                    first = False
                    impl.append(' << {}'.format(varname(arg.rep.name)))
                impl.append(' << ")"')
            impl.append(' << std::endl;\n')
            if action.formal_returns:
                impl.append('    return ask_ret(__CARD__{});\n'.format(action.formal_returns[0].sort))
            impl.append('}\n')

    

    impl.append("""
    };
""")

    impl.append("""
// Override methods to implement low-level network service

bool is_white(int c) {
    return (c == ' ' || c == '\\t' || c == '\\n' || c == '\\r');
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
    int pos;
    syntax_error(int pos) : pos(pos) {}
};

void throw_syntax(int pos){
    throw syntax_error(pos);
}

std::string get_ident(const std::string& str, int &pos) {
    std::string res = "";
    while (pos < str.size() && is_ident(str[pos])) {
        res.push_back(str[pos]);
        pos++;
    }
    if (res.size() == 0)
        throw_syntax(pos);
    return res;
}

ivy_value parse_value(const std::string& cmd, int &pos) {
    ivy_value res;
    res.pos = pos;
    skip_white(cmd,pos);
    if (pos < cmd.size() && cmd[pos] == '[') {
        while (true) {
            pos++;
            skip_white(cmd,pos);
            if (pos < cmd.size() && cmd[pos] == ']')
                break;
            res.fields.push_back(parse_value(cmd,pos));
            skip_white(cmd,pos);
            if (pos < cmd.size() && cmd[pos] == ']')
                break;
            if (!(pos < cmd.size() && cmd[pos] == ','))
                throw_syntax(pos);
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
                 throw_syntax(pos);
            pos++;
            skip_white(cmd,pos);
            field.fields.push_back(parse_value(cmd,pos));
            res.fields.push_back(field);
            skip_white(cmd,pos);
            if (pos < cmd.size() && cmd[pos] == '}')
                break;
            if (!(pos < cmd.size() && cmd[pos] == ','))
                throw_syntax(pos);
        }
        pos++;
    }
    else if (pos < cmd.size() && cmd[pos] == '"') {
        pos++;
        res.atom = "";
        while (pos < cmd.size() && cmd[pos] != '"') {
            char c = cmd[pos++];
            if (c == '\\\\') {
                if (pos == cmd.size())
                    throw_syntax(pos);
                c = cmd[pos++];
                c = (c == 'n') ? 10 : (c == 'r') ? 13 : (c == 't') ? 9 : c;
            }
            res.atom.push_back(c);
        }
        if(pos == cmd.size())
            throw_syntax(pos);
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
            throw_syntax(pos);
        pos++;
    }
    skip_white(cmd,pos);
    if (pos != cmd.size())
        throw_syntax(pos);
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

""".replace('classname',classname))


def emit_repl_boilerplate1a(header,impl,classname):
    impl.append("""

class stdin_reader: public reader {
    std::string buf;
    std::string eof_flag;

public:
    bool eof(){
      return eof_flag.size();
    }
    virtual int fdes(){
        return 0;
    }
    virtual void read() {
        char tmp[257];
        int chars = ::read(0,tmp,256);
        if (chars == 0) {  // EOF
            if (buf.size())
                process(buf);
            eof_flag = "eof";
        }
        tmp[chars] = 0;
        buf += std::string(tmp);
        size_t pos;
        while ((pos = buf.find('\\n')) != std::string::npos) {
            std::string line = buf.substr(0,pos+1);
            buf.erase(0,pos+1);
            process(line);
        }
    }
    virtual void process(const std::string &line) {
        __ivy_out << line;
    }
};

class cmd_reader: public stdin_reader {
    int lineno;
public:
    classname_repl &ivy;    

    cmd_reader(classname_repl &_ivy) : ivy(_ivy) {
        lineno = 1;
        if (isatty(fdes()))
            __ivy_out << "> "; __ivy_out.flush();
    }

    virtual void process(const std::string &cmd) {
        std::string action;
        std::vector<ivy_value> args;
        try {
            parse_command(cmd,action,args);
            ivy.__lock();
""".replace('classname',classname))


def emit_repl_boilerplate2(header,impl,classname):
    impl.append("""
            {
                std::cerr << "undefined action: " << action << std::endl;
            }
            ivy.__unlock();
        }
        catch (syntax_error& err) {
            ivy.__unlock();
            std::cerr << "line " << lineno << ":" << err.pos << ": syntax error" << std::endl;
        }
        catch (out_of_bounds &err) {
            ivy.__unlock();
            std::cerr << "line " << lineno << ":" << err.pos << ": " << err.txt << " bad value" << std::endl;
        }
        catch (bad_arity &err) {
            ivy.__unlock();
            std::cerr << "action " << err.action << " takes " << err.num  << " input parameters" << std::endl;
        }
        if (isatty(fdes()))
            __ivy_out << "> "; __ivy_out.flush();
        lineno++;
    }
};



""".replace('classname',classname))

def emit_winsock_init(impl):
    impl.append("""
#ifdef _WIN32
    // Boilerplate from windows docs

    {
        WORD wVersionRequested;
        WSADATA wsaData;
        int err;

    /* Use the MAKEWORD(lowbyte, highbyte) macro declared in Windef.h */
        wVersionRequested = MAKEWORD(2, 2);

        err = WSAStartup(wVersionRequested, &wsaData);
        if (err != 0) {
            /* Tell the user that we could not find a usable */
            /* Winsock DLL.                                  */
            printf("WSAStartup failed with error: %d\\n", err);
            return 1;
        }

    /* Confirm that the WinSock DLL supports 2.2.*/
    /* Note that if the DLL supports versions greater    */
    /* than 2.2 in addition to 2.2, it will still return */
    /* 2.2 in wVersion since that is the version we      */
    /* requested.                                        */

        if (LOBYTE(wsaData.wVersion) != 2 || HIBYTE(wsaData.wVersion) != 2) {
            /* Tell the user that we could not find a usable */
            /* WinSock DLL.                                  */
            printf("Could not find a usable version of Winsock.dll\\n");
            WSACleanup();
            return 1;
        }
    }
#endif
""")


def emit_repl_boilerplate3(header,impl,classname):
    impl.append("""

    ivy.__unlock();

    cmd_reader *cr = new cmd_reader(ivy);

    // The main thread runs the console reader

    while (!cr->eof())
        cr->read();
    return 0;

""".replace('classname',classname))

def emit_repl_boilerplate3server(header,impl,classname):
    impl.append("""

    
    ivy.__unlock();

    // The main thread waits for all reader threads to die

    for(unsigned i = 0; true ; i++) {
        ivy.__lock();
        if (i >= ivy.thread_ids.size()){
            ivy.__unlock();
            break;
        }
        pthread_t tid = ivy.thread_ids[i];
        ivy.__unlock();
        pthread_join(tid,NULL);
    }
    return 0;

""".replace('classname',classname))

def emit_repl_boilerplate3test(header,impl,classname):
    impl.append("""
        ivy.__unlock();
        initializing = false;
        for(int rdridx = 0; rdridx < readers.size(); rdridx++) {
            readers[rdridx]->bind();
        }
                    
        init_gen my_init_gen;
        my_init_gen.generate(ivy);
        std::vector<gen *> generators;
        std::vector<double> weights;

""")
    totalweight = 0.0
    num_public_actions = 0
    for actname in sorted(im.module.public_actions):
        if actname == 'ext:_finalize':
            continue
        num_public_actions += 1
        action = im.module.actions[actname]
        impl.append("        generators.push_back(new {}_gen);\n".format(varname(actname)))
        aname = (actname[4:] if actname.startswith('ext:') else actname) +'.weight'
        if aname in im.module.attributes:
            astring = im.module.attributes[aname].rep
            if astring.startswith('"'):
                astring = astring[1:-1]
            try:
                aval = float(astring)
            except ValueError:
                raise iu.IvyError(None,'bad weight attribute for action{}: {}'.format(actname,astring))
        else:
            aval = 1.0
        impl.append("        weights.push_back({});\n".format(aval))
        totalweight += aval
    impl.append("        double totalweight = {};\n".format(totalweight))
    impl.append("        int num_gens = {};\n".format(num_public_actions))
            
    final_code = 'ivy.__lock(); ivy.ext___finalize(); ivy.__unlock();' if 'ext:_finalize' in im.module.public_actions else ''
    
    impl.append("""

#ifdef _WIN32
    LARGE_INTEGER freq;
    QueryPerformanceFrequency(&freq);
#endif
    for(int cycle = 0; cycle < test_iters; cycle++) {

        int choices = num_gens + readers.size() + timers.size();
        int rnd = choices ? (rand() % choices) : 0;
        if (rnd < num_gens) {
            double frnd = totalweight * (((double)rand())/(((double)RAND_MAX)+1.0));
            int idx = 0;
            double sum = 0.0;
            while (idx < num_gens-1) {
                sum += weights[idx];
                if (frnd < sum)
                    break;
                idx++;
            }
            gen &g = *generators[idx];
            ivy.__lock();
#ifdef _WIN32
            LARGE_INTEGER before;
            QueryPerformanceCounter(&before);
#endif
            ivy._generating = true;
            bool sat = g.generate(ivy);
#ifdef _WIN32
            LARGE_INTEGER after;
            QueryPerformanceCounter(&after);
//            __ivy_out << "idx: " << idx << " sat: " << sat << " time: " << (((double)(after.QuadPart-before.QuadPart))/freq.QuadPart) << std::endl;
#endif
            if (sat){
                g.execute(ivy);
                ivy._generating = false;
                ivy.__unlock();
#ifdef _WIN32
                Sleep(sleep_ms);
#endif
            }
            else {
                ivy._generating = false;
                ivy.__unlock();
                cycle--;
            }
            continue;
        }


        fd_set rdfds;
        FD_ZERO(&rdfds);
        int maxfds = 0;

        for (unsigned i = 0; i < readers.size(); i++) {
            reader *r = readers[i];
            int fds = r->fdes();
            if (fds >= 0) {
                FD_SET(fds,&rdfds);
            }
            if (fds > maxfds)
                maxfds = fds;
        }

#ifdef _WIN32
        int timer_min = 15;
#else
        int timer_min = 1;
#endif

        struct timeval timeout;
        timeout.tv_sec = timer_min/1000;
        timeout.tv_usec = 1000 * (timer_min % 1000);

#ifdef _WIN32
        int foo;
        if (readers.size() == 0){  // winsock can't handle empty fdset!
            Sleep(timer_min);
            foo = 0;
        }
        else
            foo = select(maxfds+1,&rdfds,0,0,&timeout);
#else
        int foo = select(maxfds+1,&rdfds,0,0,&timeout);
#endif

        if (foo < 0)
#ifdef _WIN32
            {std::cerr << "select failed: " << WSAGetLastError() << std::endl; __ivy_exit(1);}
#else
            {perror("select failed"); __ivy_exit(1);}
#endif
        
        if (foo == 0){
            // std::cout << "TIMEOUT\\n";            
           cycle--;
           for (unsigned i = 0; i < timers.size(); i++){
               if (timer_min >= timers[i]->ms_delay()) {
                   cycle++;
                   break;
               }
           }
           for (unsigned i = 0; i < timers.size(); i++)
               timers[i]->timeout(timer_min);
        }
        else {
            for (unsigned i = 0; i < readers.size(); i++) {
                reader *r = readers[i];
                if (FD_ISSET(r->fdes(),&rdfds))
                    r->read();
            }
        }            
    }
    FINALIZE
#ifdef _WIN32
                Sleep(final_ms);  // HACK: wait for late responses
#endif
    __ivy_out << "test_completed" << std::endl;
    for (unsigned i = 0; i < readers.size(); i++)
        delete readers[i];
    readers.clear();
    for (unsigned i = 0; i < timers.size(); i++)
        delete timers[i];
    timers.clear();


""".replace('classname',classname).replace('FINALIZE',final_code))

def emit_boilerplate1(header,impl,classname):
    header.append("""
#include <string>
#include <vector>
#include <sstream>
#include <cstdlib>
""")
    header.append("""

using namespace hash_space;

class gen : public ivy_gen {

public:
    z3::context ctx;
    z3::solver slvr;
    z3::model model;

protected:
    gen(): slvr(ctx), model(ctx,(Z3_model)0) {}

    hash_map<std::string, z3::sort> enum_sorts;
    hash_map<Z3_sort, z3::func_decl_vector> enum_values;
    hash_map<std::string, z3::func_decl> decls_by_name;
    hash_map<Z3_symbol,int> enum_to_int;
    std::vector<Z3_symbol> sort_names;
    std::vector<Z3_sort> sorts;
    std::vector<Z3_symbol> decl_names;
    std::vector<Z3_func_decl> decls;
    std::vector<z3::expr> alits;


public:
    virtual bool generate(classname& obj)=0;
    virtual void execute(classname& obj)=0;
    virtual ~gen(){}

    z3::expr mk_apply_expr(const char *decl_name, unsigned num_args, const int *args){
        z3::func_decl decl = decls_by_name.find(decl_name)->second;
        std::vector<z3::expr> expr_args;
        unsigned arity = decl.arity();
        assert(arity == num_args);
        for(unsigned i = 0; i < arity; i ++) {
            z3::sort sort = decl.domain(i);
            expr_args.push_back(int_to_z3(sort,args[i]));
        }
        return decl(arity,&expr_args[0]);
    }

    int eval(const z3::expr &apply_expr) {
        try {
            z3::expr foo = model.eval(apply_expr,true);
            // std::cout << apply_expr << " = " << foo << std::endl;
            if (foo.is_int()) {
                assert(foo.is_numeral());
                int v;
                if (Z3_get_numeral_int(ctx,foo,&v) != Z3_TRUE) {
                    std::cerr << "integer value from Z3 too large for machine int: " << foo << std::endl;
                    assert(false);
                }
                return v;
            }
            if (foo.is_bv()) {
                assert(foo.is_numeral());
                unsigned v;
                if (Z3_get_numeral_uint(ctx,foo,&v) != Z3_TRUE) {
                    std::cerr << "bit vector value from Z3 too large for machine int: " << foo << std::endl;
                    assert(false);
                }
                return v;
            }
            assert(foo.is_app());
            if (foo.is_bool())
                return (foo.decl().decl_kind() == Z3_OP_TRUE) ? 1 : 0;
            return enum_to_int[foo.decl().name()];
        }
        catch (const z3::exception &e) {
            std::cerr << e << std::endl;
            throw e;
        }
    }

    __strlit eval_string(const z3::expr &apply_expr) {
        try {
            z3::expr foo = model.eval(apply_expr,true);
            assert(Z3_is_string(ctx,foo));
            return Z3_get_string(ctx,foo);
        }
        catch (const z3::exception &e) {
            std::cerr << e << std::endl;
            throw e;
        }
    }

    int eval_apply(const char *decl_name, unsigned num_args, const int *args) {
        z3::expr apply_expr = mk_apply_expr(decl_name,num_args,args);
        //        std::cout << "apply_expr: " << apply_expr << std::endl;
        try {
            z3::expr foo = model.eval(apply_expr,true);
            if (foo.is_bv() || foo.is_int()) {
                assert(foo.is_numeral());
                unsigned v;
                if (Z3_get_numeral_uint(ctx,foo,&v) != Z3_TRUE)
                    assert(false && "bit vector value too large for machine int");
                return v;
            }
            assert(foo.is_app());
            if (foo.is_bool())
                return (foo.decl().decl_kind() == Z3_OP_TRUE) ? 1 : 0;
            return enum_to_int[foo.decl().name()];
        }
        catch (const z3::exception &e) {
            std::cerr << e << std::endl;
            throw e;
        }
    }

    int eval_apply(const char *decl_name) {
        return eval_apply(decl_name,0,(int *)0);
    }

    int eval_apply(const char *decl_name, int arg0) {
        return eval_apply(decl_name,1,&arg0);
    }
    
    int eval_apply(const char *decl_name, int arg0, int arg1) {
        int args[2] = {arg0,arg1};
        return eval_apply(decl_name,2,args);
    }

    int eval_apply(const char *decl_name, int arg0, int arg1, int arg2) {
        int args[3] = {arg0,arg1,arg2};
        return eval_apply(decl_name,3,args);
    }

    z3::expr apply(const char *decl_name, std::vector<z3::expr> &expr_args) {
        z3::func_decl decl = decls_by_name.find(decl_name)->second;
        unsigned arity = decl.arity();
        assert(arity == expr_args.size());
        return decl(arity,&expr_args[0]);
    }

    z3::expr apply(const char *decl_name) {
        std::vector<z3::expr> a;
        return apply(decl_name,a);
    }

    z3::expr apply(const char *decl_name, z3::expr arg0) {
        std::vector<z3::expr> a;
        a.push_back(arg0);
        return apply(decl_name,a);
    }
    
    z3::expr apply(const char *decl_name, z3::expr arg0, z3::expr arg1) {
        std::vector<z3::expr> a;
        a.push_back(arg0);
        a.push_back(arg1);
        return apply(decl_name,a);
    }
    
    z3::expr apply(const char *decl_name, z3::expr arg0, z3::expr arg1, z3::expr arg2) {
        std::vector<z3::expr> a;
        a.push_back(arg0);
        a.push_back(arg1);
        a.push_back(arg2);
        return apply(decl_name,a);
    }

    z3::expr apply(const char *decl_name, z3::expr arg0, z3::expr arg1, z3::expr arg2, z3::expr arg3) {
        std::vector<z3::expr> a;
        a.push_back(arg0);
        a.push_back(arg1);
        a.push_back(arg2);
        a.push_back(arg3);
        return apply(decl_name,a);
    }

    z3::expr int_to_z3(const z3::sort &range, int64_t value) {
        if (range.is_bool())
            return ctx.bool_val((bool)value);
        if (range.is_bv())
            return ctx.bv_val((int)value,range.bv_size());
        if (range.is_int())
            return ctx.int_val((int)value);
        return enum_values.find(range)->second[(int)value]();
    }

    z3::expr int_to_z3(const z3::sort &range, const std::string& value) {
        return ctx.string_val(value);
    }

    unsigned sort_card(const z3::sort &range) {
        if (range.is_bool())
            return 2;
        if (range.is_bv())
            return 1 << range.bv_size();
        if (range.is_int())
            return 1;  // bogus -- we need a good way to randomize ints
        return enum_values.find(range)->second.size();
    }

    int set(const char *decl_name, unsigned num_args, const int *args, int value) {
        z3::func_decl decl = decls_by_name.find(decl_name)->second;
        std::vector<z3::expr> expr_args;
        unsigned arity = decl.arity();
        assert(arity == num_args);
        for(unsigned i = 0; i < arity; i ++) {
            z3::sort sort = decl.domain(i);
            expr_args.push_back(int_to_z3(sort,args[i]));
        }
        z3::expr apply_expr = decl(arity,&expr_args[0]);
        z3::sort range = decl.range();
        z3::expr val_expr = int_to_z3(range,value);
        z3::expr pred = apply_expr == val_expr;
        //        std::cout << "pred: " << pred << std::endl;
        slvr.add(pred);
    }

    int set(const char *decl_name, int value) {
        return set(decl_name,0,(int *)0,value);
    }

    int set(const char *decl_name, int arg0, int value) {
        return set(decl_name,1,&arg0,value);
    }
    
    int set(const char *decl_name, int arg0, int arg1, int value) {
        int args[2] = {arg0,arg1};
        return set(decl_name,2,args,value);
    }

    int set(const char *decl_name, int arg0, int arg1, int arg2, int value) {
        int args[3] = {arg0,arg1,arg2};
        return set(decl_name,3,args,value);
    }

    void add_alit(const z3::expr &pred){
        // std::cout << "pred: " << pred << std::endl;
        std::ostringstream ss;
        ss << "alit:" << alits.size();
        z3::expr alit = ctx.bool_const(ss.str().c_str());
        // std::cout << "alit: " << alit << std::endl;
        alits.push_back(alit);
        slvr.add(!alit || pred);
    }

    void randomize(const z3::expr &apply_expr) {
        z3::sort range = apply_expr.get_sort();
//        std::cout << apply_expr << " : " << range << std::endl;
        unsigned card = sort_card(range);
        int value = rand() % card;
        z3::expr val_expr = int_to_z3(range,value);
        z3::expr pred = apply_expr == val_expr;
        add_alit(pred);
    }

    void randomize(const char *decl_name, unsigned num_args, const int *args) {
        z3::func_decl decl = decls_by_name.find(decl_name)->second;
        z3::expr apply_expr = mk_apply_expr(decl_name,num_args,args);
        z3::sort range = decl.range();
        unsigned card = sort_card(range);
        int value = rand() % card;
        z3::expr val_expr = int_to_z3(range,value);
        z3::expr pred = apply_expr == val_expr;
        add_alit(pred);
    }

    void randomize(const char *decl_name) {
        randomize(decl_name,0,(int *)0);
    }

    void randomize(const char *decl_name, int arg0) {
        randomize(decl_name,1,&arg0);
    }
    
    void randomize(const char *decl_name, int arg0, int arg1) {
        int args[2] = {arg0,arg1};
        randomize(decl_name,2,args);
    }

    void randomize(const char *decl_name, int arg0, int arg1, int arg2) {
        int args[3] = {arg0,arg1,arg2};
        randomize(decl_name,3,args);
    }

    void push(){
        slvr.push();
    }

    void pop(){
        slvr.pop();
    }

    z3::sort sort(const char *name) {
        if (std::string("bool") == name)
            return ctx.bool_sort();
        return enum_sorts.find(name)->second;
    }

    void mk_enum(const char *sort_name, unsigned num_values, char const * const * value_names) {
        z3::func_decl_vector cs(ctx), ts(ctx);
        z3::sort sort = ctx.enumeration_sort(sort_name, num_values, value_names, cs, ts);
        // can't use operator[] here because the value classes don't have nullary constructors
        enum_sorts.insert(std::pair<std::string, z3::sort>(sort_name,sort));
        enum_values.insert(std::pair<Z3_sort, z3::func_decl_vector>(sort,cs));
        sort_names.push_back(Z3_mk_string_symbol(ctx,sort_name));
        sorts.push_back(sort);
        for(unsigned i = 0; i < num_values; i++){
            Z3_symbol sym = Z3_mk_string_symbol(ctx,value_names[i]);
            decl_names.push_back(sym);
            decls.push_back(cs[i]);
            enum_to_int[sym] = i;
        }
    }

    void mk_bv(const char *sort_name, unsigned width) {
        z3::sort sort = ctx.bv_sort(width);
        // can't use operator[] here because the value classes don't have nullary constructors
        enum_sorts.insert(std::pair<std::string, z3::sort>(sort_name,sort));
    }

    void mk_int(const char *sort_name) {
        z3::sort sort = ctx.int_sort();
        // can't use operator[] here because the value classes don't have nullary constructors
        enum_sorts.insert(std::pair<std::string, z3::sort>(sort_name,sort));
    }

    void mk_string(const char *sort_name) {
        z3::sort sort = ctx.string_sort();
        // can't use operator[] here because the value classes don't have nullary constructors
        enum_sorts.insert(std::pair<std::string, z3::sort>(sort_name,sort));
    }

    void mk_sort(const char *sort_name) {
        Z3_symbol symb = Z3_mk_string_symbol(ctx,sort_name);
        z3::sort sort(ctx,Z3_mk_uninterpreted_sort(ctx, symb));
//        z3::sort sort = ctx.uninterpreted_sort(sort_name);
        // can't use operator[] here because the value classes don't have nullary constructors
        enum_sorts.insert(std::pair<std::string, z3::sort>(sort_name,sort));
        sort_names.push_back(symb);
        sorts.push_back(sort);
    }

    void mk_decl(const char *decl_name, unsigned arity, const char **domain_names, const char *range_name) {
        std::vector<z3::sort> domain;
        for (unsigned i = 0; i < arity; i++)
            domain.push_back(enum_sorts.find(domain_names[i])->second);
        std::string bool_name("Bool");
        z3::sort range = (range_name == bool_name) ? ctx.bool_sort() : enum_sorts.find(range_name)->second;   
        z3::func_decl decl = ctx.function(decl_name,arity,&domain[0],range);
        decl_names.push_back(Z3_mk_string_symbol(ctx,decl_name));
        decls.push_back(decl);
        decls_by_name.insert(std::pair<std::string, z3::func_decl>(decl_name,decl));
    }

    void mk_const(const char *const_name, const char *sort_name) {
        mk_decl(const_name,0,0,sort_name);
    }

    void add(const std::string &z3inp) {
        z3::expr fmla(ctx,Z3_parse_smtlib2_string(ctx, z3inp.c_str(), sort_names.size(), &sort_names[0], &sorts[0], decl_names.size(), &decl_names[0], &decls[0]));
        ctx.check_error();

        slvr.add(fmla);
    }

    bool solve() {
        // std::cout << alits.size();
        static bool show_model = true;
        while(true){
            z3::check_result res = slvr.check(alits.size(),&alits[0]);
            if (res != z3::unsat)
                break;
            z3::expr_vector core = slvr.unsat_core();
            if (core.size() == 0){
//                if (__ivy_modelfile.is_open()) 
//                    __ivy_modelfile << "begin unsat:\\n" << slvr << "end unsat:\\n" << std::endl;
                return false;
            }
            //for (unsigned i = 0; i < core.size(); i++)
            //    std::cout << "core: " << core[i] << std::endl;
            unsigned idx = rand() % core.size();
            z3::expr to_delete = core[idx];
            // std::cout << "to delete: " << to_delete << std::endl;
            for (unsigned i = 0; i < alits.size(); i++)
                if (z3::eq(alits[i],to_delete)) {
                    alits[i] = alits.back();
                    alits.pop_back();
                    break;
                }
        }
        model = slvr.get_model();
        alits.clear();
""".replace('classname',classname))
    if target.get() != "gen":
        header.append("""
        if(__ivy_modelfile.is_open()){
            __ivy_modelfile << "begin sat:\\n" << slvr << "end sat:\\n" << std::endl;
            __ivy_modelfile << model;
            __ivy_modelfile.flush();
        }
""")
    header.append("""
        return true;
    }

    int choose(int rng, const char *name){
        if (decls_by_name.find(name) == decls_by_name.end())
            return 0;
        return eval_apply(name);
    }
};
""".replace('classname',classname))

target = iu.EnumeratedParameter("target",["impl","gen","repl","test","class"],"gen")
opt_classname = iu.Parameter("classname","")
opt_build = iu.BooleanParameter("build",False)
opt_trace = iu.BooleanParameter("trace",False)
opt_test_iters = iu.Parameter("test_iters","100")
opt_test_runs = iu.Parameter("test_runs","1")
opt_compiler = iu.EnumeratedParameter("compiler",["g++","cl","default"],"default")
opt_main = iu.Parameter("main","main")
opt_stdafx = iu.BooleanParameter("stdafx",False)
opt_outdir = iu.Parameter("outdir","")

emit_main = True

def main():
    main_int(False)

def ivyc():
    main_int(True)

def main_int(is_ivyc):
    ia.set_determinize(True)
    slv.set_use_native_enums(True)
    iso.set_interpret_all_sorts(True)

    # set different defaults for ivyc

    if is_ivyc:
        target.set("repl")
        opt_build.set("true")

    ivy_init.read_params()
    iu.set_parameters({'coi':'false',"create_imports":'true',"enforce_axioms":'true','ui':'none','isolate_mode':'test','assume_invariants':'false'})
    if target.get() == "gen":
        iu.set_parameters({'filter_symbols':'false'})
    else:
        iu.set_parameters({'keep_destructors':'true'})
        
    if target.get() == 'class':
        target.set('repl')
        global emit_main
        emit_main = False
        
    with iu.ErrorPrinter():
        if len(sys.argv) == 2 and ic.get_file_version(sys.argv[1]) >= [2]:
            if not target.get() == 'repl' and emit_main:
                raise iu.IvyError(None,'Version 2 compiler supports only target=repl')
            cdir = os.path.join(os.path.dirname(__file__), 'ivy2/s3')
            cmd = 'IVY_INCLUDE_PATH={} {} {}'.format(os.path.join(cdir,'include'),os.path.join(cdir,'ivyc_s3'),sys.argv[1])
            print cmd
            sys.stdout.flush()
            status = os.system(cmd)
            exit(status)


    with im.Module():
        if target.get() == 'test':
            im.module.sig.add_symbol('_generating',il.BooleanSort())
        ivy_init.ivy_init(create_isolate=False)

        if iu.version_le(iu.get_string_version(),"1.6"):
            iso.set_interpret_all_sorts(True)

        isolate = ic.isolate.get()

        if is_ivyc:
            if isolate != None:
                isolates = [isolate]
            else:
                extracts = list((x,y) for x,y in im.module.isolates.iteritems()
                                if isinstance(y,ivy_ast.ExtractDef))
                if len(extracts) == 0:
                    isol = ivy_ast.ExtractDef(ivy_ast.Atom('extract'),ivy_ast.Atom('this'))
                    isol.with_args = 1
                    im.module.isolates['extract'] = isol
                    isolates = ['extract']
                elif len(extracts) == 1:
                    isolates = [extracts[0][0]]

        else:
            if isolate != None:
                isolates = [isolate]
            else:
                if isolate == 'all':
                    if target.get() == 'repl':
                        isolates = sorted(list(m for m in im.module.isolates if isinstance(m,ivy_ast.ExtractDef)))
                    else:
                        isolates = sorted(list(m for m in im.module.isolates if not isinstance(m,ivy_ast.ExtractDef)))
                else:
                    isolates = [isolate]

                if len(isolates) == 0:
                    isolates = [None]

                if isolates == [None] and not iu.version_le(iu.get_string_version(),"1.6"):
                    isolates = ['this']

        import json
        for isolate in isolates:
            with im.module.copy():
                with iu.ErrorPrinter():


                    def do_cmd(cmd):
                        print cmd
                        status = os.system(cmd)
                        if status:
                            exit(1)
    
                    if isolate:
                        if len(isolates) > 1:
                            print "Compiling isolate {}...".format(isolate)

                    if (not iu.version_le(iu.get_string_version(),"1.6") and
                        target.get() == 'repl' and isolate in im.module.isolates):
                        the_iso = im.module.isolates[isolate]
                        if not isinstance(the_iso,ivy_ast.ExtractDef):
                            the_iso = ivy_ast.ExtractDef(*the_iso.args)
                            the_iso.with_args = len(the_iso.args)
                            im.module.isolates[isolate] = the_iso
                        
                    iso.create_isolate(isolate) # ,ext='ext'

                    # Tricky: cone of influence may eliminate this symbol, but
                    # run-time accesses it.
                    if '_generating' not in im.module.sig.symbols:
                        im.module.sig.add_symbol('_generating',il.BooleanSort())


                    im.module.labeled_axioms.extend(im.module.labeled_props)
                    im.module.labeled_props = []
#                    if target.get() != 'repl':
#                        ifc.check_fragment(True)
                    with im.module.theory_context():
                        basename = opt_classname.get() or im.module.name
                        if len(isolates) > 1:
                            basename = basename + '_' + isolate
                        classname = varname(basename)
                        with ivy_cpp.CppContext():
                            header,impl = module_to_cpp_class(classname,basename)
            #        print header
            #        print impl
                    builddir = 'build' if os.path.exists('build') else '.'
                    f = open(outfile(builddir+'/'+basename+'.h'),'w')
                    f.write(header)
                    f.close()
                    f = open(outfile(builddir+'/'+basename+'.cpp'),'w')
                    f.write(impl)
                    f.close()
                if opt_build.get():
                    import platform
                    libpath = os.path.join(os.path.dirname(os.path.dirname(__file__)),'lib')
                    specfilename = os.path.join(libpath,'specs')
                    if os.path.isfile(specfilename):
                        try:
                            with open(specfilename) as inp:
                                libs = json.load(inp)
                        except:
                            sys.stderr.write('bad format in {}\n'.format(specfilename))
                            exit(1)
                    else:
                        libs = []    
                    cpp11 = any(x.endswith('.cppstd') and y.rep=='cpp11' for x,y in im.module.attributes.iteritems())
                    gpp11_spec = ' -std=c++11 ' if cpp11 else '' 
                    libspec = ''
                    for x,y in im.module.attributes.iteritems():
                        p,c = iu.parent_child_name(x)
                        if c == 'libspec':
                            if platform.system() == 'Windows':
                                libspec += ''.join(' {}'.format(ll) for ll in y.rep.strip('"').split(',') if ll.endswith('.lib'))
                            else:
                                libspec += ''.join(' -l' + ll for ll in y.rep.strip('"').split(',') if not ll.endswith('.lib'))
                    if platform.system() == 'Windows':
                        # if 'Z3DIR' in os.environ:
                        #     incspec = '/I %Z3DIR%\\include'
                        #     libpspec = '/LIBPATH:%Z3DIR%\\lib /LIBPATH:%Z3DIR%\\bin'
                        # else:
                        #     import z3
                        #     z3path = os.path.dirname(os.path.abspath(z3.__file__))
                        #     incspec = '/I {}'.format(z3path)
                        #     libpspec = '/LIBPATH:{}'.format(z3path)
                        _dir = os.path.dirname(os.path.abspath(__file__))
                        incspec = '/I {}'.format(os.path.join(_dir,'include'))
                        libpspec = '/LIBPATH:{}'.format(os.path.join(_dir,'lib'))
                        if not os.path.exists('libz3.dll'):
                            print 'Copying libz3.dll to current directory.'
                            print 'If the binary {}.exe is moved to another directory, this file must also be moved.'.format(basename)
                            do_cmd('copy {} libz3.dll'.format(os.path.join(_dir,'lib','libz3.dll')))
                        for lib in libs:
                            _incdir = lib[1] if len(lib) >= 2 else []
                            _libdir = lib[2] if len(lib) >= 3 else []
                            _incdir = [_incdir] if isinstance(_incdir,str) else _incdir
                            _libdir = [_libdir] if isinstance(_libdir,str) else _libdir
                            incspec += ''.join(' /I {} '.format(d) for d in _incdir)
                            libpspec += ''.join(' /LIBPATH:{} '.format(d) for d in _libdir)
                        vsdir = find_vs()
                        if opt_compiler.get() != 'g++':
                            cmd = '"{}\\VC\\vcvarsall.bat" amd64& cl /EHsc /Zi {}.cpp ws2_32.lib'.format(vsdir,basename)
                            if target.get() in ['gen','test']:
                                cmd = '"{}\\VC\\vcvarsall.bat" amd64& cl /MDd /EHsc /Zi {} {}.cpp ws2_32.lib libz3.lib /link {}'.format(vsdir,incspec,basename,libpspec)
                            cmd += libspec
                        else:
                            cmd = "g++ {} -I %Z3DIR%/include -L %Z3DIR%/lib -L %Z3DIR%/bin -g -o {} {}.cpp -lws2_32".format(gpp11_spec,basename,basename)
                            if target.get() in ['gen','test']:
                                cmd = cmd + ' -lz3'
                        if opt_outdir.get():
                            cmd = 'cd {} & '.format(opt_outdir.get()) + cmd
                    else:
                        if target.get() in ['gen','test']:
                            if 'Z3DIR' in os.environ:
                                paths = '-I $Z3DIR/include -L $Z3DIR/lib -Wl,-rpath=$Z3DIR/lib' 
                            else:
                                _dir = os.path.dirname(os.path.abspath(__file__))
                                paths = '-I {} -L {} -Wl,-rpath={}'.format(os.path.join(_dir,'include'),os.path.join(_dir,'lib'),os.path.join(_dir,'lib'))
                        else:
                            paths = ''
                        for lib in libs:
                            _dir = lib[1]
                            _libdir = lib[2] if len(lib) >= 3 else (_dir  + '/lib')
                            paths += ' -I {}/include -L {} -Wl,-rpath={}'.format(_dir,_libdir,_libdir)
                        if emit_main:
                            cmd = "g++ {} {} -g -o {} {}.cpp".format(gpp11_spec,paths,basename,basename)
                        else:
                            cmd = "g++ {} {} -g -c {}.cpp".format(gpp11_spec,paths,basename)
                        if target.get() in ['gen','test']:
                            cmd = cmd + ' -lz3'
                        cmd += libspec
                        cmd += ' -pthread'
                    print cmd
                    sys.stdout.flush()
                    with iu.WorkingDir(builddir):
                        status = os.system(cmd)
                    if status:
                        exit(1)

def outfile(name):
    return (opt_outdir.get() + '/' + name) if opt_outdir.get() else name
        
def find_vs():
    try:
        windir = os.getenv('WINDIR')
        drive = windir[0]
    except:
        drive = 'C'
    for v in range(15,9,-1):
        for w in ['',' (x86)']:
            dir = '{}:\\Program Files{}\\Microsoft Visual Studio {}.0'.format(drive,w,v)
            if os.path.exists(dir):
                return dir
    raise iu.IvyError(None,'Cannot find a suitable version of Visual Studio (require 10.0-15.0)')

if __name__ == "__main__":
    main_int(True)
        
