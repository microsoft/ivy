#define _HAS_ITERATOR_DEBUGGING 0

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
typedef std::string __strlit;
extern std::ofstream __ivy_out;
void __ivy_exit(int);

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


    class reader;
    class timer;

class ivyc_s1 {
  public:
    typedef ivyc_s1 ivy_class;

    std::vector<std::string> __argv;
#ifdef _WIN32
    void *mutex;  // forward reference to HANDLE
#else
    pthread_mutex_t mutex;
#endif
    void __lock();
    void __unlock();

#ifdef _WIN32
    std::vector<HANDLE> thread_ids;

#else
    std::vector<pthread_t> thread_ids;

#endif
    void install_reader(reader *);
    void install_thread(reader *);
    void install_timer(timer *);
    virtual ~ivyc_s1();
    std::vector<int> ___ivy_stack;
    int ___ivy_choose(int rng,const char *name,int id);
    virtual void ivy_assert(bool,const char *){}
    virtual void ivy_assume(bool,const char *){}
    virtual void ivy_check_progress(int,int){}
    enum char__kinds{char__alphanum,char__bracket,char__punct};
    class str : public std::vector<int>{
        public: size_t __hash() const { return hash_space::hash<std::vector<int> >()(*this);};
    };
    struct pretty__token {
    bool pair;
    unsigned long long tdepth;
    str first;
    unsigned long long second;
        size_t __hash() const { return hash_space::hash<bool>()(pair)+hash_space::hash<unsigned long long>()(tdepth)+hash_space::hash<str>()(first)+hash_space::hash<unsigned long long>()(second);}
    };
    class vector__pretty__token__ : public std::vector<pretty__token>{
        public: size_t __hash() const { return hash_space::hash<std::vector<pretty__token> >()(*this);};
    };
    struct pretty__state {
    unsigned long long begin;
    unsigned long long total;
        size_t __hash() const { return hash_space::hash<unsigned long long>()(begin)+hash_space::hash<unsigned long long>()(total);}
    };
    class vector__pos__ : public std::vector<unsigned long long>{
        public: size_t __hash() const { return hash_space::hash<std::vector<unsigned long long> >()(*this);};
    };
    class vector__pretty__state__ : public std::vector<pretty__state>{
        public: size_t __hash() const { return hash_space::hash<std::vector<pretty__state> >()(*this);};
    };
    struct pretty {
    vector__pretty__token__ tokens;
    pretty__state st;
    unsigned long long maxline;
    unsigned long long indent;
    str whitespace;
    vector__pretty__state__ states;
    vector__pos__ stack;
    str output;
    unsigned long long space;
    unsigned long long depth;
    bool cppstyle;
        size_t __hash() const { return hash_space::hash<vector__pretty__token__>()(tokens)+hash_space::hash<pretty__state>()(st)+hash_space::hash<unsigned long long>()(maxline)+hash_space::hash<unsigned long long>()(indent)+hash_space::hash<str>()(whitespace)+hash_space::hash<vector__pretty__state__>()(states)+hash_space::hash<vector__pos__>()(stack)+hash_space::hash<str>()(output)+hash_space::hash<unsigned long long>()(space)+hash_space::hash<unsigned long long>()(depth)+hash_space::hash<bool>()(cppstyle);}
    };
class annot{
public:
    struct wrap {
    
        virtual wrap *dup() = 0;
        virtual bool deref() = 0;
        virtual ~wrap() {}
    };
    
    template <typename T> struct twrap : public wrap {
    
        unsigned refs;
    
        T item;
    
        twrap(const T &item) : refs(1), item(item) {}
    
        virtual wrap *dup() {refs++; return this;}
    
        virtual bool deref() {return (--refs) != 0;}
    
    };
    
    int tag;
    
    wrap *ptr;
    
    annot(){
    tag=-1;
    ptr=0;
    }
    
    annot(int tag,wrap *ptr) : tag(tag),ptr(ptr) {}
    
    annot(const annot&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
    };
    
    annot& operator=(const annot&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
        return *this;
    };
    
    ~annot(){if(ptr){if (!ptr->deref()) delete ptr;}}
    
    static int temp_counter;
    
    static void prepare() {temp_counter = 0;}
    
    static void cleanup() {}
    
    size_t __hash() const {
    
        switch(tag) {
    
            case 0: return 0 + hash_space::hash<ivyc_s1::annot_i>()(ivyc_s1::annot::unwrap< ivyc_s1::annot_i >((*this)));
    
        }
    
        return 0;
    
    }
    
    template <typename T> static const T &unwrap(const annot &x) {
    
        return ((static_cast<const twrap<T> *>(x.ptr))->item);
    
    }
    
    template <typename T> static T &unwrap(annot &x) {
    
         twrap<T> *p = static_cast<twrap<T> *>(x.ptr);
    
         if (p->refs > 1) {
    
             p = new twrap<T> (p->item);
    
         }
    
         return ((static_cast<twrap<T> *>(p))->item);
    
    }
    
};    class vector__str__ : public std::vector<str>{
        public: size_t __hash() const { return hash_space::hash<std::vector<str> >()(*this);};
    };
    struct annot_i {
    vector__str__ comments;
    unsigned long long line;
    str file;
        size_t __hash() const { return hash_space::hash<vector__str__>()(comments)+hash_space::hash<unsigned long long>()(line)+hash_space::hash<str>()(file);}
    };
    struct pstate {
    str b;
    unsigned long long p;
    str tok;
    annot_i ann;
    bool ok;
        size_t __hash() const { return hash_space::hash<str>()(b)+hash_space::hash<unsigned long long>()(p)+hash_space::hash<str>()(tok)+hash_space::hash<annot_i>()(ann)+hash_space::hash<bool>()(ok);}
    };
    enum ivy__verb{ivy__verb__none,ivy__verb__arrow,ivy__verb__plus,ivy__verb__times,ivy__verb__colon,ivy__verb__app,ivy__verb__empty,ivy__verb__dot,ivy__verb__new,ivy__verb__numeral,ivy__verb__castv,ivy__verb__boolv,ivy__verb__truev,ivy__verb__falsev,ivy__verb__and,ivy__verb__or,ivy__verb__not,ivy__verb__iff,ivy__verb__equals,ivy__verb__notequals,ivy__verb__lt,ivy__verb__leq,ivy__verb__gt,ivy__verb__geq,ivy__verb__minus,ivy__verb__div,ivy__verb__string,ivy__verb__ite,ivy__verb__comma,ivy__verb__varv,ivy__verb__logvar,ivy__verb__isav};
class ivy__ident{
public:
    struct wrap {
    
        virtual wrap *dup() = 0;
        virtual bool deref() = 0;
        virtual ~wrap() {}
    };
    
    template <typename T> struct twrap : public wrap {
    
        unsigned refs;
    
        T item;
    
        twrap(const T &item) : refs(1), item(item) {}
    
        virtual wrap *dup() {refs++; return this;}
    
        virtual bool deref() {return (--refs) != 0;}
    
    };
    
    int tag;
    
    wrap *ptr;
    
    ivy__ident(){
    tag=-1;
    ptr=0;
    }
    
    ivy__ident(int tag,wrap *ptr) : tag(tag),ptr(ptr) {}
    
    ivy__ident(const ivy__ident&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
    };
    
    ivy__ident& operator=(const ivy__ident&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
        return *this;
    };
    
    ~ivy__ident(){if(ptr){if (!ptr->deref()) delete ptr;}}
    
    static int temp_counter;
    
    static void prepare() {temp_counter = 0;}
    
    static void cleanup() {}
    
    size_t __hash() const {
    
        switch(tag) {
    
            case 0: return 0 + hash_space::hash<ivyc_s1::ivy__strident>()(ivyc_s1::ivy__ident::unwrap< ivyc_s1::ivy__strident >((*this)));
    
            case 1: return 1 + hash_space::hash<ivyc_s1::ivy__numident>()(ivyc_s1::ivy__ident::unwrap< ivyc_s1::ivy__numident >((*this)));
    
            case 2: return 2 + hash_space::hash<ivyc_s1::ivy__dotident>()(ivyc_s1::ivy__ident::unwrap< ivyc_s1::ivy__dotident >((*this)));
    
        }
    
        return 0;
    
    }
    
    template <typename T> static const T &unwrap(const ivy__ident &x) {
    
        return ((static_cast<const twrap<T> *>(x.ptr))->item);
    
    }
    
    template <typename T> static T &unwrap(ivy__ident &x) {
    
         twrap<T> *p = static_cast<twrap<T> *>(x.ptr);
    
         if (p->refs > 1) {
    
             p = new twrap<T> (p->item);
    
         }
    
         return ((static_cast<twrap<T> *>(p))->item);
    
    }
    
};    class vector__ivy__ident__ : public std::vector<ivy__ident>{
        public: size_t __hash() const { return hash_space::hash<std::vector<ivy__ident> >()(*this);};
    };
    struct ivy__strident {
    str val;
    vector__ivy__ident__ subscrs;
        size_t __hash() const { return hash_space::hash<str>()(val)+hash_space::hash<vector__ivy__ident__>()(subscrs);}
    };
    struct ivy__numident {
    unsigned long long val;
        size_t __hash() const { return hash_space::hash<unsigned long long>()(val);}
    };
    struct ivy__dotident {
    ivy__ident namesp;
    ivy__strident member;
        size_t __hash() const { return hash_space::hash<ivy__ident>()(namesp)+hash_space::hash<ivy__strident>()(member);}
    };
class ivy__expr{
public:
    struct wrap {
    
        virtual wrap *dup() = 0;
        virtual bool deref() = 0;
        virtual ~wrap() {}
    };
    
    template <typename T> struct twrap : public wrap {
    
        unsigned refs;
    
        T item;
    
        twrap(const T &item) : refs(1), item(item) {}
    
        virtual wrap *dup() {refs++; return this;}
    
        virtual bool deref() {return (--refs) != 0;}
    
    };
    
    int tag;
    
    wrap *ptr;
    
    ivy__expr(){
    tag=-1;
    ptr=0;
    }
    
    ivy__expr(int tag,wrap *ptr) : tag(tag),ptr(ptr) {}
    
    ivy__expr(const ivy__expr&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
    };
    
    ivy__expr& operator=(const ivy__expr&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
        return *this;
    };
    
    ~ivy__expr(){if(ptr){if (!ptr->deref()) delete ptr;}}
    
    static int temp_counter;
    
    static void prepare() {temp_counter = 0;}
    
    static void cleanup() {}
    
    size_t __hash() const {
    
        switch(tag) {
    
            case 0: return 0 + hash_space::hash<ivyc_s1::ivy__symbol>()(ivyc_s1::ivy__expr::unwrap< ivyc_s1::ivy__symbol >((*this)));
    
            case 1: return 1 + hash_space::hash<ivyc_s1::ivy__app>()(ivyc_s1::ivy__expr::unwrap< ivyc_s1::ivy__app >((*this)));
    
            case 2: return 2 + hash_space::hash<ivyc_s1::ivy__variable>()(ivyc_s1::ivy__expr::unwrap< ivyc_s1::ivy__variable >((*this)));
    
            case 3: return 3 + hash_space::hash<ivyc_s1::ivy__pi>()(ivyc_s1::ivy__expr::unwrap< ivyc_s1::ivy__pi >((*this)));
    
        }
    
        return 0;
    
    }
    
    template <typename T> static const T &unwrap(const ivy__expr &x) {
    
        return ((static_cast<const twrap<T> *>(x.ptr))->item);
    
    }
    
    template <typename T> static T &unwrap(ivy__expr &x) {
    
         twrap<T> *p = static_cast<twrap<T> *>(x.ptr);
    
         if (p->refs > 1) {
    
             p = new twrap<T> (p->item);
    
         }
    
         return ((static_cast<twrap<T> *>(p))->item);
    
    }
    
};    struct ivy__symbol {
    ivy__ident name;
    ivy__verb vrb;
    annot ann;
        size_t __hash() const { return hash_space::hash<ivy__ident>()(name)+hash_space::hash<int>()(vrb)+hash_space::hash<annot>()(ann);}
    };
    class vector__ivy__expr__ : public std::vector<ivy__expr>{
        public: size_t __hash() const { return hash_space::hash<std::vector<ivy__expr> >()(*this);};
    };
    struct ivy__app {
    ivy__expr func;
    vector__ivy__expr__ args;
    annot ann;
        size_t __hash() const { return hash_space::hash<ivy__expr>()(func)+hash_space::hash<vector__ivy__expr__>()(args)+hash_space::hash<annot>()(ann);}
    };
    struct ivy__variable {
    unsigned long long idx;
    annot ann;
        size_t __hash() const { return hash_space::hash<unsigned long long>()(idx)+hash_space::hash<annot>()(ann);}
    };
    struct ivy__pi {
    vector__ivy__expr__ vars;
    ivy__expr body;
    annot ann;
        size_t __hash() const { return hash_space::hash<vector__ivy__expr__>()(vars)+hash_space::hash<ivy__expr>()(body)+hash_space::hash<annot>()(ann);}
    };
class ivy__stmt{
public:
    struct wrap {
    
        virtual wrap *dup() = 0;
        virtual bool deref() = 0;
        virtual ~wrap() {}
    };
    
    template <typename T> struct twrap : public wrap {
    
        unsigned refs;
    
        T item;
    
        twrap(const T &item) : refs(1), item(item) {}
    
        virtual wrap *dup() {refs++; return this;}
    
        virtual bool deref() {return (--refs) != 0;}
    
    };
    
    int tag;
    
    wrap *ptr;
    
    ivy__stmt(){
    tag=-1;
    ptr=0;
    }
    
    ivy__stmt(int tag,wrap *ptr) : tag(tag),ptr(ptr) {}
    
    ivy__stmt(const ivy__stmt&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
    };
    
    ivy__stmt& operator=(const ivy__stmt&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
        return *this;
    };
    
    ~ivy__stmt(){if(ptr){if (!ptr->deref()) delete ptr;}}
    
    static int temp_counter;
    
    static void prepare() {temp_counter = 0;}
    
    static void cleanup() {}
    
    size_t __hash() const {
    
        switch(tag) {
    
            case 0: return 0 + hash_space::hash<ivyc_s1::ivy__asgn>()(ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__asgn >((*this)));
    
            case 1: return 1 + hash_space::hash<ivyc_s1::ivy__sequence>()(ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__sequence >((*this)));
    
            case 2: return 2 + hash_space::hash<ivyc_s1::ivy__skipst>()(ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__skipst >((*this)));
    
            case 3: return 3 + hash_space::hash<ivyc_s1::ivy__ifst>()(ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__ifst >((*this)));
    
            case 4: return 4 + hash_space::hash<ivyc_s1::ivy__whilest>()(ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__whilest >((*this)));
    
            case 5: return 5 + hash_space::hash<ivyc_s1::ivy__breakst>()(ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__breakst >((*this)));
    
            case 6: return 6 + hash_space::hash<ivyc_s1::ivy__varst>()(ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__varst >((*this)));
    
        }
    
        return 0;
    
    }
    
    template <typename T> static const T &unwrap(const ivy__stmt &x) {
    
        return ((static_cast<const twrap<T> *>(x.ptr))->item);
    
    }
    
    template <typename T> static T &unwrap(ivy__stmt &x) {
    
         twrap<T> *p = static_cast<twrap<T> *>(x.ptr);
    
         if (p->refs > 1) {
    
             p = new twrap<T> (p->item);
    
         }
    
         return ((static_cast<twrap<T> *>(p))->item);
    
    }
    
};    struct ivy__asgn {
    ivy__expr lhs;
    ivy__expr rhs;
    annot ann;
        size_t __hash() const { return hash_space::hash<ivy__expr>()(lhs)+hash_space::hash<ivy__expr>()(rhs)+hash_space::hash<annot>()(ann);}
    };
    struct ivy__sequence {
    ivy__stmt lhs;
    ivy__stmt rhs;
    annot ann;
        size_t __hash() const { return hash_space::hash<ivy__stmt>()(lhs)+hash_space::hash<ivy__stmt>()(rhs)+hash_space::hash<annot>()(ann);}
    };
    class vector__ivy__stmt__ : public std::vector<ivy__stmt>{
        public: size_t __hash() const { return hash_space::hash<std::vector<ivy__stmt> >()(*this);};
    };
    struct ivy__skipst {
    annot ann;
        size_t __hash() const { return hash_space::hash<annot>()(ann);}
    };
    struct ivy__ifst {
    ivy__expr cond;
    ivy__stmt thenst;
    ivy__stmt elsest;
    annot ann;
        size_t __hash() const { return hash_space::hash<ivy__expr>()(cond)+hash_space::hash<ivy__stmt>()(thenst)+hash_space::hash<ivy__stmt>()(elsest)+hash_space::hash<annot>()(ann);}
    };
    struct ivy__whilest {
    ivy__expr cond;
    ivy__stmt body;
    annot ann;
        size_t __hash() const { return hash_space::hash<ivy__expr>()(cond)+hash_space::hash<ivy__stmt>()(body)+hash_space::hash<annot>()(ann);}
    };
    struct ivy__breakst {
    annot ann;
        size_t __hash() const { return hash_space::hash<annot>()(ann);}
    };
class ivy__decl{
public:
    struct wrap {
    
        virtual wrap *dup() = 0;
        virtual bool deref() = 0;
        virtual ~wrap() {}
    };
    
    template <typename T> struct twrap : public wrap {
    
        unsigned refs;
    
        T item;
    
        twrap(const T &item) : refs(1), item(item) {}
    
        virtual wrap *dup() {refs++; return this;}
    
        virtual bool deref() {return (--refs) != 0;}
    
    };
    
    int tag;
    
    wrap *ptr;
    
    ivy__decl(){
    tag=-1;
    ptr=0;
    }
    
    ivy__decl(int tag,wrap *ptr) : tag(tag),ptr(ptr) {}
    
    ivy__decl(const ivy__decl&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
    };
    
    ivy__decl& operator=(const ivy__decl&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
        return *this;
    };
    
    ~ivy__decl(){if(ptr){if (!ptr->deref()) delete ptr;}}
    
    static int temp_counter;
    
    static void prepare() {temp_counter = 0;}
    
    static void cleanup() {}
    
    size_t __hash() const {
    
        switch(tag) {
    
            case 0: return 0 + hash_space::hash<ivyc_s1::ivy__actdc>()(ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__actdc >((*this)));
    
            case 1: return 1 + hash_space::hash<ivyc_s1::ivy__groupdc>()(ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__groupdc >((*this)));
    
            case 2: return 2 + hash_space::hash<ivyc_s1::ivy__typedc>()(ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__typedc >((*this)));
    
            case 3: return 3 + hash_space::hash<ivyc_s1::ivy__vardc>()(ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__vardc >((*this)));
    
            case 4: return 4 + hash_space::hash<ivyc_s1::ivy__header>()(ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__header >((*this)));
    
            case 5: return 5 + hash_space::hash<ivyc_s1::ivy__interpdc>()(ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__interpdc >((*this)));
    
            case 6: return 6 + hash_space::hash<ivyc_s1::ivy__includedc>()(ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__includedc >((*this)));
    
            case 7: return 7 + hash_space::hash<ivyc_s1::ivy__moduledc>()(ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__moduledc >((*this)));
    
            case 8: return 8 + hash_space::hash<ivyc_s1::ivy__instantiatedc>()(ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__instantiatedc >((*this)));
    
            case 9: return 9 + hash_space::hash<ivyc_s1::ivy__objectdc>()(ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__objectdc >((*this)));
    
            case 10: return 10 + hash_space::hash<ivyc_s1::ivy__instancedc>()(ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__instancedc >((*this)));
    
            case 11: return 11 + hash_space::hash<ivyc_s1::ivy__initdc>()(ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__initdc >((*this)));
    
        }
    
        return 0;
    
    }
    
    template <typename T> static const T &unwrap(const ivy__decl &x) {
    
        return ((static_cast<const twrap<T> *>(x.ptr))->item);
    
    }
    
    template <typename T> static T &unwrap(ivy__decl &x) {
    
         twrap<T> *p = static_cast<twrap<T> *>(x.ptr);
    
         if (p->refs > 1) {
    
             p = new twrap<T> (p->item);
    
         }
    
         return ((static_cast<twrap<T> *>(p))->item);
    
    }
    
};    enum ivy__action_kind{ivy__action_kind__internal,ivy__action_kind__external,ivy__action_kind__imported,ivy__action_kind__exported};
    struct ivy__prototype_argument {
    ivy__expr name;
    bool is_input;
    unsigned long long inpos;
    bool is_output;
    unsigned long long outpos;
    bool is_ref;
    bool is_const;
        size_t __hash() const { return hash_space::hash<ivy__expr>()(name)+hash_space::hash<bool>()(is_input)+hash_space::hash<unsigned long long>()(inpos)+hash_space::hash<bool>()(is_output)+hash_space::hash<unsigned long long>()(outpos)+hash_space::hash<bool>()(is_ref)+hash_space::hash<bool>()(is_const);}
    };
    class vector__ivy__prototype_argument__ : public std::vector<ivy__prototype_argument>{
        public: size_t __hash() const { return hash_space::hash<std::vector<ivy__prototype_argument> >()(*this);};
    };
    struct ivy__prototype {
    vector__ivy__prototype_argument__ args;
    bool has_ret;
    ivy__prototype_argument ret;
        size_t __hash() const { return hash_space::hash<vector__ivy__prototype_argument__>()(args)+hash_space::hash<bool>()(has_ret)+hash_space::hash<ivy__prototype_argument>()(ret);}
    };
    struct ivy__actdc {
    ivy__expr name;
    ivy__action_kind kind;
    vector__ivy__expr__ inputs;
    vector__ivy__expr__ outputs;
    bool has_body;
    ivy__stmt body;
    annot ann;
    bool has_proto;
    ivy__prototype proto;
        size_t __hash() const { return hash_space::hash<ivy__expr>()(name)+hash_space::hash<int>()(kind)+hash_space::hash<vector__ivy__expr__>()(inputs)+hash_space::hash<vector__ivy__expr__>()(outputs)+hash_space::hash<bool>()(has_body)+hash_space::hash<ivy__stmt>()(body)+hash_space::hash<annot>()(ann)+hash_space::hash<bool>()(has_proto)+hash_space::hash<ivy__prototype>()(proto);}
    };
    class ivy__ident_set : public hash_space::hash_map<ivy__ident,bool>{
        public: size_t __hash() const { return hash_space::hash<hash_space::hash_map<ivy__ident,bool> >()(*this);};
    };
    struct ivy__varst {
    ivy__expr name;
    annot ann;
        size_t __hash() const { return hash_space::hash<ivy__expr>()(name)+hash_space::hash<annot>()(ann);}
    };
    class vector__ivy__decl__ : public std::vector<ivy__decl>{
        public: size_t __hash() const { return hash_space::hash<std::vector<ivy__decl> >()(*this);};
    };
    struct ivy__groupdc {
    vector__ivy__decl__ decls;
    annot ann;
        size_t __hash() const { return hash_space::hash<vector__ivy__decl__>()(decls)+hash_space::hash<annot>()(ann);}
    };
class ivy__typespec{
public:
    struct wrap {
    
        virtual wrap *dup() = 0;
        virtual bool deref() = 0;
        virtual ~wrap() {}
    };
    
    template <typename T> struct twrap : public wrap {
    
        unsigned refs;
    
        T item;
    
        twrap(const T &item) : refs(1), item(item) {}
    
        virtual wrap *dup() {refs++; return this;}
    
        virtual bool deref() {return (--refs) != 0;}
    
    };
    
    int tag;
    
    wrap *ptr;
    
    ivy__typespec(){
    tag=-1;
    ptr=0;
    }
    
    ivy__typespec(int tag,wrap *ptr) : tag(tag),ptr(ptr) {}
    
    ivy__typespec(const ivy__typespec&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
    };
    
    ivy__typespec& operator=(const ivy__typespec&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
        return *this;
    };
    
    ~ivy__typespec(){if(ptr){if (!ptr->deref()) delete ptr;}}
    
    static int temp_counter;
    
    static void prepare() {temp_counter = 0;}
    
    static void cleanup() {}
    
    size_t __hash() const {
    
        switch(tag) {
    
            case 0: return 0 + hash_space::hash<ivyc_s1::ivy__enumspec>()(ivyc_s1::ivy__typespec::unwrap< ivyc_s1::ivy__enumspec >((*this)));
    
            case 1: return 1 + hash_space::hash<ivyc_s1::ivy__structspec>()(ivyc_s1::ivy__typespec::unwrap< ivyc_s1::ivy__structspec >((*this)));
    
        }
    
        return 0;
    
    }
    
    template <typename T> static const T &unwrap(const ivy__typespec &x) {
    
        return ((static_cast<const twrap<T> *>(x.ptr))->item);
    
    }
    
    template <typename T> static T &unwrap(ivy__typespec &x) {
    
         twrap<T> *p = static_cast<twrap<T> *>(x.ptr);
    
         if (p->refs > 1) {
    
             p = new twrap<T> (p->item);
    
         }
    
         return ((static_cast<twrap<T> *>(p))->item);
    
    }
    
};    struct ivy__enumspec {
    vector__ivy__expr__ constructors;
    annot ann;
        size_t __hash() const { return hash_space::hash<vector__ivy__expr__>()(constructors)+hash_space::hash<annot>()(ann);}
    };
    struct ivy__structspec {
    vector__ivy__expr__ destructors;
    annot ann;
        size_t __hash() const { return hash_space::hash<vector__ivy__expr__>()(destructors)+hash_space::hash<annot>()(ann);}
    };
    struct ivy__typedc {
    ivy__expr sort;
    bool has_super;
    ivy__expr super;
    bool has_spec;
    ivy__typespec spec;
    annot ann;
        size_t __hash() const { return hash_space::hash<ivy__expr>()(sort)+hash_space::hash<bool>()(has_super)+hash_space::hash<ivy__expr>()(super)+hash_space::hash<bool>()(has_spec)+hash_space::hash<ivy__typespec>()(spec)+hash_space::hash<annot>()(ann);}
    };
    struct ivy__vardc {
    ivy__expr typing;
    bool is_destructor;
    bool has_def;
    ivy__expr def;
    annot ann;
        size_t __hash() const { return hash_space::hash<ivy__expr>()(typing)+hash_space::hash<bool>()(is_destructor)+hash_space::hash<bool>()(has_def)+hash_space::hash<ivy__expr>()(def)+hash_space::hash<annot>()(ann);}
    };
    struct ivy__header {
    str filename;
    annot ann;
        size_t __hash() const { return hash_space::hash<str>()(filename)+hash_space::hash<annot>()(ann);}
    };
    struct ivy__interpdc {
    ivy__expr itype;
    ivy__expr ctype;
    annot ann;
        size_t __hash() const { return hash_space::hash<ivy__expr>()(itype)+hash_space::hash<ivy__expr>()(ctype)+hash_space::hash<annot>()(ann);}
    };
    struct ivy__includedc {
    ivy__expr file;
    annot ann;
        size_t __hash() const { return hash_space::hash<ivy__expr>()(file)+hash_space::hash<annot>()(ann);}
    };
    struct ivy__moduledc {
    ivy__expr name;
    vector__ivy__expr__ prms;
    ivy__decl body;
    annot ann;
        size_t __hash() const { return hash_space::hash<ivy__expr>()(name)+hash_space::hash<vector__ivy__expr__>()(prms)+hash_space::hash<ivy__decl>()(body)+hash_space::hash<annot>()(ann);}
    };
    struct ivy__instantiatedc {
    ivy__expr name;
    vector__ivy__expr__ prms;
    annot ann;
        size_t __hash() const { return hash_space::hash<ivy__expr>()(name)+hash_space::hash<vector__ivy__expr__>()(prms)+hash_space::hash<annot>()(ann);}
    };
    struct ivy__objectdc {
    ivy__expr name;
    ivy__decl body;
    annot ann;
        size_t __hash() const { return hash_space::hash<ivy__expr>()(name)+hash_space::hash<ivy__decl>()(body)+hash_space::hash<annot>()(ann);}
    };
    struct ivy__instancedc {
    ivy__expr objname;
    ivy__expr modname;
    vector__ivy__expr__ prms;
    bool is_auto;
    annot ann;
        size_t __hash() const { return hash_space::hash<ivy__expr>()(objname)+hash_space::hash<ivy__expr>()(modname)+hash_space::hash<vector__ivy__expr__>()(prms)+hash_space::hash<bool>()(is_auto)+hash_space::hash<annot>()(ann);}
    };
    struct ivy__initdc {
    ivy__stmt body;
    annot ann;
        size_t __hash() const { return hash_space::hash<ivy__stmt>()(body)+hash_space::hash<annot>()(ann);}
    };
    struct ivy__version {
    vector__pos__ nums;
        size_t __hash() const { return hash_space::hash<vector__pos__>()(nums);}
    };
    struct ivy__prog {
    ivy__version vers;
    vector__ivy__decl__ decls;
        size_t __hash() const { return hash_space::hash<ivy__version>()(vers)+hash_space::hash<vector__ivy__decl__>()(decls);}
    };
class ivy__error{
public:
    struct wrap {
    
        virtual wrap *dup() = 0;
        virtual bool deref() = 0;
        virtual ~wrap() {}
    };
    
    template <typename T> struct twrap : public wrap {
    
        unsigned refs;
    
        T item;
    
        twrap(const T &item) : refs(1), item(item) {}
    
        virtual wrap *dup() {refs++; return this;}
    
        virtual bool deref() {return (--refs) != 0;}
    
    };
    
    int tag;
    
    wrap *ptr;
    
    ivy__error(){
    tag=-1;
    ptr=0;
    }
    
    ivy__error(int tag,wrap *ptr) : tag(tag),ptr(ptr) {}
    
    ivy__error(const ivy__error&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
    };
    
    ivy__error& operator=(const ivy__error&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
        return *this;
    };
    
    ~ivy__error(){if(ptr){if (!ptr->deref()) delete ptr;}}
    
    static int temp_counter;
    
    static void prepare() {temp_counter = 0;}
    
    static void cleanup() {}
    
    size_t __hash() const {
    
        switch(tag) {
    
            case 0: return 0 + hash_space::hash<ivyc_s1::ivy__type_clash>()(ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__type_clash >((*this)));
    
            case 1: return 1 + hash_space::hash<ivyc_s1::ivy__type_conversion>()(ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__type_conversion >((*this)));
    
            case 2: return 2 + hash_space::hash<ivyc_s1::ivy__untyped>()(ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__untyped >((*this)));
    
            case 3: return 3 + hash_space::hash<ivyc_s1::ivy__not_first_order>()(ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__not_first_order >((*this)));
    
            case 4: return 4 + hash_space::hash<ivyc_s1::ivy__file_not_found>()(ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__file_not_found >((*this)));
    
            case 5: return 5 + hash_space::hash<ivyc_s1::ivy__cannot_write>()(ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__cannot_write >((*this)));
    
            case 6: return 6 + hash_space::hash<ivyc_s1::ivy__undefined>()(ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__undefined >((*this)));
    
            case 7: return 7 + hash_space::hash<ivyc_s1::ivy__wrong_number_params>()(ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__wrong_number_params >((*this)));
    
            case 8: return 8 + hash_space::hash<ivyc_s1::ivy__syntax_error>()(ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__syntax_error >((*this)));
    
        }
    
        return 0;
    
    }
    
    template <typename T> static const T &unwrap(const ivy__error &x) {
    
        return ((static_cast<const twrap<T> *>(x.ptr))->item);
    
    }
    
    template <typename T> static T &unwrap(ivy__error &x) {
    
         twrap<T> *p = static_cast<twrap<T> *>(x.ptr);
    
         if (p->refs > 1) {
    
             p = new twrap<T> (p->item);
    
         }
    
         return ((static_cast<twrap<T> *>(p))->item);
    
    }
    
};    class vector__ivy__error__ : public std::vector<ivy__error>{
        public: size_t __hash() const { return hash_space::hash<std::vector<ivy__error> >()(*this);};
    };
    struct ivy__type_clash {
    ivy__expr e;
    ivy__expr t1;
    ivy__expr t2;
        size_t __hash() const { return hash_space::hash<ivy__expr>()(e)+hash_space::hash<ivy__expr>()(t1)+hash_space::hash<ivy__expr>()(t2);}
    };
    struct ivy__type_conversion {
    ivy__expr e;
    ivy__expr t1;
    ivy__expr t2;
        size_t __hash() const { return hash_space::hash<ivy__expr>()(e)+hash_space::hash<ivy__expr>()(t1)+hash_space::hash<ivy__expr>()(t2);}
    };
    struct ivy__untyped {
    ivy__expr e;
    ivy__expr t1;
        size_t __hash() const { return hash_space::hash<ivy__expr>()(e)+hash_space::hash<ivy__expr>()(t1);}
    };
    struct ivy__not_first_order {
    ivy__expr e;
    ivy__expr t1;
        size_t __hash() const { return hash_space::hash<ivy__expr>()(e)+hash_space::hash<ivy__expr>()(t1);}
    };
    struct ivy__file_not_found {
    str n;
        size_t __hash() const { return hash_space::hash<str>()(n);}
    };
    struct ivy__cannot_write {
    str n;
        size_t __hash() const { return hash_space::hash<str>()(n);}
    };
    struct ivy__undefined {
    ivy__ident n;
        size_t __hash() const { return hash_space::hash<ivy__ident>()(n);}
    };
    struct ivy__wrong_number_params {
    unsigned long long n;
        size_t __hash() const { return hash_space::hash<unsigned long long>()(n);}
    };
    struct ivy__syntax_error {
    str tok;
        size_t __hash() const { return hash_space::hash<str>()(tok);}
    };
    struct ivy__prog__readst {
    ivy__ident_set have_read;
        size_t __hash() const { return hash_space::hash<ivy__ident_set>()(have_read);}
    };
    class ivy__symeval : public hash_space::hash_map<ivy__ident,ivy__expr>{
        public: size_t __hash() const { return hash_space::hash<hash_space::hash_map<ivy__ident,ivy__expr> >()(*this);};
    };
    class ivy__ident_to_moduledc : public hash_space::hash_map<ivy__ident,ivy__moduledc>{
        public: size_t __hash() const { return hash_space::hash<hash_space::hash_map<ivy__ident,ivy__moduledc> >()(*this);};
    };
    class ivy__ident_to_ident : public hash_space::hash_map<ivy__ident,ivy__ident>{
        public: size_t __hash() const { return hash_space::hash<hash_space::hash_map<ivy__ident,ivy__ident> >()(*this);};
    };
    class ivy__ident_to_instantiatedc : public hash_space::hash_map<ivy__ident,ivy__instantiatedc>{
        public: size_t __hash() const { return hash_space::hash<hash_space::hash_map<ivy__ident,ivy__instantiatedc> >()(*this);};
    };
    struct ivy__flatst {
    vector__ivy__decl__ decls;
    ivy__ident_to_ident prmvals;
    ivy__ident_to_moduledc moddecls;
    ivy__ident_set defs;
    bool has_root;
    ivy__ident root;
    ivy__ident_set locals;
    ivy__ident_set globals;
    bool defining;
    bool absolute;
    bool dot_rhs;
    ivy__ident_to_instantiatedc autodefs;
    ivy__ident_set autos_pending;
    bool no_undefined;
        size_t __hash() const { return hash_space::hash<vector__ivy__decl__>()(decls)+hash_space::hash<ivy__ident_to_ident>()(prmvals)+hash_space::hash<ivy__ident_to_moduledc>()(moddecls)+hash_space::hash<ivy__ident_set>()(defs)+hash_space::hash<bool>()(has_root)+hash_space::hash<ivy__ident>()(root)+hash_space::hash<ivy__ident_set>()(locals)+hash_space::hash<ivy__ident_set>()(globals)+hash_space::hash<bool>()(defining)+hash_space::hash<bool>()(absolute)+hash_space::hash<bool>()(dot_rhs)+hash_space::hash<ivy__ident_to_instantiatedc>()(autodefs)+hash_space::hash<ivy__ident_set>()(autos_pending)+hash_space::hash<bool>()(no_undefined);}
    };
    class ivy__ident_to_exprs : public hash_space::hash_map<ivy__ident,vector__ivy__expr__>{
        public: size_t __hash() const { return hash_space::hash<hash_space::hash_map<ivy__ident,vector__ivy__expr__> >()(*this);};
    };
    struct ivy__subtypes {
    ivy__ident_to_exprs subtypes_of;
    ivy__symeval supertype_of;
        size_t __hash() const { return hash_space::hash<ivy__ident_to_exprs>()(subtypes_of)+hash_space::hash<ivy__symeval>()(supertype_of);}
    };
    struct ivy__global_types {
    ivy__symeval type_of;
    ivy__ident_set is_action;
    bool curried;
        size_t __hash() const { return hash_space::hash<ivy__symeval>()(type_of)+hash_space::hash<ivy__ident_set>()(is_action)+hash_space::hash<bool>()(curried);}
    };
    class ivy__param_map : public hash_space::hash_map<ivy__ident,unsigned long long>{
        public: size_t __hash() const { return hash_space::hash<hash_space::hash_map<ivy__ident,unsigned long long> >()(*this);};
    };
    class ivy__push_pop_ident_set__map_t : public hash_space::hash_map<ivy__ident,bool>{
        public: size_t __hash() const { return hash_space::hash<hash_space::hash_map<ivy__ident,bool> >()(*this);};
    };
    class ivy__push_pop_ident_set__vec_t : public std::vector<ivy__ident>{
        public: size_t __hash() const { return hash_space::hash<std::vector<ivy__ident> >()(*this);};
    };
    struct ivy__push_pop_ident_set {
    ivy__push_pop_ident_set__map_t map;
    ivy__push_pop_ident_set__vec_t del;
    vector__pos__ stack;
        size_t __hash() const { return hash_space::hash<ivy__push_pop_ident_set__map_t>()(map)+hash_space::hash<ivy__push_pop_ident_set__vec_t>()(del)+hash_space::hash<vector__pos__>()(stack);}
    };
    struct ivy__local_tracker {
    ivy__push_pop_ident_set map;
        size_t __hash() const { return hash_space::hash<ivy__push_pop_ident_set>()(map);}
    };
    class ivy__decost__map : public hash_space::hash_map<ivy__ident,ivy__expr>{
        public: size_t __hash() const { return hash_space::hash<hash_space::hash_map<ivy__ident,ivy__expr> >()(*this);};
    };
    struct ivy__decost {
    unsigned long long counter;
    ivy__decost__map m;
    ivy__symeval ty;
    bool member;
    bool ok;
    vector__ivy__expr__ failed;
    bool error_reported;
        size_t __hash() const { return hash_space::hash<unsigned long long>()(counter)+hash_space::hash<ivy__decost__map>()(m)+hash_space::hash<ivy__symeval>()(ty)+hash_space::hash<bool>()(member)+hash_space::hash<bool>()(ok)+hash_space::hash<vector__ivy__expr__>()(failed)+hash_space::hash<bool>()(error_reported);}
    };
    class ivy__elidest__map : public hash_space::hash_map<ivy__ident,bool>{
        public: size_t __hash() const { return hash_space::hash<hash_space::hash_map<ivy__ident,bool> >()(*this);};
    };
    struct ivy__elidest {
    ivy__elidest__map seen;
        size_t __hash() const { return hash_space::hash<ivy__elidest__map>()(seen);}
    };
    struct ivy__type_context__stack_entry {
    ivy__ident id;
    bool any;
    ivy__expr val;
        size_t __hash() const { return hash_space::hash<ivy__ident>()(id)+hash_space::hash<bool>()(any)+hash_space::hash<ivy__expr>()(val);}
    };
    class vector__ivy__type_context__stack_entry__ : public std::vector<ivy__type_context__stack_entry>{
        public: size_t __hash() const { return hash_space::hash<std::vector<ivy__type_context__stack_entry> >()(*this);};
    };
    struct ivy__type_context {
    ivy__symeval m;
    vector__ivy__type_context__stack_entry__ stack;
        size_t __hash() const { return hash_space::hash<ivy__symeval>()(m)+hash_space::hash<vector__ivy__type_context__stack_entry__>()(stack);}
    };
    struct ivy__typeinferst {
    ivy__type_context tc;
    ivy__subtypes subtype_rel;
        size_t __hash() const { return hash_space::hash<ivy__type_context>()(tc)+hash_space::hash<ivy__subtypes>()(subtype_rel);}
    };
    enum cpp__verb{cpp__verb__none,cpp__verb__arrow,cpp__verb__plus,cpp__verb__times,cpp__verb__colon,cpp__verb__app,cpp__verb__empty,cpp__verb__dot,cpp__verb__new,cpp__verb__numeral,cpp__verb__castv,cpp__verb__boolv,cpp__verb__truev,cpp__verb__falsev,cpp__verb__and,cpp__verb__or,cpp__verb__not,cpp__verb__iff,cpp__verb__equals,cpp__verb__notequals,cpp__verb__lt,cpp__verb__leq,cpp__verb__gt,cpp__verb__geq,cpp__verb__minus,cpp__verb__div,cpp__verb__string,cpp__verb__ite,cpp__verb__comma,cpp__verb__varv,cpp__verb__logvar,cpp__verb__isav};
class cpp__ident{
public:
    struct wrap {
    
        virtual wrap *dup() = 0;
        virtual bool deref() = 0;
        virtual ~wrap() {}
    };
    
    template <typename T> struct twrap : public wrap {
    
        unsigned refs;
    
        T item;
    
        twrap(const T &item) : refs(1), item(item) {}
    
        virtual wrap *dup() {refs++; return this;}
    
        virtual bool deref() {return (--refs) != 0;}
    
    };
    
    int tag;
    
    wrap *ptr;
    
    cpp__ident(){
    tag=-1;
    ptr=0;
    }
    
    cpp__ident(int tag,wrap *ptr) : tag(tag),ptr(ptr) {}
    
    cpp__ident(const cpp__ident&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
    };
    
    cpp__ident& operator=(const cpp__ident&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
        return *this;
    };
    
    ~cpp__ident(){if(ptr){if (!ptr->deref()) delete ptr;}}
    
    static int temp_counter;
    
    static void prepare() {temp_counter = 0;}
    
    static void cleanup() {}
    
    size_t __hash() const {
    
        switch(tag) {
    
            case 0: return 0 + hash_space::hash<ivyc_s1::cpp__strident>()(ivyc_s1::cpp__ident::unwrap< ivyc_s1::cpp__strident >((*this)));
    
            case 1: return 1 + hash_space::hash<ivyc_s1::cpp__numident>()(ivyc_s1::cpp__ident::unwrap< ivyc_s1::cpp__numident >((*this)));
    
            case 2: return 2 + hash_space::hash<ivyc_s1::cpp__dotident>()(ivyc_s1::cpp__ident::unwrap< ivyc_s1::cpp__dotident >((*this)));
    
        }
    
        return 0;
    
    }
    
    template <typename T> static const T &unwrap(const cpp__ident &x) {
    
        return ((static_cast<const twrap<T> *>(x.ptr))->item);
    
    }
    
    template <typename T> static T &unwrap(cpp__ident &x) {
    
         twrap<T> *p = static_cast<twrap<T> *>(x.ptr);
    
         if (p->refs > 1) {
    
             p = new twrap<T> (p->item);
    
         }
    
         return ((static_cast<twrap<T> *>(p))->item);
    
    }
    
};    class vector__cpp__ident__ : public std::vector<cpp__ident>{
        public: size_t __hash() const { return hash_space::hash<std::vector<cpp__ident> >()(*this);};
    };
    struct cpp__strident {
    str val;
    vector__cpp__ident__ subscrs;
        size_t __hash() const { return hash_space::hash<str>()(val)+hash_space::hash<vector__cpp__ident__>()(subscrs);}
    };
    struct cpp__numident {
    unsigned long long val;
        size_t __hash() const { return hash_space::hash<unsigned long long>()(val);}
    };
    struct cpp__dotident {
    cpp__ident namesp;
    cpp__strident member;
        size_t __hash() const { return hash_space::hash<cpp__ident>()(namesp)+hash_space::hash<cpp__strident>()(member);}
    };
class cpp__expr{
public:
    struct wrap {
    
        virtual wrap *dup() = 0;
        virtual bool deref() = 0;
        virtual ~wrap() {}
    };
    
    template <typename T> struct twrap : public wrap {
    
        unsigned refs;
    
        T item;
    
        twrap(const T &item) : refs(1), item(item) {}
    
        virtual wrap *dup() {refs++; return this;}
    
        virtual bool deref() {return (--refs) != 0;}
    
    };
    
    int tag;
    
    wrap *ptr;
    
    cpp__expr(){
    tag=-1;
    ptr=0;
    }
    
    cpp__expr(int tag,wrap *ptr) : tag(tag),ptr(ptr) {}
    
    cpp__expr(const cpp__expr&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
    };
    
    cpp__expr& operator=(const cpp__expr&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
        return *this;
    };
    
    ~cpp__expr(){if(ptr){if (!ptr->deref()) delete ptr;}}
    
    static int temp_counter;
    
    static void prepare() {temp_counter = 0;}
    
    static void cleanup() {}
    
    size_t __hash() const {
    
        switch(tag) {
    
            case 0: return 0 + hash_space::hash<ivyc_s1::cpp__symbol>()(ivyc_s1::cpp__expr::unwrap< ivyc_s1::cpp__symbol >((*this)));
    
            case 1: return 1 + hash_space::hash<ivyc_s1::cpp__app>()(ivyc_s1::cpp__expr::unwrap< ivyc_s1::cpp__app >((*this)));
    
            case 2: return 2 + hash_space::hash<ivyc_s1::cpp__variable>()(ivyc_s1::cpp__expr::unwrap< ivyc_s1::cpp__variable >((*this)));
    
            case 3: return 3 + hash_space::hash<ivyc_s1::cpp__pi>()(ivyc_s1::cpp__expr::unwrap< ivyc_s1::cpp__pi >((*this)));
    
        }
    
        return 0;
    
    }
    
    template <typename T> static const T &unwrap(const cpp__expr &x) {
    
        return ((static_cast<const twrap<T> *>(x.ptr))->item);
    
    }
    
    template <typename T> static T &unwrap(cpp__expr &x) {
    
         twrap<T> *p = static_cast<twrap<T> *>(x.ptr);
    
         if (p->refs > 1) {
    
             p = new twrap<T> (p->item);
    
         }
    
         return ((static_cast<twrap<T> *>(p))->item);
    
    }
    
};    struct cpp__symbol {
    cpp__ident name;
    cpp__verb vrb;
    annot ann;
        size_t __hash() const { return hash_space::hash<cpp__ident>()(name)+hash_space::hash<int>()(vrb)+hash_space::hash<annot>()(ann);}
    };
    class vector__cpp__expr__ : public std::vector<cpp__expr>{
        public: size_t __hash() const { return hash_space::hash<std::vector<cpp__expr> >()(*this);};
    };
    struct cpp__app {
    cpp__expr func;
    vector__cpp__expr__ args;
    annot ann;
        size_t __hash() const { return hash_space::hash<cpp__expr>()(func)+hash_space::hash<vector__cpp__expr__>()(args)+hash_space::hash<annot>()(ann);}
    };
    struct cpp__variable {
    unsigned long long idx;
    annot ann;
        size_t __hash() const { return hash_space::hash<unsigned long long>()(idx)+hash_space::hash<annot>()(ann);}
    };
    struct cpp__pi {
    vector__cpp__expr__ vars;
    cpp__expr body;
    annot ann;
        size_t __hash() const { return hash_space::hash<vector__cpp__expr__>()(vars)+hash_space::hash<cpp__expr>()(body)+hash_space::hash<annot>()(ann);}
    };
class cpp__stmt{
public:
    struct wrap {
    
        virtual wrap *dup() = 0;
        virtual bool deref() = 0;
        virtual ~wrap() {}
    };
    
    template <typename T> struct twrap : public wrap {
    
        unsigned refs;
    
        T item;
    
        twrap(const T &item) : refs(1), item(item) {}
    
        virtual wrap *dup() {refs++; return this;}
    
        virtual bool deref() {return (--refs) != 0;}
    
    };
    
    int tag;
    
    wrap *ptr;
    
    cpp__stmt(){
    tag=-1;
    ptr=0;
    }
    
    cpp__stmt(int tag,wrap *ptr) : tag(tag),ptr(ptr) {}
    
    cpp__stmt(const cpp__stmt&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
    };
    
    cpp__stmt& operator=(const cpp__stmt&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
        return *this;
    };
    
    ~cpp__stmt(){if(ptr){if (!ptr->deref()) delete ptr;}}
    
    static int temp_counter;
    
    static void prepare() {temp_counter = 0;}
    
    static void cleanup() {}
    
    size_t __hash() const {
    
        switch(tag) {
    
            case 0: return 0 + hash_space::hash<ivyc_s1::cpp__asgn>()(ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__asgn >((*this)));
    
            case 1: return 1 + hash_space::hash<ivyc_s1::cpp__sequence>()(ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__sequence >((*this)));
    
            case 2: return 2 + hash_space::hash<ivyc_s1::cpp__skipst>()(ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__skipst >((*this)));
    
            case 3: return 3 + hash_space::hash<ivyc_s1::cpp__ifst>()(ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__ifst >((*this)));
    
            case 4: return 4 + hash_space::hash<ivyc_s1::cpp__whilest>()(ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__whilest >((*this)));
    
            case 5: return 5 + hash_space::hash<ivyc_s1::cpp__breakst>()(ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__breakst >((*this)));
    
            case 6: return 6 + hash_space::hash<ivyc_s1::cpp__varst>()(ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__varst >((*this)));
    
            case 7: return 7 + hash_space::hash<ivyc_s1::cpp__retst>()(ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__retst >((*this)));
    
        }
    
        return 0;
    
    }
    
    template <typename T> static const T &unwrap(const cpp__stmt &x) {
    
        return ((static_cast<const twrap<T> *>(x.ptr))->item);
    
    }
    
    template <typename T> static T &unwrap(cpp__stmt &x) {
    
         twrap<T> *p = static_cast<twrap<T> *>(x.ptr);
    
         if (p->refs > 1) {
    
             p = new twrap<T> (p->item);
    
         }
    
         return ((static_cast<twrap<T> *>(p))->item);
    
    }
    
};    struct cpp__asgn {
    cpp__expr lhs;
    cpp__expr rhs;
    annot ann;
        size_t __hash() const { return hash_space::hash<cpp__expr>()(lhs)+hash_space::hash<cpp__expr>()(rhs)+hash_space::hash<annot>()(ann);}
    };
    struct cpp__sequence {
    cpp__stmt lhs;
    cpp__stmt rhs;
    annot ann;
        size_t __hash() const { return hash_space::hash<cpp__stmt>()(lhs)+hash_space::hash<cpp__stmt>()(rhs)+hash_space::hash<annot>()(ann);}
    };
    class vector__cpp__stmt__ : public std::vector<cpp__stmt>{
        public: size_t __hash() const { return hash_space::hash<std::vector<cpp__stmt> >()(*this);};
    };
    struct cpp__skipst {
    annot ann;
        size_t __hash() const { return hash_space::hash<annot>()(ann);}
    };
    struct cpp__ifst {
    cpp__expr cond;
    cpp__stmt thenst;
    cpp__stmt elsest;
    annot ann;
        size_t __hash() const { return hash_space::hash<cpp__expr>()(cond)+hash_space::hash<cpp__stmt>()(thenst)+hash_space::hash<cpp__stmt>()(elsest)+hash_space::hash<annot>()(ann);}
    };
    struct cpp__whilest {
    cpp__expr cond;
    cpp__stmt body;
    annot ann;
        size_t __hash() const { return hash_space::hash<cpp__expr>()(cond)+hash_space::hash<cpp__stmt>()(body)+hash_space::hash<annot>()(ann);}
    };
    struct cpp__breakst {
    annot ann;
        size_t __hash() const { return hash_space::hash<annot>()(ann);}
    };
    struct cpp__simpletype {
    cpp__expr _type;
    cpp__expr name;
    bool is_const;
    bool is_ref;
        size_t __hash() const { return hash_space::hash<cpp__expr>()(_type)+hash_space::hash<cpp__expr>()(name)+hash_space::hash<bool>()(is_const)+hash_space::hash<bool>()(is_ref);}
    };
    class vector__cpp__simpletype__ : public std::vector<cpp__simpletype>{
        public: size_t __hash() const { return hash_space::hash<std::vector<cpp__simpletype> >()(*this);};
    };
    struct cpp__functype {
    cpp__simpletype base;
    vector__cpp__simpletype__ args;
    bool is_const;
    bool has_initializer;
    cpp__expr initializer;
        size_t __hash() const { return hash_space::hash<cpp__simpletype>()(base)+hash_space::hash<vector__cpp__simpletype__>()(args)+hash_space::hash<bool>()(is_const)+hash_space::hash<bool>()(has_initializer)+hash_space::hash<cpp__expr>()(initializer);}
    };
    struct cpp__varst {
    cpp__simpletype vtype;
    annot ann;
        size_t __hash() const { return hash_space::hash<cpp__simpletype>()(vtype)+hash_space::hash<annot>()(ann);}
    };
    struct cpp__retst {
    cpp__expr val;
    annot ann;
        size_t __hash() const { return hash_space::hash<cpp__expr>()(val)+hash_space::hash<annot>()(ann);}
    };
class cpp__decl{
public:
    struct wrap {
    
        virtual wrap *dup() = 0;
        virtual bool deref() = 0;
        virtual ~wrap() {}
    };
    
    template <typename T> struct twrap : public wrap {
    
        unsigned refs;
    
        T item;
    
        twrap(const T &item) : refs(1), item(item) {}
    
        virtual wrap *dup() {refs++; return this;}
    
        virtual bool deref() {return (--refs) != 0;}
    
    };
    
    int tag;
    
    wrap *ptr;
    
    cpp__decl(){
    tag=-1;
    ptr=0;
    }
    
    cpp__decl(int tag,wrap *ptr) : tag(tag),ptr(ptr) {}
    
    cpp__decl(const cpp__decl&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
    };
    
    cpp__decl& operator=(const cpp__decl&other){
        tag=other.tag;
        ptr = other.ptr ? other.ptr->dup() : 0;
        return *this;
    };
    
    ~cpp__decl(){if(ptr){if (!ptr->deref()) delete ptr;}}
    
    static int temp_counter;
    
    static void prepare() {temp_counter = 0;}
    
    static void cleanup() {}
    
    size_t __hash() const {
    
        switch(tag) {
    
            case 0: return 0 + hash_space::hash<ivyc_s1::cpp__header>()(ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__header >((*this)));
    
            case 1: return 1 + hash_space::hash<ivyc_s1::cpp__typedecl>()(ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__typedecl >((*this)));
    
            case 2: return 2 + hash_space::hash<ivyc_s1::cpp__enumdecl>()(ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__enumdecl >((*this)));
    
            case 3: return 3 + hash_space::hash<ivyc_s1::cpp__vardecl>()(ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__vardecl >((*this)));
    
            case 4: return 4 + hash_space::hash<ivyc_s1::cpp__funcdecl>()(ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__funcdecl >((*this)));
    
            case 5: return 5 + hash_space::hash<ivyc_s1::cpp__structdecl>()(ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__structdecl >((*this)));
    
            case 6: return 6 + hash_space::hash<ivyc_s1::cpp__namespacedecl>()(ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__namespacedecl >((*this)));
    
            case 7: return 7 + hash_space::hash<ivyc_s1::cpp__groupdc>()(ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__groupdc >((*this)));
    
        }
    
        return 0;
    
    }
    
    template <typename T> static const T &unwrap(const cpp__decl &x) {
    
        return ((static_cast<const twrap<T> *>(x.ptr))->item);
    
    }
    
    template <typename T> static T &unwrap(cpp__decl &x) {
    
         twrap<T> *p = static_cast<twrap<T> *>(x.ptr);
    
         if (p->refs > 1) {
    
             p = new twrap<T> (p->item);
    
         }
    
         return ((static_cast<twrap<T> *>(p))->item);
    
    }
    
};    struct cpp__header {
    str filename;
    annot ann;
        size_t __hash() const { return hash_space::hash<str>()(filename)+hash_space::hash<annot>()(ann);}
    };
    struct cpp__typedecl {
    cpp__simpletype ttype;
    annot ann;
        size_t __hash() const { return hash_space::hash<cpp__simpletype>()(ttype)+hash_space::hash<annot>()(ann);}
    };
    struct cpp__enumdecl {
    cpp__expr name;
    vector__cpp__expr__ elems;
    annot ann;
        size_t __hash() const { return hash_space::hash<cpp__expr>()(name)+hash_space::hash<vector__cpp__expr__>()(elems)+hash_space::hash<annot>()(ann);}
    };
    struct cpp__vardecl {
    cpp__simpletype vtype;
    annot ann;
        size_t __hash() const { return hash_space::hash<cpp__simpletype>()(vtype)+hash_space::hash<annot>()(ann);}
    };
    struct cpp__funcdecl {
    cpp__functype ftype;
    bool has_body;
    cpp__stmt body;
    bool is_static;
    bool is_virtual;
    annot ann;
        size_t __hash() const { return hash_space::hash<cpp__functype>()(ftype)+hash_space::hash<bool>()(has_body)+hash_space::hash<cpp__stmt>()(body)+hash_space::hash<bool>()(is_static)+hash_space::hash<bool>()(is_virtual)+hash_space::hash<annot>()(ann);}
    };
    class vector__cpp__decl__ : public std::vector<cpp__decl>{
        public: size_t __hash() const { return hash_space::hash<std::vector<cpp__decl> >()(*this);};
    };
    struct cpp__structdecl {
    cpp__expr name;
    bool has_super;
    cpp__expr super;
    bool has_members;
    vector__cpp__decl__ members;
    annot ann;
        size_t __hash() const { return hash_space::hash<cpp__expr>()(name)+hash_space::hash<bool>()(has_super)+hash_space::hash<cpp__expr>()(super)+hash_space::hash<bool>()(has_members)+hash_space::hash<vector__cpp__decl__>()(members)+hash_space::hash<annot>()(ann);}
    };
    struct cpp__namespacedecl {
    cpp__expr name;
    vector__cpp__decl__ members;
    annot ann;
        size_t __hash() const { return hash_space::hash<cpp__expr>()(name)+hash_space::hash<vector__cpp__decl__>()(members)+hash_space::hash<annot>()(ann);}
    };
    struct cpp__groupdc {
    vector__cpp__decl__ decls;
    annot ann;
        size_t __hash() const { return hash_space::hash<vector__cpp__decl__>()(decls)+hash_space::hash<annot>()(ann);}
    };
    struct cpp__version {
    vector__pos__ nums;
        size_t __hash() const { return hash_space::hash<vector__pos__>()(nums);}
    };
    struct cpp__prog {
    cpp__version vers;
    vector__cpp__decl__ decls;
        size_t __hash() const { return hash_space::hash<cpp__version>()(vers)+hash_space::hash<vector__cpp__decl__>()(decls);}
    };
    struct ivy__access_path {
    vector__ivy__ident__ elems;
        size_t __hash() const { return hash_space::hash<vector__ivy__ident__>()(elems);}
    };
    struct ivy__lvalue_count {
    cpp__expr lvalue;
    ivy__access_path path;
    unsigned long long cnt;
        size_t __hash() const { return hash_space::hash<cpp__expr>()(lvalue)+hash_space::hash<ivy__access_path>()(path)+hash_space::hash<unsigned long long>()(cnt);}
    };
    class ivy__ident_to_declvec : public hash_space::hash_map<ivy__ident,vector__ivy__decl__>{
        public: size_t __hash() const { return hash_space::hash<hash_space::hash_map<ivy__ident,vector__ivy__decl__> >()(*this);};
    };
    class ivy__ident_to_cppclass : public hash_space::hash_map<ivy__ident,ivy__expr>{
        public: size_t __hash() const { return hash_space::hash<hash_space::hash_map<ivy__ident,ivy__expr> >()(*this);};
    };
    class ivy__ident_to_prototype : public hash_space::hash_map<ivy__ident,ivy__prototype>{
        public: size_t __hash() const { return hash_space::hash<hash_space::hash_map<ivy__ident,ivy__prototype> >()(*this);};
    };
    class vector__ivy__lvalue_count__ : public std::vector<ivy__lvalue_count>{
        public: size_t __hash() const { return hash_space::hash<std::vector<ivy__lvalue_count> >()(*this);};
    };
    struct ivy__tocppst {
    ivy__ident_to_declvec members;
    ivy__ident_to_cppclass cppclasses;
    ivy__ident_set objects;
    ivy__global_types globals;
    bool is_member;
    ivy__ident this_ident;
    bool in_class;
    bool proto_only;
    ivy__subtypes subtype_rel;
    bool native;
    bool forward;
    vector__ivy__expr__ outputs;
    vector__cpp__stmt__ code;
    unsigned long long counter;
    ivy__ident_to_prototype protos;
    vector__ivy__lvalue_count__ dead;
    ivy__local_tracker locals;
    ivy__ident_set constructors;
    bool dot_rhs;
        size_t __hash() const { return hash_space::hash<ivy__ident_to_declvec>()(members)+hash_space::hash<ivy__ident_to_cppclass>()(cppclasses)+hash_space::hash<ivy__ident_set>()(objects)+hash_space::hash<ivy__global_types>()(globals)+hash_space::hash<bool>()(is_member)+hash_space::hash<ivy__ident>()(this_ident)+hash_space::hash<bool>()(in_class)+hash_space::hash<bool>()(proto_only)+hash_space::hash<ivy__subtypes>()(subtype_rel)+hash_space::hash<bool>()(native)+hash_space::hash<bool>()(forward)+hash_space::hash<vector__ivy__expr__>()(outputs)+hash_space::hash<vector__cpp__stmt__>()(code)+hash_space::hash<unsigned long long>()(counter)+hash_space::hash<ivy__ident_to_prototype>()(protos)+hash_space::hash<vector__ivy__lvalue_count__>()(dead)+hash_space::hash<ivy__local_tracker>()(locals)+hash_space::hash<ivy__ident_set>()(constructors)+hash_space::hash<bool>()(dot_rhs);}
    };
    class vector__ivy__access_path__ : public std::vector<ivy__access_path>{
        public: size_t __hash() const { return hash_space::hash<std::vector<ivy__access_path> >()(*this);};
    };
    bool ivy__verb_out_to_in[32];
    unsigned long long ivy__verb_to_arity[32];
    hash_thunk<str,cpp__verb> cpp__str_to_verb;
    ivy__expr ivy__optypes[32];
    int cpp__verb_to_prio[32];
    str input_file_name;
    hash_thunk<str,bool> ivy__cpp_reserved_word;
    bool ivy__verb_mono[32];
    bool _generating;
    bool ivy__verb_first_to_in[32];
    str cpp__verb_to_str[32];
    int ivy__verb_to_prio[32];
    vector__ivy__error__ ivy__errors;
    vector__str__ ivy__include_path;
    bool ivy__verb_in_to_out[32];
    hash_thunk<str,ivy__verb> ivy__str_to_verb;
    unsigned long long cpp__verb_to_arity[32];
    str ivy__verb_to_str[32];
    long long __CARD__vector__ivy__stmt____domain;
    long long __CARD__vector__ivy__lvalue_count____domain;
    long long __CARD__vector__ivy__decl____domain;
    long long __CARD__pos;
    long long __CARD__char;
    long long __CARD__vector__cpp__decl____domain;
    long long __CARD__vector__cpp__ident____domain;
    long long __CARD__vector__ivy__expr____domain;
    long long __CARD__vector__cpp__expr____domain;
    long long __CARD__vector__ivy__type_context__stack_entry____domain;
    long long __CARD__vector__pretty__token____domain;
    long long __CARD__vector__ivy__ident____domain;
    long long __CARD__vector__cpp__stmt____domain;
    long long __CARD__vector__cpp__simpletype____domain;
    long long __CARD__vector__pretty__state____domain;
    long long __CARD__vector__ivy__prototype_argument____domain;
    long long __CARD__vector__pos____domain;
    long long __CARD__vector__str____domain;
    long long __CARD__vector__ivy__error____domain;
    long long __CARD__vector__ivy__access_path____domain;
    long long __CARD__priority;
    virtual bool char__is_alphanum(int X);
    virtual bool char__is_bracket(int X);
    virtual bool char__is_white(int X);
    virtual char__kinds char__kind(int X);
    virtual bool char__non_printing(int X);
    virtual bool char__is_digit(int X);
    virtual bool char__is_capital(int X);
    virtual unsigned long long str__begin(const str& A);
    virtual unsigned long long vector__pretty__token____begin(const vector__pretty__token__& A);
    virtual unsigned long long vector__pos____begin(const vector__pos__& A);
    virtual unsigned long long vector__str____begin(const vector__str__& A);
    virtual unsigned long long vector__ivy__ident____begin(const vector__ivy__ident__& A);
    virtual unsigned long long vector__ivy__expr____begin(const vector__ivy__expr__& A);
    virtual unsigned long long vector__ivy__stmt____begin(const vector__ivy__stmt__& A);
    virtual unsigned long long vector__ivy__prototype_argument____begin(const vector__ivy__prototype_argument__& A);
    virtual unsigned long long vector__ivy__decl____begin(const vector__ivy__decl__& A);
    virtual unsigned long long vector__cpp__ident____begin(const vector__cpp__ident__& A);
    virtual unsigned long long vector__cpp__expr____begin(const vector__cpp__expr__& A);
    virtual unsigned long long vector__cpp__stmt____begin(const vector__cpp__stmt__& A);
    virtual unsigned long long vector__cpp__simpletype____begin(const vector__cpp__simpletype__& A);
    virtual unsigned long long vector__cpp__decl____begin(const vector__cpp__decl__& A);
    virtual unsigned long long vector__ivy__lvalue_count____begin(const vector__ivy__lvalue_count__& A);
    virtual unsigned long long vector__ivy__access_path____begin(const vector__ivy__access_path__& A);
    virtual int str__value(const str& a, unsigned long long i);
    virtual unsigned long long str__end(const str& a);
    virtual str str__segment(const str& a, unsigned long long lo, unsigned long long hi);
    virtual pretty__token vector__pretty__token____value(const vector__pretty__token__& a, unsigned long long i);
    virtual unsigned long long vector__pretty__token____end(const vector__pretty__token__& a);
    virtual unsigned long long vector__pos____value(const vector__pos__& a, unsigned long long i);
    virtual unsigned long long vector__pos____end(const vector__pos__& a);
    virtual pretty__state vector__pretty__state____value(const vector__pretty__state__& a, unsigned long long i);
    virtual unsigned long long vector__pretty__state____end(const vector__pretty__state__& a);
    virtual str vector__str____value(const vector__str__& a, unsigned long long i);
    virtual unsigned long long vector__str____end(const vector__str__& a);
    virtual vector__str__ vector__str____segment(const vector__str__& a, unsigned long long lo, unsigned long long hi);
    virtual ivyc_s1::ivy__ident vector__ivy__ident____value(const vector__ivy__ident__& a, unsigned long long i);
    virtual unsigned long long vector__ivy__ident____end(const vector__ivy__ident__& a);
    virtual ivyc_s1::ivy__expr vector__ivy__expr____value(const vector__ivy__expr__& a, unsigned long long i);
    virtual unsigned long long vector__ivy__expr____end(const vector__ivy__expr__& a);
    virtual vector__ivy__expr__ vector__ivy__expr____segment(const vector__ivy__expr__& a, unsigned long long lo, unsigned long long hi);
    virtual ivyc_s1::ivy__stmt vector__ivy__stmt____value(const vector__ivy__stmt__& a, unsigned long long i);
    virtual unsigned long long vector__ivy__stmt____end(const vector__ivy__stmt__& a);
    virtual ivy__prototype_argument vector__ivy__prototype_argument____value(const vector__ivy__prototype_argument__& a, unsigned long long i);
    virtual unsigned long long vector__ivy__prototype_argument____end(const vector__ivy__prototype_argument__& a);
    virtual ivyc_s1::ivy__decl vector__ivy__decl____value(const vector__ivy__decl__& a, unsigned long long i);
    virtual unsigned long long vector__ivy__decl____end(const vector__ivy__decl__& a);
    virtual ivyc_s1::ivy__error vector__ivy__error____value(const vector__ivy__error__& a, unsigned long long i);
    virtual unsigned long long vector__ivy__error____end(const vector__ivy__error__& a);
    virtual ivyc_s1::ivy__expr ivy__symeval__value(const ivy__symeval& a, ivyc_s1::ivy__ident i);
    virtual ivy__instantiatedc ivy__ident_to_instantiatedc__value(const ivy__ident_to_instantiatedc& a, ivyc_s1::ivy__ident i);
    virtual unsigned long long ivy__param_map__value(const ivy__param_map& a, ivyc_s1::ivy__ident i);
    virtual ivyc_s1::ivy__ident ivy__push_pop_ident_set__vec_t__value(const ivy__push_pop_ident_set__vec_t& a, unsigned long long i);
    virtual unsigned long long ivy__push_pop_ident_set__vec_t__end(const ivy__push_pop_ident_set__vec_t& a);
    virtual ivy__type_context__stack_entry vector__ivy__type_context__stack_entry____value(const vector__ivy__type_context__stack_entry__& a, unsigned long long i);
    virtual unsigned long long vector__ivy__type_context__stack_entry____end(const vector__ivy__type_context__stack_entry__& a);
    virtual ivyc_s1::cpp__ident vector__cpp__ident____value(const vector__cpp__ident__& a, unsigned long long i);
    virtual unsigned long long vector__cpp__ident____end(const vector__cpp__ident__& a);
    virtual ivyc_s1::cpp__expr vector__cpp__expr____value(const vector__cpp__expr__& a, unsigned long long i);
    virtual unsigned long long vector__cpp__expr____end(const vector__cpp__expr__& a);
    virtual vector__cpp__expr__ vector__cpp__expr____segment(const vector__cpp__expr__& a, unsigned long long lo, unsigned long long hi);
    virtual ivyc_s1::cpp__stmt vector__cpp__stmt____value(const vector__cpp__stmt__& a, unsigned long long i);
    virtual unsigned long long vector__cpp__stmt____end(const vector__cpp__stmt__& a);
    virtual cpp__simpletype vector__cpp__simpletype____value(const vector__cpp__simpletype__& a, unsigned long long i);
    virtual unsigned long long vector__cpp__simpletype____end(const vector__cpp__simpletype__& a);
    virtual ivyc_s1::cpp__decl vector__cpp__decl____value(const vector__cpp__decl__& a, unsigned long long i);
    virtual unsigned long long vector__cpp__decl____end(const vector__cpp__decl__& a);
    virtual ivyc_s1::ivy__expr ivy__ident_to_cppclass__value(const ivy__ident_to_cppclass& a, ivyc_s1::ivy__ident i);
    virtual ivy__prototype ivy__ident_to_prototype__value(const ivy__ident_to_prototype& a, ivyc_s1::ivy__ident i);
    virtual ivy__lvalue_count vector__ivy__lvalue_count____value(const vector__ivy__lvalue_count__& a, unsigned long long i);
    virtual unsigned long long vector__ivy__lvalue_count____end(const vector__ivy__lvalue_count__& a);
    virtual ivy__access_path vector__ivy__access_path____value(const vector__ivy__access_path__& a, unsigned long long i);
    virtual unsigned long long vector__ivy__access_path____end(const vector__ivy__access_path__& a);
    ivyc_s1(str input_file_name);
    virtual void ext__ivy__typespec__auto_flat_spec(ivyc_s1::ivy__typespec s, ivy__flatst& st, ivyc_s1::ivy__expr ty);
    virtual ivyc_s1::ivy__expr ext__ivy__get_typed_symbol(ivyc_s1::ivy__expr typing);
    virtual void ext__ivy__ident_to_declvec__get(const ivy__ident_to_declvec& a, ivyc_s1::ivy__ident x, vector__ivy__decl__& y);
    virtual ivyc_s1::ivy__stmt ext__ivy__asgn__make(ivyc_s1::ivy__expr x, ivyc_s1::ivy__expr y, ivyc_s1::annot ann);
    virtual unsigned long long ext__vector__ivy__access_path____domain__next(unsigned long long x);
    virtual ivyc_s1::ivy__decl ext__ivy__vardc__typeinfer(const ivy__vardc& s, ivy__typeinferst& st);
    virtual void ext__vector__ivy__prototype_argument____append(vector__ivy__prototype_argument__& a, const ivy__prototype_argument& v);
    virtual ivyc_s1::cpp__expr ext__ivy__make_cpp_call(ivyc_s1::ivy__expr func, const vector__cpp__expr__& args, ivyc_s1::annot ann, ivy__tocppst& st);
    virtual void ext__ivy__header__flat(const ivy__header& s, ivy__flatst& st);
    virtual void ext__ivy__instantiatedc__flat(const ivy__instantiatedc& s, ivy__flatst& st);
    virtual void ext__ivy__typedc__build_global_types(const ivy__typedc& s, ivy__global_types& st);
    virtual ivyc_s1::cpp__expr ext__cpp__expr__prefix(ivyc_s1::cpp__expr s, ivyc_s1::cpp__ident pref);
    virtual cpp__verb ext__cpp__verb_from_name(const str& name);
    virtual void ext__ivy__typespec__parse(pstate& st, int prio, ivyc_s1::ivy__typespec& res);
    virtual ivyc_s1::cpp__decl ext__ivy__enum_to_cpp(ivyc_s1::cpp__expr name, ivyc_s1::ivy__typespec spec, ivyc_s1::cpp__decl sd, ivy__tocppst& st);
    virtual bool ext__ivy__initdc__emitted(const ivy__initdc& s, const ivy__tocppst& st);
    virtual ivyc_s1::cpp__expr ext__cpp__inttype(ivyc_s1::annot ann);
    virtual ivyc_s1::ivy__stmt ext__ivy__sequence__typeinfer(const ivy__sequence& s, ivy__typeinferst& st);
    virtual void ext__ivy__add_derived_traits(cpp__structdecl& s);
    virtual ivyc_s1::ivy__typespec ext__ivy__typespec__flat(ivyc_s1::ivy__typespec s, ivy__flatst& st);
    virtual unsigned long long ext__vector__cpp__ident____domain__next(unsigned long long x);
    virtual void ext__cpp__namespacedecl__encode(const cpp__namespacedecl& s, pretty& b, int prio);
    virtual ivyc_s1::ivy__ident ext__ivy__strident__prefix(const ivy__strident& s, ivyc_s1::ivy__ident pref);
    virtual void ext__ivy__add_base_conversion(cpp__structdecl& s);
    virtual void ext__cpp__simpletype__encode(const cpp__simpletype& s, pretty& b, int prio);
    virtual ivyc_s1::cpp__expr ext__ivy__symbol__to_cpp(const ivy__symbol& s, ivy__tocppst& st);
    virtual pstate ext__pstate__make(const str& s);
    virtual void ext__ivy__strident__encode(const ivy__strident& s, pretty& b, int prio);
    virtual void ext__cpp__breakst__encode(const cpp__breakst& s, pretty& b, int prio);
    virtual ivyc_s1::ivy__expr ext__ivy__includedc__get_expr(const ivy__includedc& s);
    virtual ivy__verb ext__ivy__app__app_verb(const ivy__app& s);
    virtual ivy__not_first_order ext__ivy__not_first_order__make(ivyc_s1::ivy__expr e, ivyc_s1::ivy__expr t1);
    virtual vector__pretty__token__ ext__vector__pretty__token____empty();
    virtual void ext__ivy__decl__record_prototypes(ivyc_s1::ivy__decl s, ivy__tocppst& st);
    virtual ivyc_s1::ivy__ident ext__ivy__ident__flat(ivyc_s1::ivy__ident s, bool rhs, const ivy__flatst& st);
    virtual void ext__ivy__type_context__set(ivy__type_context& s, ivyc_s1::ivy__expr typing);
    virtual ivy__verb ext__ivy__expr__app_verb(ivyc_s1::ivy__expr s);
    virtual ivyc_s1::cpp__stmt ext__ivy__stmt__to_cpp(ivyc_s1::ivy__stmt s, ivy__tocppst& st);
    virtual ivy__wrong_number_params ext__ivy__wrong_number_params__make(unsigned long long n);
    virtual void ext__cpp__version__encode(const cpp__version& s, pretty& b);
    virtual ivyc_s1::cpp__expr ext__cpp__symbol__make(ivyc_s1::cpp__ident name, ivyc_s1::annot ann);
    virtual vector__cpp__expr__ ext__cpp__app__get_args(const cpp__app& s);
    virtual ivy__ident_to_ident ext__ivy__prm_map(const vector__ivy__expr__& fml, const vector__ivy__expr__& act, ivyc_s1::annot ann);
    virtual ivyc_s1::ivy__expr ext__ivy__get_dom0(ivyc_s1::ivy__expr ty);
    virtual void ext__annot_i__encode(const annot_i& s, pretty& b);
    virtual ivyc_s1::ivy__stmt ext__ivy__whilest__flat(const ivy__whilest& s, ivy__flatst& st);
    virtual bool ext__ivy__expr__has_numident(ivyc_s1::ivy__expr e);
    virtual void ext__vector__ivy__access_path____append(vector__ivy__access_path__& a, const ivy__access_path& v);
    virtual bool ext__ivy__ident_set__mem(const ivy__ident_set& a, ivyc_s1::ivy__ident x);
    virtual unsigned long long ext__vector__cpp__simpletype____domain__next(unsigned long long x);
    virtual ivy__strident ext__ivy__dotident__get_last(const ivy__dotident& s);
    virtual void ext__cpp__sequence__encode(const cpp__sequence& s, pretty& b, int prio);
    virtual vector__ivy__expr__ ext__ivy__expr__get_args(ivyc_s1::ivy__expr s);
    virtual ivyc_s1::annot ext__cpp__vardecl__get_ann(const cpp__vardecl& d);
    virtual ivyc_s1::ivy__stmt ext__ivy__sequence__fold_right(const vector__ivy__stmt__& args, ivyc_s1::annot ann);
    virtual vector__ivy__expr__ ext__vector__ivy__expr____empty();
    virtual ivyc_s1::ivy__expr ext__ivy__symbol__reduce(const ivy__symbol& s, const ivy__symeval& smap);
    virtual ivyc_s1::ivy__stmt ext__ivy__decl__get_body(ivyc_s1::ivy__decl s);
    virtual bool ext__cpp__app__is(const cpp__app& s, cpp__verb vrb);
    virtual ivy__strident ext__ivy__ident__get_last(ivyc_s1::ivy__ident s);
    virtual ivyc_s1::ivy__expr ext__ivy__symbol__makestr(const str& name, ivyc_s1::annot ann);
    virtual void ext__ivy__typespec__to_destrs(ivyc_s1::ivy__typespec s, ivy__flatst& st, ivyc_s1::ivy__expr ty);
    virtual vector__ivy__expr__ ext__ivy__app__get_args(const ivy__app& s);
    virtual ivyc_s1::cpp__decl ext__ivy__header__to_cpp(const ivy__header& s, ivy__tocppst& st);
    virtual ivyc_s1::annot ext__ivy__skipst__get_ann(const ivy__skipst& s);
    virtual bool ext__ivy__local_tracker__mem(const ivy__local_tracker& s, ivyc_s1::ivy__ident id);
    virtual void ext__ivy__add_eq_pred(cpp__structdecl& s);
    virtual ivyc_s1::ivy__stmt ext__ivy__stmt__typeinfer(ivyc_s1::ivy__stmt s, ivy__typeinferst& st);
    virtual void ext__ivy__error__encode(ivyc_s1::ivy__error e, pretty& b);
    virtual ivyc_s1::ivy__expr ext__ivy__stmt__get_expr(ivyc_s1::ivy__stmt s);
    virtual void ext__ivy__decl__defd(ivyc_s1::ivy__decl s, ivy__flatst& st);
    virtual ivyc_s1::ivy__expr ext__ivy__expr__curry(ivyc_s1::ivy__expr ty);
    virtual void ext__cpp__vardecl__encode(const cpp__vardecl& s, pretty& b, int prio);
    virtual bool ext__ivy__expr__occurs(ivyc_s1::ivy__expr e, ivyc_s1::ivy__ident n);
    virtual void ext__vector__ivy__lvalue_count____set(vector__ivy__lvalue_count__& a, unsigned long long x, const ivy__lvalue_count& y);
    virtual void ext__vector__pretty__state____append(vector__pretty__state__& a, const pretty__state& v);
    virtual ivyc_s1::annot ext__ivy__expr__get_ann(ivyc_s1::ivy__expr s);
    virtual void imp__ivy__decost__typeinf_show_str(const str& s);
    virtual ivyc_s1::ivy__expr ext__ivy__symbol__make(ivyc_s1::ivy__ident name, ivyc_s1::annot ann);
    virtual void ext__ivy__tocppst__wrap_stmt(ivy__tocppst& s, ivyc_s1::cpp__stmt code, ivyc_s1::annot ann, ivyc_s1::cpp__stmt& res);
    virtual void ext__cpp__functype__encode(const cpp__functype& s, pretty& b, int prio);
    virtual void ext__ivy__write_file(const str& name, const str& buf);
    virtual ivyc_s1::cpp__expr ext__ivy__make_from_string(ivyc_s1::cpp__expr ty, ivyc_s1::cpp__expr arg, ivyc_s1::annot ann);
    virtual ivyc_s1::cpp__stmt ext__ivy__ifst__to_cpp(const ivy__ifst& s, ivy__tocppst& st);
    virtual ivyc_s1::ivy__decl ext__ivy__initdc__typeinfer(const ivy__initdc& s, ivy__typeinferst& st);
    virtual void ext__ivy__lvalue_path(ivyc_s1::ivy__expr s, ivy__access_path& path, bool& ok);
    virtual ivyc_s1::annot ext__annot__strip(ivyc_s1::annot s);
    virtual void ext__cpp__ifst__encode(const cpp__ifst& s, pretty& b, int prio);
    virtual void ext__ivy__syntax_error__encode(const ivy__syntax_error& e, pretty& b);
    virtual void ext__vector__ivy__ident____append(vector__ivy__ident__& a, ivyc_s1::ivy__ident v);
    virtual void ext__cpp__prog__encode(const cpp__prog& s, pretty& b, int prio);
    virtual bool ext__ivy__expr__is_typed(ivyc_s1::ivy__expr s, ivy__verb vrb);
    virtual bool ext__ivy__ident_to_cppclass__mem(const ivy__ident_to_cppclass& a, ivyc_s1::ivy__ident x);
    virtual ivyc_s1::cpp__ident ext__cpp__ident__get_member(ivyc_s1::cpp__ident s);
    virtual vector__str__ ext__vector__str____empty();
    virtual void ext__cpp__simpletype__tup__encode(const vector__cpp__simpletype__& s, pretty& b, int prio);
    virtual unsigned long long ext__vector__ivy__decl____domain__prev(unsigned long long x);
    virtual ivy__sequence ext__ivy__sequence__flat_int(const ivy__sequence& s, ivy__flatst& st);
    virtual bool ext__ivy__ident_to_instantiatedc__mem(const ivy__ident_to_instantiatedc& a, ivyc_s1::ivy__ident x);
    virtual void ext__ivy__unown_path(const ivy__access_path& path, ivy__tocppst& st);
    virtual ivyc_s1::cpp__stmt ext__cpp__asgn__make(ivyc_s1::cpp__expr x, ivyc_s1::cpp__expr y, ivyc_s1::annot ann);
    virtual void ext__ivy__instancedc__defd(const ivy__instancedc& s, ivy__flatst& st);
    virtual ivyc_s1::ivy__expr ext__ivy__flat_formal(ivyc_s1::ivy__expr s, ivy__flatst& st);
    virtual ivyc_s1::ivy__decl ext__ivy__groupdc__make(const vector__ivy__decl__& decls);
    virtual ivy__global_types ext__ivy__prog__get_global_types(const ivy__prog& p, bool curried);
    virtual vector__ivy__expr__ ext__ivy__typespec__get_elems(ivyc_s1::ivy__typespec s);
    virtual ivyc_s1::annot ext__cpp__symbol__get_ann(const cpp__symbol& s);
    virtual ivyc_s1::ivy__ident ext__ivy__ident__get_namesp(ivyc_s1::ivy__ident s);
    virtual void imp__ivy__report_cannot_infer(const str& s1, const str& s2);
    virtual ivyc_s1::ivy__expr ext__ivy__app__get_arg(const ivy__app& s, unsigned long long p);
    virtual ivyc_s1::annot ext__cpp__typedecl__get_ann(const cpp__typedecl& d);
    virtual void ext__ivy__curly_tup__parse(pstate& st, int prio, vector__ivy__expr__& res);
    virtual bool ext__ivy__push_pop_ident_set__mem(const ivy__push_pop_ident_set& s, ivyc_s1::ivy__ident id);
    virtual ivyc_s1::ivy__expr ext__ivy__uncurry_func(ivyc_s1::ivy__expr func);
    virtual ivyc_s1::ivy__expr ext__ivy__app__flat(const ivy__app& s, ivy__flatst& st);
    virtual ivyc_s1::ivy__expr ext__ivy__get_app(ivyc_s1::ivy__expr s, vector__ivy__expr__& args);
    virtual void ext__ivy__ident_set__get(const ivy__ident_set& a, ivyc_s1::ivy__ident x, bool& y);
    virtual void ext__ivy__add_virtual_destructor(cpp__structdecl& s);
    virtual void ext__ivy__local_tracker__push_stmt(ivy__local_tracker& s, ivyc_s1::ivy__stmt stm);
    virtual ivyc_s1::ivy__expr ext__ivy__applydot(ivyc_s1::ivy__expr arg, ivyc_s1::ivy__ident member, ivyc_s1::annot ann, const ivy__flatst& st);
    virtual ivyc_s1::ivy__stmt ext__ivy__asgn__typeinfer_desugar(const ivy__asgn& s, bool desugar, ivy__typeinferst& st);
    virtual vector__ivy__lvalue_count__ ext__vector__ivy__lvalue_count____empty();
    virtual ivy__header ext__ivy__header__flat_int(const ivy__header& s, ivy__flatst& st);
    virtual vector__cpp__expr__ ext__cpp__expr__get_args(ivyc_s1::cpp__expr s);
    virtual ivy__vardc ext__ivy__vardc__typeinfer_int(const ivy__vardc& s, ivy__typeinferst& st);
    virtual ivyc_s1::cpp__expr ext__ivy__fix_variant_type(ivyc_s1::ivy__expr t, ivy__tocppst& st);
    virtual unsigned long long ext__vector__pretty__token____domain__next(unsigned long long x);
    virtual ivy__prototype ext__ivy__actdc__get_proto(const ivy__actdc& s);
    virtual ivy__initdc ext__ivy__initdc__flat_int(const ivy__initdc& s, ivy__flatst& st);
    virtual ivy__instantiatedc ext__ivy__find_auto_inst(ivyc_s1::ivy__ident id, const ivy__flatst& st, bool& ok);
    virtual void ext__ivy__bottom_up_type(ivyc_s1::ivy__expr& e, const ivy__typeinferst& st, bool& ok);
    virtual ivyc_s1::annot ext__cpp__funcdecl__get_ann(const cpp__funcdecl& d);
    virtual void ext__ivy__strident__parse(pstate& st, ivy__strident& id);
    virtual ivyc_s1::ivy__stmt ext__ivy__sequence__make(ivyc_s1::ivy__stmt x, ivyc_s1::ivy__stmt y, ivyc_s1::annot ann);
    virtual bool ext__ivy__expr__eq(ivyc_s1::ivy__expr e1, ivyc_s1::ivy__expr e2);
    virtual void ext__ivy__ident_to_moduledc__set(ivy__ident_to_moduledc& a, ivyc_s1::ivy__ident x, const ivy__moduledc& y);
    virtual void ext__ivy__local_tracker__pop(ivy__local_tracker& s);
    virtual ivyc_s1::ivy__expr ext__ivy__expr__get_type(ivyc_s1::ivy__expr s);
    virtual void ext__vector__cpp__ident____append(vector__cpp__ident__& a, ivyc_s1::cpp__ident v);
    virtual bool ext__ivy__is_subtype(ivyc_s1::ivy__expr rhsty, ivyc_s1::ivy__expr lhsty, const ivy__typeinferst& st);
    virtual void ext__ivy__tocppst__add_member(ivy__tocppst& s, ivyc_s1::ivy__ident namesp, ivyc_s1::ivy__decl member);
    virtual ivyc_s1::ivy__expr ext__ivy__expr__get_arg(ivyc_s1::ivy__expr s, unsigned long long p);
    virtual ivy__vardc ext__ivy__vardc__flat_int(const ivy__vardc& s, ivy__flatst& st);
    virtual void ext__ivy__ident_to_cppclass__set(ivy__ident_to_cppclass& a, ivyc_s1::ivy__ident x, ivyc_s1::ivy__expr y);
    virtual bool ext__ivy__symbol__occurs(const ivy__symbol& e, ivyc_s1::ivy__ident n);
    virtual void ext__ivy__auto_flat_rec(ivyc_s1::ivy__expr s, ivy__flatst& st);
    virtual unsigned long long ext__vector__ivy__stmt____domain__prev(unsigned long long x);
    virtual void ext__ivy__make_cast(ivyc_s1::ivy__expr lhsty, ivyc_s1::ivy__expr& rhs, const ivy__typeinferst& st);
    virtual void ext__ivy__objectdc__flat(const ivy__objectdc& s, ivy__flatst& st);
    virtual ivyc_s1::cpp__stmt ext__cpp__ifst__make(ivyc_s1::cpp__expr cond, ivyc_s1::cpp__stmt thenst, ivyc_s1::cpp__stmt elsest, ivyc_s1::annot ann);
    virtual void ext__cpp__numident__encode(const cpp__numident& s, pretty& b, int prio);
    virtual ivyc_s1::ivy__ident ext__ivy__numident__make(unsigned long long val);
    virtual ivy__verb ext__ivy__verb_from_name(const str& name);
    virtual str ext__ivy__strident__to_str(const ivy__strident& s);
    virtual void ext__ivy__untyped__encode(const ivy__untyped& e, pretty& b);
    virtual ivy__moduledc ext__ivy__ident_to_moduledc__get_def(const ivy__ident_to_moduledc& m, ivyc_s1::ivy__ident x, ivyc_s1::annot ann);
    virtual void ext__parse_error(unsigned long long p, const str& tok);
    virtual ivyc_s1::ivy__expr ext__ivy__varv__make(ivyc_s1::ivy__expr arg, ivyc_s1::annot ann);
    virtual void ext__ivy__auto_defd_rec(ivyc_s1::ivy__expr s, ivy__flatst& st);
    virtual ivyc_s1::cpp__ident ext__cpp__strident__make1(const str& val, ivyc_s1::cpp__ident arg);
    virtual void ext__ivy__objectdc__defd(const ivy__objectdc& s, ivy__flatst& st);
    virtual void ext__vector__ivy__expr____reverse(vector__ivy__expr__& a);
    virtual cpp__strident ext__ivy__strident_to_cpp(const ivy__strident& s, bool native);
    virtual void ext__vector__cpp__simpletype____append(vector__cpp__simpletype__& a, const cpp__simpletype& v);
    virtual ivyc_s1::ivy__expr ext__ivy__times__fold_left(const vector__ivy__expr__& args, ivyc_s1::annot ann);
    virtual ivyc_s1::ivy__expr ext__ivy__symbol__type_fill_in(const ivy__symbol& e, ivy__decost& st);
    virtual void ext__cpp__expr__encode(ivyc_s1::cpp__expr s, pretty& b, int prio);
    virtual void ext__cpp__funcdecl__encode(const cpp__funcdecl& s, pretty& b, int prio);
    virtual void ext__cpp__pi__encode(const cpp__pi& s, pretty& b, int prio);
    virtual ivyc_s1::cpp__expr ext__ivy__expr__to_cpp(ivyc_s1::ivy__expr s, ivy__tocppst& st);
    virtual void ext__cpp__groupdc__encode(const cpp__groupdc& s, pretty& b, int prio);
    virtual ivyc_s1::cpp__ident ext__cpp__strident__make(const str& val);
    virtual ivyc_s1::ivy__ident ext__ivy__strident__make(const str& val);
    virtual ivyc_s1::cpp__expr ext__cpp__comma__fold_left(const vector__cpp__expr__& args, ivyc_s1::annot ann);
    virtual void ext__cpp__ident__encode(ivyc_s1::cpp__ident s, pretty& b, int prio);
    virtual ivyc_s1::ivy__expr ext__ivy__asgn__get_rhs(const ivy__asgn& s);
    virtual void ext__vector__pos____append(vector__pos__& a, unsigned long long v);
    virtual void ext__ivy__file__read(const str& fname, str& b, bool& ok);
    virtual void ext__ivy__app__encode(const ivy__app& s, pretty& b, int prio);
    virtual ivyc_s1::ivy__stmt ext__ivy__ifst__typeinfer(const ivy__ifst& s, ivy__typeinferst& st);
    virtual void ext__ivy__typespec__defd(ivyc_s1::ivy__typespec s, ivy__flatst& st, ivyc_s1::ivy__ident id);
    virtual void ext__get_annot(pstate& st);
    virtual bool ext__ivy__is_cpp_this(ivyc_s1::cpp__expr s);
    virtual ivyc_s1::ivy__expr ext__ivy__decl__get_expr(ivyc_s1::ivy__decl s);
    virtual ivyc_s1::annot ext__ivy__app__get_ann(const ivy__app& s);
    virtual ivyc_s1::ivy__expr ext__ivy__asgn__get_lhs(const ivy__asgn& s);
    virtual bool ext__ivy__push_pop_ident_set__map_t__mem(const ivy__push_pop_ident_set__map_t& a, ivyc_s1::ivy__ident x);
    virtual ivy__untyped ext__ivy__untyped__make(ivyc_s1::ivy__expr e, ivyc_s1::ivy__expr t1);
    virtual str ext__cpp__ident__to_str(ivyc_s1::cpp__ident s);
    virtual void ext__ivy__type_conversion__encode(const ivy__type_conversion& e, pretty& b);
    virtual ivy__verb ext__ivy__strident__get_verb(const ivy__strident& s);
    virtual void ext__pretty__newline(pretty& self);
    virtual void ext__ivy__subst_vector(vector__ivy__expr__& v, const ivy__symeval& smap);
    virtual ivyc_s1::ivy__expr ext__ivy__expr__dec(const str& s);
    virtual void ext__ivy__prog__parse_to(pstate& st, int prio, ivy__prog& res);
    virtual ivy__ifst ext__ivy__ifst__typeinfer_int(const ivy__ifst& s, ivy__typeinferst& st);
    virtual ivyc_s1::ivy__decl ext__ivy__instantiatedc__make(ivyc_s1::ivy__expr name, const vector__ivy__expr__& prms, ivyc_s1::annot ann);
    virtual void ext__skip_space(pstate& st);
    virtual ivyc_s1::cpp__stmt ext__cpp__varst__make(ivyc_s1::cpp__expr _type, ivyc_s1::cpp__expr name, ivyc_s1::annot ann);
    virtual ivyc_s1::cpp__decl ext__ivy__actdc__to_cpp(const ivy__actdc& s, ivy__tocppst& st);
    virtual void ext__ivy__vardc__build_global_types(const ivy__vardc& s, ivy__global_types& st);
    virtual bool ext__ivy__is_variant_type(ivyc_s1::ivy__expr t, const ivy__tocppst& st);
    virtual void ext__pretty__extend(pretty& self, const str& string);
    virtual cpp__header ext__ivy__header__to_cpp_int(const ivy__header& s, ivy__tocppst& st);
    virtual ivyc_s1::annot ext__ivy__asgn__get_ann(const ivy__asgn& s);
    virtual void ext__ivy__make_temp(ivy__tocppst& s, ivyc_s1::ivy__expr ty, ivyc_s1::annot ann, ivyc_s1::cpp__expr& res);
    virtual void ext__ivy__enumspec__defd(const ivy__enumspec& s, ivy__flatst& st, ivyc_s1::ivy__ident id);
    virtual unsigned long long ext__pos__prev(unsigned long long x);
    virtual void ext__ivy__member_name(ivyc_s1::cpp__expr& s);
    virtual void ext__ivy__decl__flat(ivyc_s1::ivy__decl s, ivy__flatst& st);
    virtual ivyc_s1::ivy__expr ext__ivy__expr__uncurry(ivyc_s1::ivy__expr ty);
    virtual ivyc_s1::cpp__expr ext__ivy__make_std_tpl(const str& tpl, const str& ty, ivyc_s1::annot ann);
    virtual void ext__cpp__skipst__encode(const cpp__skipst& s, pretty& b, int prio);
    virtual void ext__ivy__instancedc__flat(const ivy__instancedc& s, ivy__flatst& st);
    virtual bool ext__ivy__func_is_member(ivyc_s1::ivy__expr func);
    virtual void ext__ivy__vardc__defd(const ivy__vardc& s, ivy__flatst& st);
    virtual cpp__verb ext__cpp__symbol__get_verb(const cpp__symbol& s);
    virtual str ext__pos__to_str(unsigned long long num);
    virtual void ext__ivy__report_cannot_infer(const str& s1, const str& s2);
    virtual ivyc_s1::ivy__expr ext__ivy__dot__make(ivyc_s1::ivy__expr lhs, ivyc_s1::ivy__expr rhs, ivyc_s1::annot ann);
    virtual void ext__vector__str____append(vector__str__& a, const str& v);
    virtual bool ext__ivy__actdc__is_member(const ivy__actdc& s);
    virtual ivyc_s1::ivy__decl ext__ivy__objectdc__make(ivyc_s1::ivy__expr name, ivyc_s1::ivy__decl body, ivyc_s1::annot ann);
    virtual void ext__ivy__kill_lvalue(ivyc_s1::ivy__expr e, ivy__tocppst& st, const vector__ivy__access_path__& paths);
    virtual void ext__ivy__actdc__defd(const ivy__actdc& s, ivy__flatst& st);
    virtual void ext__ivy__canon_typing(ivyc_s1::ivy__expr& typing);
    virtual bool ext__ivy__app__has_numident(const ivy__app& s);
    virtual void ext__ivy__find_ident(ivyc_s1::ivy__ident root, ivyc_s1::ivy__ident& s, const ivy__flatst& st);
    virtual ivyc_s1::ivy__ident ext__ivy__dotident__make(ivyc_s1::ivy__ident namesp, const ivy__strident& member);
    virtual void ext__ivy__prog__typeinfer(ivy__prog& p);
    virtual void ext__ivy__decl__reg_member(ivyc_s1::ivy__decl s, ivy__tocppst& st);
    virtual void ext__ivy__not_first_order__encode(const ivy__not_first_order& e, pretty& b);
    virtual ivyc_s1::cpp__decl ext__ivy__vardc__to_cpp(const ivy__vardc& s, ivy__tocppst& st);
    virtual ivyc_s1::ivy__expr ext__ivy__varst__get_expr(const ivy__varst& s);
    virtual ivyc_s1::cpp__expr ext__ivy__call_to_cpp(ivyc_s1::ivy__expr func, const vector__ivy__expr__& inputs, ivyc_s1::annot ann, ivy__tocppst& st);
    virtual void ext__cpp__curly_tup__encode(const vector__cpp__expr__& s, pretty& b, int prio);
    virtual void ext__ivy__decl__parse(pstate& st, int prio, ivyc_s1::ivy__decl& res);
    virtual void ext__ivy__cannot_infer(ivyc_s1::ivy__expr e, ivyc_s1::ivy__expr t);
    virtual vector__ivy__expr__ ext__ivy__enumspec__get_elems(const ivy__enumspec& s);
    virtual ivyc_s1::cpp__stmt ext__ivy__sequence__to_cpp(const ivy__sequence& s, ivy__tocppst& st);
    virtual unsigned long long ext__vector__cpp__decl____domain__next(unsigned long long x);
    virtual void ext__cpp__sequence__encode_int(const cpp__sequence& s, pretty& b, int prio);
    virtual str ext__ivy__dotident__to_str(const ivy__dotident& s);
    virtual ivyc_s1::ivy__ident ext__ivy__ident__prefix(ivyc_s1::ivy__ident s, ivyc_s1::ivy__ident pref);
    virtual ivyc_s1::cpp__expr ext__ivy__function_type(ivyc_s1::ivy__expr ty, ivy__tocppst& st);
    virtual bool ext__ivy__is_dead(ivyc_s1::cpp__expr e, const ivy__tocppst& st, unsigned long long cnt);
    virtual ivyc_s1::ivy__ident ext__ivy__strident__flat(const ivy__strident& s, bool rhs, const ivy__flatst& st);
    virtual ivyc_s1::ivy__typespec ext__ivy__enumspec__flat(const ivy__enumspec& s, ivy__flatst& st);
    virtual ivyc_s1::cpp__expr ext__cpp__plus__fold_left(const vector__cpp__expr__& args, ivyc_s1::annot ann);
    virtual void ext__ivy__tocppst__get_code(ivy__tocppst& s, ivyc_s1::annot ann, ivyc_s1::cpp__stmt& res);
    virtual void ext__ivy__report_error(ivyc_s1::ivy__error e, ivyc_s1::annot ann);
    virtual unsigned long long ext__vector__ivy__decl____domain__next(unsigned long long x);
    virtual ivyc_s1::ivy__stmt ext__ivy__skipst__make(ivyc_s1::annot ann);
    virtual unsigned long long ext__vector__ivy__stmt____domain__next(unsigned long long x);
    virtual void ext__ivy__typedc__reg_member(const ivy__typedc& s, ivy__tocppst& st);
    virtual ivy__initdc ext__ivy__initdc__typeinfer_int(const ivy__initdc& s, ivy__typeinferst& st);
    virtual void ext__ivy__elidest__map__set(ivy__elidest__map& a, ivyc_s1::ivy__ident x, bool y);
    virtual void ext__ivy__type_clash__encode(const ivy__type_clash& e, pretty& b);
    virtual void ext__ivy__set_root(ivy__flatst& st, ivyc_s1::ivy__expr s);
    virtual pretty ext__pretty__make(unsigned long long maxline, unsigned long long indent);
    virtual cpp__skipst ext__ivy__skipst__to_cpp_int(const ivy__skipst& s, ivy__tocppst& st);
    virtual ivyc_s1::cpp__expr ext__cpp__decl__get_type(ivyc_s1::cpp__decl d);
    virtual void ext__vector__ivy__decl____set(vector__ivy__decl__& a, unsigned long long x, ivyc_s1::ivy__decl y);
    virtual ivy__file_not_found ext__ivy__file_not_found__make(const str& n);
    virtual void ext__ivy__decost__newvar(ivy__decost& s, ivyc_s1::annot ann, ivyc_s1::ivy__expr& res);
    virtual void ext__cpp__varst__encode(const cpp__varst& s, pretty& b, int prio);
    virtual void ext__ivy__add_namespaces(ivyc_s1::cpp__decl& d, ivyc_s1::ivy__ident id);
    virtual void ext__cpp__structdecl__encode(const cpp__structdecl& s, pretty& b, int prio);
    virtual vector__ivy__ident__ ext__ivy__setup_local_vars(ivyc_s1::ivy__stmt s, ivy__flatst& st);
    virtual void ext__ivy__flat_exprvec(vector__ivy__expr__& es, ivy__flatst& st);
    virtual void ext__ivy__typedc__flat(const ivy__typedc& s, ivy__flatst& st);
    virtual ivyc_s1::cpp__ident ext__cpp__dotident__make(ivyc_s1::cpp__ident namesp, const cpp__strident& member);
    virtual ivyc_s1::ivy__decl ext__ivy__instancedc__desugar(const ivy__instancedc& s);
    virtual ivyc_s1::ivy__expr ext__ivy__symbol__type_elide_int(const ivy__symbol& e, bool b, const ivy__symeval& m, ivy__elidest& st);
    virtual ivyc_s1::cpp__expr ext__ivy__native_type_to_cpp(ivyc_s1::ivy__expr ty, ivy__tocppst& st);
    virtual void ext__ivy__auto_instance_defd(const ivy__instancedc& s, ivy__flatst& st);
    virtual void ext__ivy__range_type(ivyc_s1::ivy__expr& s);
    virtual ivyc_s1::cpp__expr ext__cpp__comma__make(ivyc_s1::cpp__expr lhs, ivyc_s1::cpp__expr rhs, ivyc_s1::annot ann);
    virtual ivy__whilest ext__ivy__whilest__typeinfer_int(const ivy__whilest& s, ivy__typeinferst& st);
    virtual unsigned long long ext__vector__str____domain__next(unsigned long long x);
    virtual ivyc_s1::ivy__expr ext__ivy__comma__fold_left(const vector__ivy__expr__& args, ivyc_s1::annot ann);
    virtual ivyc_s1::ivy__ident ext__ivy__actdc__member_type(const ivy__actdc& s);
    virtual ivyc_s1::ivy__decl ext__ivy__vardc__func_to_action(const ivy__vardc& s);
    virtual str ext__annot_i__to_str(const annot_i& s);
    virtual void ext__cpp__app__encode(const cpp__app& s, pretty& b, int prio);
    virtual ivyc_s1::ivy__expr ext__ivy__arrow__make(ivyc_s1::ivy__expr lhs, ivyc_s1::ivy__expr rhs, ivyc_s1::annot ann);
    virtual ivyc_s1::ivy__expr ext__ivy__symbol__flat(const ivy__symbol& s, ivy__flatst& st);
    virtual cpp__funcdecl ext__ivy__make_virt_destr(const cpp__structdecl& t);
    virtual vector__ivy__expr__ ext__ivy__structspec__get_elems(const ivy__structspec& s);
    virtual ivyc_s1::cpp__expr ext__cpp__app__make(ivyc_s1::cpp__expr func, const vector__cpp__expr__& args, ivyc_s1::annot ann);
    virtual ivy__decost ext__ivy__decost__make();
    virtual ivyc_s1::cpp__stmt ext__ivy__asgn__to_cpp(const ivy__asgn& s, ivy__tocppst& st);
    virtual void ext__cpp__ifst__encode_int(const cpp__ifst& s, pretty& b, int prio);
    virtual void ext__ivy__vardc__reg_member(const ivy__vardc& s, ivy__tocppst& st);
    virtual void ext__ivy__ident_set__remove(ivy__ident_set& a, ivyc_s1::ivy__ident x);
    virtual ivyc_s1::ivy__expr ext__ivy__expr__reduce(ivyc_s1::ivy__expr e, const ivy__symeval& smap);
    virtual void ext__ivy__flat_formalvec(vector__ivy__expr__& es, ivy__flatst& st);
    virtual ivyc_s1::cpp__ident ext__ivy__dotident__to_cpp(const ivy__dotident& s, bool native);
    virtual ivyc_s1::ivy__ident ext__ivy__dotident__get_member(const ivy__dotident& s);
    virtual ivyc_s1::cpp__expr ext__ivy__upcast(ivyc_s1::ivy__expr lhsty, ivyc_s1::ivy__expr rhs, ivy__tocppst& st);
    virtual bool ext__ivy__file__write(const str& fname, const str& b);
    virtual void ext__ivy__actdc__flat(const ivy__actdc& s, ivy__flatst& st);
    virtual ivyc_s1::cpp__expr ext__cpp__empty__make(ivyc_s1::annot ann);
    virtual ivyc_s1::ivy__stmt ext__ivy__asgn__flat(const ivy__asgn& s, ivy__flatst& st);
    virtual vector__ivy__expr__ ext__ivy__times__unfold_left(ivyc_s1::ivy__expr s);
    virtual void ext__ivy__decost__unification_failed(ivy__decost& st, ivyc_s1::ivy__expr x, ivyc_s1::ivy__expr y);
    virtual ivyc_s1::ivy__ident ext__ivy__formal_ident(ivyc_s1::ivy__expr s);
    virtual void ext__vector__pretty__token____append(vector__pretty__token__& a, const pretty__token& v);
    virtual void ext__ivy__add_is_zero_pred(cpp__structdecl& s);
    virtual ivyc_s1::annot ext__cpp__decl__get_ann(ivyc_s1::cpp__decl d);
    virtual ivy__actdc ext__ivy__actdc__flat_int(const ivy__actdc& s, ivy__flatst& st);
    virtual void ext__ivy__decl__build_global_types(ivyc_s1::ivy__decl s, ivy__global_types& st);
    virtual unsigned long long ext__vector__cpp__stmt____domain__prev(unsigned long long x);
    virtual void ext__ivy__fix_variant_arg(ivyc_s1::ivy__expr s, ivyc_s1::cpp__expr& rhs, const ivy__tocppst& st);
    virtual void ext__ivy__add_def(ivyc_s1::ivy__expr s, ivy__flatst& st, bool is_global);
    virtual vector__ivy__stmt__ ext__ivy__desugar_asgn(ivyc_s1::ivy__stmt& s);
    virtual void ext__vector__ivy__ident____set(vector__ivy__ident__& a, unsigned long long x, ivyc_s1::ivy__ident y);
    virtual ivyc_s1::ivy__expr ext__ivy__expr__flat(ivyc_s1::ivy__expr s, ivy__flatst& st);
    virtual void ext__ivy__wrong_number_params__encode(const ivy__wrong_number_params& e, pretty& b);
    virtual void ext__cpp__whilest__encode(const cpp__whilest& s, pretty& b, int prio);
    virtual ivyc_s1::annot ext__cpp__structdecl__get_ann(const cpp__structdecl& d);
    virtual void ext__vector__cpp__expr____append(vector__cpp__expr__& a, ivyc_s1::cpp__expr v);
    virtual void ext__ivy__decl__build_subtypes(ivyc_s1::ivy__decl s, ivy__subtypes& st);
    virtual void ext__vector__ivy__lvalue_count____append(vector__ivy__lvalue_count__& a, const ivy__lvalue_count& v);
    virtual vector__ivy__decl__ ext__vector__ivy__decl____empty();
    virtual ivyc_s1::annot ext__cpp__expr__get_ann(ivyc_s1::cpp__expr s);
    virtual cpp__funcdecl ext__ivy__make_cpp_cons(const cpp__structdecl& t);
    virtual ivyc_s1::cpp__stmt ext__ivy__varst__to_cpp(const ivy__varst& s, ivy__tocppst& st);
    virtual unsigned long long ext__pos__from_str(const str& x);
    virtual void ext__ivy__push_pop_ident_set__vec_t__append(ivy__push_pop_ident_set__vec_t& a, ivyc_s1::ivy__ident v);
    virtual void ext__vector__cpp__expr____set(vector__cpp__expr__& a, unsigned long long x, ivyc_s1::cpp__expr y);
    virtual ivyc_s1::annot ext__ivy__ifst__get_ann(const ivy__ifst& s);
    virtual ivyc_s1::cpp__stmt ext__cpp__skipst__make(ivyc_s1::annot ann);
    virtual void ext__lex(pstate& st);
    virtual void ext__vector__ivy__type_context__stack_entry____pop_back(vector__ivy__type_context__stack_entry__& a);
    virtual ivy__param_map ext__ivy__param_set(const vector__ivy__expr__& ps);
    virtual void ext__cpp__symbol__encode(const cpp__symbol& s, pretty& b, int prio);
    virtual void ext__ivy__ident_to_moduledc__get(const ivy__ident_to_moduledc& a, ivyc_s1::ivy__ident x, ivy__moduledc& y);
    virtual str ext__ivy__testelide(const str& inp);
    virtual void ext__ivy__push_pop_ident_set__map_t__set(ivy__push_pop_ident_set__map_t& a, ivyc_s1::ivy__ident x, bool y);
    virtual void ext__ivy__decost__find(ivy__decost& st, ivyc_s1::ivy__expr x, ivyc_s1::ivy__expr& res);
    virtual ivyc_s1::cpp__expr ext__cpp__app__make0(ivyc_s1::cpp__expr func, ivyc_s1::annot ann);
    virtual ivyc_s1::cpp__expr ext__cpp__app__make1(ivyc_s1::cpp__expr func, ivyc_s1::cpp__expr arg0, ivyc_s1::annot ann);
    virtual void ext__vector__cpp__stmt____append(vector__cpp__stmt__& a, ivyc_s1::cpp__stmt v);
    virtual vector__cpp__stmt__ ext__vector__cpp__stmt____empty();
    virtual void ext__ivy__ident_to_declvec__set(ivy__ident_to_declvec& a, ivyc_s1::ivy__ident x, const vector__ivy__decl__& y);
    virtual bool ext__ivy__actdc__emitted(const ivy__actdc& s, const ivy__tocppst& st);
    virtual void ext__ivy__type_infer_known(ivyc_s1::ivy__expr& e, ivyc_s1::ivy__expr ty, const ivy__symeval& tc);
    virtual void ext__ivy__numident__encode(const ivy__numident& s, pretty& b, int prio);
    virtual void ext__ivy__symeval__remove(ivy__symeval& a, ivyc_s1::ivy__ident x);
    virtual ivy__subtypes ext__ivy__prog__get_subtypes(const ivy__prog& p);
    virtual ivyc_s1::ivy__ident ext__ivy__symbol__get_name(const ivy__symbol& s);
    virtual void ext__str__append(str& a, int v);
    virtual ivyc_s1::ivy__ident ext__ivy__dotident__flat(const ivy__dotident& s, bool rhs, const ivy__flatst& st);
    virtual ivyc_s1::ivy__stmt ext__ivy__stmt__typeinfer_desugar(ivyc_s1::ivy__stmt s, bool desugar, ivy__typeinferst& st);
    virtual void ext__ivy__add_namespaces_rec(ivyc_s1::cpp__decl& d, ivyc_s1::ivy__ident id);
    virtual void ext__ivy__interpdc__flat(const ivy__interpdc& s, ivy__flatst& st);
    virtual bool ext__ivy__symeval__mem(const ivy__symeval& a, ivyc_s1::ivy__ident x);
    virtual void ext__ivy__type_unify_exprs(ivyc_s1::ivy__expr& e1, ivyc_s1::ivy__expr& e2, const ivy__symeval& tc);
    virtual ivyc_s1::ivy__expr ext__ivy__empty__make(ivyc_s1::annot ann);
    virtual ivy__prog ext__ivy__prog__read_file(const str& name);
    virtual ivyc_s1::ivy__stmt ext__ivy__ifst__flat(const ivy__ifst& s, ivy__flatst& st);
    virtual bool ext__ivy__ident_to_exprs__mem(const ivy__ident_to_exprs& a, ivyc_s1::ivy__ident x);
    virtual ivyc_s1::annot ext__cpp__header__get_ann(const cpp__header& d);
    virtual void ext__ivy__type_error(ivyc_s1::ivy__expr e, ivy__decost& st);
    virtual bool ext__ivy__file__exist(const str& fname);
    virtual ivyc_s1::cpp__expr ext__cpp__decl__get_name(ivyc_s1::cpp__decl d);
    virtual void ext__ivy__cannot_write__encode(const ivy__cannot_write& e, pretty& b);
    virtual ivy__asgn ext__ivy__asgn__flat_int(const ivy__asgn& s, ivy__flatst& st);
    virtual void ext__ivy__typedc__defd(const ivy__typedc& s, ivy__flatst& st);
    virtual void ext__ivy__fix_object_clash(ivyc_s1::ivy__ident& id, const ivy__tocppst& st);
    virtual void ext__pretty__unnest(pretty& self);
    virtual ivyc_s1::ivy__expr ext__ivy__expr__type_fill_in(ivyc_s1::ivy__expr e, ivy__decost& st);
    virtual void ext__pretty__print(pretty& self, const pretty__token& tok);
    virtual ivyc_s1::cpp__expr ext__cpp__vardecl__get_type(const cpp__vardecl& d);
    virtual void ext__pretty__flush(pretty& self);
    virtual bool ext__ivy__is_logvar_name(const str& name);
    virtual ivy__varst ext__ivy__varst__flat_int(const ivy__varst& s, ivy__flatst& st);
    virtual void ext__ivy__ident__encode(ivyc_s1::ivy__ident s, pretty& b, int prio);
    virtual ivy__verb ext__ivy__ident__get_verb(ivyc_s1::ivy__ident s);
    virtual ivyc_s1::ivy__ident ext__ivy__dotident__get_namesp(const ivy__dotident& s);
    virtual cpp__prog ext__ivy__prog__to_cpp(const ivy__prog& sp);
    virtual ivy__cannot_write ext__ivy__cannot_write__make(const str& n);
    virtual void ext__ivy__groupdc__flat(const ivy__groupdc& s, ivy__flatst& st);
    virtual ivyc_s1::annot ext__annot_i__strip(const annot_i& s);
    virtual void ext__cpp__enumdecl__encode(const cpp__enumdecl& s, pretty& b, int prio);
    virtual ivyc_s1::ivy__ident ext__ivy__dotident__prefix(const ivy__dotident& s, ivyc_s1::ivy__ident pref);
    virtual ivyc_s1::annot ext__cpp__app__get_ann(const cpp__app& s);
    virtual void ext__ivy__decost__map__get(const ivy__decost__map& a, ivyc_s1::ivy__ident x, ivyc_s1::ivy__expr& y);
    virtual void ext__ivy__decost__unify(ivy__decost& st, ivyc_s1::ivy__expr x0, ivyc_s1::ivy__expr y0);
    virtual void ext__cpp__header__encode(const cpp__header& s, pretty& b, int prio);
    virtual ivyc_s1::cpp__expr ext__cpp__namedtype(ivyc_s1::cpp__ident name, ivyc_s1::annot ann);
    virtual void ext__ivy__decl__parse_list(pstate& st, int prio, vector__ivy__decl__& res);
    virtual ivyc_s1::ivy__expr ext__ivy__comma__make(ivyc_s1::ivy__expr lhs, ivyc_s1::ivy__expr rhs, ivyc_s1::annot ann);
    virtual str ext__ivy__enum_name(ivyc_s1::cpp__expr name);
    virtual void ext__ivy__pi__encode(const ivy__pi& s, pretty& b, int prio);
    virtual void ext__ivy__expr__tup__encode(const vector__ivy__expr__& s, pretty& b, int prio);
    virtual cpp__funcdecl ext__ivy__make_upcast_method(const cpp__structdecl& t);
    virtual bool ext__ivy__param_map__mem(const ivy__param_map& a, ivyc_s1::ivy__ident x);
    virtual void ext__cpp__breakst__encode_int(const cpp__breakst& s, pretty& b, int prio);
    virtual unsigned long long ext__vector__cpp__expr____domain__next(unsigned long long x);
    virtual ivyc_s1::cpp__ident ext__ivy__ident__to_cpp(ivyc_s1::ivy__ident s, bool native);
    virtual unsigned long long ext__vector__ivy__ident____domain__next(unsigned long long x);
    virtual void ext__pstate__consume(pstate& st);
    virtual void ext__vector__ivy__stmt____append(vector__ivy__stmt__& a, ivyc_s1::ivy__stmt v);
    virtual void ext__ivy__expr__parse(pstate& st, int prio, ivyc_s1::ivy__expr& res);
    virtual unsigned long long ext__vector__ivy__lvalue_count____domain__next(unsigned long long x);
    virtual ivyc_s1::cpp__expr ext__ivy__full_action_name(ivyc_s1::ivy__expr name, bool is_member, ivy__tocppst& st);
    virtual void ext__ivy__add_numeric_cons(cpp__structdecl& s);
    virtual void ext__get_line(pstate& st, str& line);
    virtual void ext__ivy__symeval__get(const ivy__symeval& a, ivyc_s1::ivy__ident x, ivyc_s1::ivy__expr& y);
    virtual ivy__type_clash ext__ivy__type_clash__make(ivyc_s1::ivy__expr e, ivyc_s1::ivy__expr t1, ivyc_s1::ivy__expr t2);
    virtual ivy__ifst ext__ivy__ifst__flat_int(const ivy__ifst& s, ivy__flatst& st);
    virtual ivyc_s1::annot ext__ivy__whilest__get_ann(const ivy__whilest& s);
    virtual void ext__cpp__asgn__encode_int(const cpp__asgn& s, pretty& b, int prio);
    virtual ivyc_s1::cpp__expr ext__ivy__app__to_cpp(const ivy__app& s, ivy__tocppst& st);
    virtual void ext__ivy__unown_func_args(const vector__ivy__expr__& args, ivy__tocppst& st);
    virtual ivyc_s1::ivy__expr ext__ivy__app__get_func(const ivy__app& s);
    virtual ivyc_s1::cpp__expr ext__cpp__plus__make(ivyc_s1::cpp__expr lhs, ivyc_s1::cpp__expr rhs, ivyc_s1::annot ann);
    virtual ivyc_s1::cpp__expr ext__cpp__symbol__makestr(const str& name, ivyc_s1::annot ann);
    virtual void ext__ivy__file_not_found__encode(const ivy__file_not_found& e, pretty& b);
    virtual void imp__parse_error(unsigned long long p, const str& tok);
    virtual ivy__whilest ext__ivy__whilest__flat_int(const ivy__whilest& s, ivy__flatst& st);
    virtual ivyc_s1::ivy__expr ext__ivy__colon__make(ivyc_s1::ivy__expr lhs, ivyc_s1::ivy__expr rhs, ivyc_s1::annot ann);
    virtual void ext__str__extend(str& a, const str& b);
    virtual ivyc_s1::annot ext__ivy__sequence__get_ann(const ivy__sequence& s);
    virtual ivyc_s1::ivy__expr ext__ivy__get_formal_type(const vector__ivy__expr__& typings, ivyc_s1::annot ann);
    virtual void ext__ivy__type_context__pop(ivy__type_context& s);
    virtual ivyc_s1::annot ext__ivy__includedc__get_ann(const ivy__includedc& s);
    virtual bool ext__ivy__expr__is(ivyc_s1::ivy__expr s, ivy__verb vrb);
    virtual void ext__ivy__initdc__flat(const ivy__initdc& s, ivy__flatst& st);
    virtual vector__ivy__expr__ ext__ivy__get_func_params(ivyc_s1::ivy__expr typing);
    virtual bool ext__ivy__app__occurs(const ivy__app& s, ivyc_s1::ivy__ident n);
    virtual void ext__pstate__get_ann(pstate& st, ivyc_s1::annot& ann);
    virtual ivyc_s1::cpp__expr ext__ivy__make_md_vector_type(const vector__ivy__expr__& dom, ivyc_s1::ivy__expr rng, ivy__tocppst& st);
    virtual void ext__ivy__add_is_seq_pred(cpp__structdecl& s);
    virtual void ext__ivy__actdc__build_global_types(const ivy__actdc& s, ivy__global_types& st);
    virtual ivyc_s1::ivy__expr ext__ivy__stmt__get_lhs(ivyc_s1::ivy__stmt s);
    virtual ivyc_s1::cpp__ident ext__cpp__dotident__prefix(const cpp__dotident& s, ivyc_s1::cpp__ident pref);
    virtual ivyc_s1::ivy__stmt ext__ivy__whilest__typeinfer(const ivy__whilest& s, ivy__typeinferst& st);
    virtual void ext__pretty__do_indent(pretty& self);
    virtual void ext__ivy__ident_to_ident__set(ivy__ident_to_ident& a, ivyc_s1::ivy__ident x, ivyc_s1::ivy__ident y);
    virtual void ext__stdio__write(const str& s);
    virtual void ext__annot__encode(ivyc_s1::annot s, pretty& b);
    virtual ivyc_s1::ivy__expr ext__ivy__app__reduce(const ivy__app& s, const ivy__symeval& smap);
    virtual str ext__ivy__ident__to_str(ivyc_s1::ivy__ident s);
    virtual ivyc_s1::ivy__expr ext__ivy__app__get_type(const ivy__app& s);
    virtual str ext__annot__to_str(ivyc_s1::annot s);
    virtual void ext__ivy__groupdc__defd(const ivy__groupdc& s, ivy__flatst& st);
    virtual void ext__vector__ivy__decl____append(vector__ivy__decl__& a, ivyc_s1::ivy__decl v);
    virtual void ext__ivy__kill_lvalues(const vector__ivy__expr__& es, ivy__tocppst& st, const vector__ivy__access_path__& paths);
    virtual void ext__ivy__add_upcast_method(cpp__structdecl& s);
    virtual void ext__ivy__prog__find_include(str& name);
    virtual bool ext__cpp__expr__eq(ivyc_s1::cpp__expr e1, ivyc_s1::cpp__expr e2);
    virtual void ext__ivy__set_built_in_type(ivy__verb vrb, const str& ty, bool m, bool io, bool oi, bool fi);
    virtual unsigned long long ext__pos__next(unsigned long long x);
    virtual ivyc_s1::cpp__expr ext__ivy__fix_tpl_param(ivyc_s1::ivy__expr s, ivy__tocppst& st);
    virtual void ext__ivy__path__change_extension(str& path, const str& ext);
    virtual bool ext__ivy__path_may_alias(const ivy__access_path& v, const ivy__access_path& w);
    virtual void ext__ivy__dotident__encode(const ivy__dotident& s, pretty& b, int prio);
    virtual ivy__interpdc ext__ivy__interpdc__flat_int(const ivy__interpdc& s, ivy__flatst& st);
    virtual ivyc_s1::cpp__expr ext__cpp__symbol__makestr1(const str& name, ivyc_s1::cpp__ident arg, ivyc_s1::annot ann);
    virtual bool ext__ivy__is_typing_complete(ivyc_s1::ivy__expr typing);
    virtual void ext__ivy__stmt__parse_lang_stmt(pstate& st, int prio, ivyc_s1::ivy__stmt& res);
    virtual bool ext__cpp__is_logvar_name(const str& name);
    virtual void ext__cpp__expr__tup__encode(const vector__cpp__expr__& s, pretty& b, int prio);
    virtual void ext__ivy__add_sizet_conv(cpp__structdecl& s);
    virtual void ext__ivy__typedc__build_subtypes(const ivy__typedc& s, ivy__subtypes& st);
    virtual ivyc_s1::cpp__ident ext__ivy__strident__to_cpp(const ivy__strident& s, bool native);
    virtual str ext__ivy__expr__enc(ivyc_s1::ivy__expr e);
    virtual void ext__cpp__stmt__encode(ivyc_s1::cpp__stmt s, pretty& b, int prio);
    virtual ivyc_s1::ivy__stmt ext__ivy__sequence__flat(const ivy__sequence& s, ivy__flatst& st);
    virtual void ext__ivy__moduledc__defd(const ivy__moduledc& s, ivy__flatst& st);
    virtual ivyc_s1::ivy__stmt ext__ivy__stmt__flat(ivyc_s1::ivy__stmt s, ivy__flatst& st);
    virtual unsigned long long ext__vector__pos____domain__next(unsigned long long x);
    virtual vector__ivy__expr__ ext__ivy__comma__unfold_left(ivyc_s1::ivy__expr s);
    virtual pretty__state ext__vector__pretty__state____back(const vector__pretty__state__& a);
    virtual ivyc_s1::cpp__expr ext__cpp__new__make(ivyc_s1::cpp__expr arg, ivyc_s1::annot ann);
    virtual void ext__ivy__param_map__set(ivy__param_map& a, ivyc_s1::ivy__ident x, unsigned long long y);
    virtual void ext__vector__ivy__error____append(vector__ivy__error__& a, ivyc_s1::ivy__error v);
    virtual void ext__cpp__strident__encode(const cpp__strident& s, pretty& b, int prio);
    virtual void ext__ivy__instantiatedc__defd(const ivy__instantiatedc& s, ivy__flatst& st);
    virtual void ext__ivy__ident_to_prototype__set(ivy__ident_to_prototype& a, ivyc_s1::ivy__ident x, const ivy__prototype& y);
    virtual ivyc_s1::ivy__expr ext__ivy__expr__type_decorate(ivyc_s1::ivy__expr e, ivy__decost& st, const ivy__symeval& m, ivyc_s1::ivy__expr& ty);
    virtual void ext__vector__pretty__token____set(vector__pretty__token__& a, unsigned long long x, const pretty__token& y);
    virtual bool ext__ivy__subtypes__is_subtype(const ivy__subtypes& s, ivyc_s1::ivy__expr sub, ivyc_s1::ivy__expr super);
    virtual void ext__ivy__type_context__push(ivy__type_context& s, ivyc_s1::ivy__expr typing);
    virtual void ext__ivy__elidest__map__get(const ivy__elidest__map& a, ivyc_s1::ivy__ident x, bool& y);
    virtual ivyc_s1::cpp__expr ext__cpp__and__make(ivyc_s1::cpp__expr lhs, ivyc_s1::cpp__expr rhs, ivyc_s1::annot ann);
    virtual void ext__cpp__asgn__encode(const cpp__asgn& s, pretty& b, int prio);
    virtual void ext__cpp__decl__encode(ivyc_s1::cpp__decl s, pretty& b, int prio);
    virtual void ext__vector__cpp__decl____append(vector__cpp__decl__& a, ivyc_s1::cpp__decl v);
    virtual ivyc_s1::ivy__stmt ext__ivy__actdc__get_body(const ivy__actdc& s);
    virtual void ext__ivy__expr__tup__parse(pstate& st, int prio, vector__ivy__expr__& res);
    virtual ivyc_s1::ivy__ident ext__ivy__ident__get_member(ivyc_s1::ivy__ident s);
    virtual ivyc_s1::ivy__ident ext__ivy__expr__get_name(ivyc_s1::ivy__expr s);
    virtual void ext__ivy__remove_local_vars(const vector__ivy__ident__& del, ivy__flatst& st);
    virtual ivy__strident ext__ivy__strident__get_last(const ivy__strident& s);
    virtual ivyc_s1::annot ext__ivy__breakst__get_ann(const ivy__breakst& s);
    virtual void ext__read_string_literal(pstate& st);
    virtual unsigned long long ext__vector__pretty__token____domain__prev(unsigned long long x);
    virtual ivyc_s1::ivy__stmt ext__ivy__initdc__get_body(const ivy__initdc& s);
    virtual bool ext__ivy__is_input_param(const ivy__actdc& s, ivyc_s1::ivy__expr p);
    virtual void ext__vector__ivy__type_context__stack_entry____append(vector__ivy__type_context__stack_entry__& a, const ivy__type_context__stack_entry& v);
    virtual ivyc_s1::cpp__expr ext__cpp__dot__make(ivyc_s1::cpp__expr lhs, ivyc_s1::cpp__expr rhs, ivyc_s1::annot ann);
    virtual ivy__verb ext__ivy__expr__get_verb(ivyc_s1::ivy__expr s);
    virtual void ext__ivy__add_standard_traits(cpp__structdecl& s);
    virtual ivyc_s1::cpp__ident ext__cpp__ident__prefix(ivyc_s1::cpp__ident s, ivyc_s1::cpp__ident pref);
    virtual void ext__ivy__vardc__flat(const ivy__vardc& s, ivy__flatst& st);
    virtual void ext__ivy__structspec__auto_flat_spec(const ivy__structspec& s, ivy__flatst& st, ivyc_s1::ivy__expr ty);
    virtual unsigned long long ext__vector__cpp__stmt____domain__next(unsigned long long x);
    virtual ivyc_s1::cpp__decl ext__ivy__typedc__to_cpp(const ivy__typedc& s, ivy__tocppst& st);
    virtual str ext__cpp__dotident__to_str(const cpp__dotident& s);
    virtual ivyc_s1::cpp__ident ext__cpp__dotident__get_member(const cpp__dotident& s);
    virtual ivyc_s1::ivy__expr ext__ivy__isaop__make(ivyc_s1::ivy__expr lhs, ivyc_s1::ivy__expr rhs, ivyc_s1::annot ann);
    virtual void ext__ivy__setup_formals(const vector__ivy__expr__& es, bool val, ivy__typeinferst& st);
    virtual ivyc_s1::ivy__expr ext__ivy__app__make1(ivyc_s1::ivy__expr func, ivyc_s1::ivy__expr arg0, ivyc_s1::annot ann);
    virtual void ext__ivy__local_tracker__push(ivy__local_tracker& s);
    virtual str ext__cpp__strident__to_str(const cpp__strident& s);
    virtual void ext__ivy__ident_to_exprs__add(ivy__ident_to_exprs& a, ivyc_s1::ivy__ident x, ivyc_s1::ivy__expr y);
    virtual void ext__ivy__bottom_up_types(vector__ivy__expr__& es, ivyc_s1::ivy__expr func, const ivy__typeinferst& st, bool& ok);
    virtual void ext__cpp__varst__encode_int(const cpp__varst& s, pretty& b, int prio);
    virtual ivyc_s1::annot ext__cpp__namespacedecl__get_ann(const cpp__namespacedecl& d);
    virtual ivyc_s1::ivy__decl ext__ivy__includedc__make(ivyc_s1::ivy__expr file, ivyc_s1::annot ann);
    virtual void ext__ivy__ident_to_instantiatedc__set(ivy__ident_to_instantiatedc& a, ivyc_s1::ivy__ident x, const ivy__instantiatedc& y);
    virtual ivyc_s1::cpp__ident ext__cpp__strident__prefix(const cpp__strident& s, ivyc_s1::cpp__ident pref);
    virtual void ext__ivy__check_defined(ivyc_s1::ivy__ident name, const ivy__flatst& st, ivyc_s1::annot ann);
    virtual ivyc_s1::annot ext__ivy__stmt__get_ann(ivyc_s1::ivy__stmt s);
    virtual ivyc_s1::cpp__ident ext__cpp__dotident__get_namesp(const cpp__dotident& s);
    virtual ivy__actdc ext__ivy__actdc__typeinfer_int(const ivy__actdc& s, ivy__typeinferst& st);
    virtual ivyc_s1::ivy__decl ext__ivy__actdc__typeinfer(const ivy__actdc& s, ivy__typeinferst& st);
    virtual ivyc_s1::cpp__expr ext__cpp__and__fold_left(const vector__cpp__expr__& args, ivyc_s1::annot ann);
    virtual ivyc_s1::cpp__expr ext__cpp__expr__get_func(ivyc_s1::cpp__expr s);
    virtual void ext__ivy__path__concat(str& path1, const str& path2);
    virtual ivyc_s1::cpp__decl ext__ivy__decl__to_cpp(ivyc_s1::ivy__decl s, ivy__tocppst& st);
    virtual ivyc_s1::cpp__stmt ext__cpp__sequence__make(ivyc_s1::cpp__stmt x, ivyc_s1::cpp__stmt y, ivyc_s1::annot ann);
    virtual bool ext__ivy__decl__emitted(ivyc_s1::ivy__decl s, const ivy__tocppst& st);
    virtual ivyc_s1::annot ext__ivy__symbol__get_ann(const ivy__symbol& s);
    virtual void ext__ivy__decost__map__set(ivy__decost__map& a, ivyc_s1::ivy__ident x, ivyc_s1::ivy__expr y);
    virtual void ext__ivy__add_derived_cons(cpp__structdecl& s, ivyc_s1::cpp__expr t, bool constref);
    virtual bool ext__ivy__app__is(const ivy__app& s, ivy__verb vrb);
    virtual ivy__moduledc ext__ivy__instantiatedc__setup(const ivy__instantiatedc& s, ivy__flatst& st);
    virtual bool ext__ivy__objectdc__emitted(const ivy__objectdc& s, const ivy__tocppst& st);
    virtual void ext__ivy__parse_action(pstate& st, int prio, ivy__action_kind kind, ivyc_s1::ivy__decl& res);
    virtual void ext__ivy__symbol__parse(pstate& st, ivyc_s1::ivy__expr& res);
    virtual ivyc_s1::ivy__expr ext__ivy__times__make(ivyc_s1::ivy__expr lhs, ivyc_s1::ivy__expr rhs, ivyc_s1::annot ann);
    virtual ivyc_s1::ivy__stmt ext__ivy__varst__flat(const ivy__varst& s, ivy__flatst& st);
    virtual void ext__ivy__add_diseq_pred(cpp__structdecl& s);
    virtual void ext__vector__ivy__expr____append(vector__ivy__expr__& a, ivyc_s1::ivy__expr v);
    virtual void ext__ivy__actdc__reg_member(const ivy__actdc& s, ivy__tocppst& st);
    virtual void __init();
    virtual void ext__ivy__version__parse(pstate& st, int prio, ivy__version& res);
    virtual void ext__ivy__prog__file_to_cpp(const str& name);
    virtual void ext__ivy__stmt__parse(pstate& st, int prio, ivyc_s1::ivy__stmt& res);
    virtual void ext__ivy__prog__read_file_int(const str& name, ivyc_s1::annot ann, ivy__prog& p, ivy__prog__readst& rst);
    virtual void ext__ivy__tocppst__add_stmt(ivy__tocppst& s, ivyc_s1::cpp__stmt code);
    virtual void ext__ivy__ident_set__set(ivy__ident_set& a, ivyc_s1::ivy__ident x, bool y);
    virtual ivyc_s1::ivy__expr ext__ivy__stmt__get_rhs(ivyc_s1::ivy__stmt s);
    virtual ivyc_s1::cpp__expr ext__cpp__not__make(ivyc_s1::cpp__expr arg, ivyc_s1::annot ann);
    virtual ivyc_s1::ivy__decl ext__ivy__decl__typeinfer(ivyc_s1::ivy__decl s, ivy__typeinferst& st);
    virtual ivyc_s1::ivy__expr ext__ivy__app__type_elide_int(const ivy__app& e, bool b0, const ivy__symeval& m, ivy__elidest& st);
    virtual void ext__cpp__retst__encode(const cpp__retst& s, pretty& b, int prio);
    virtual ivyc_s1::cpp__expr ext__cpp__symbol__prefix(const cpp__symbol& s, ivyc_s1::cpp__ident pref);
    virtual ivyc_s1::ivy__decl ext__ivy__vardc__make(ivyc_s1::ivy__expr typing, bool is_destructor, ivyc_s1::annot ann);
    virtual ivy__verb ext__ivy__symbol__get_verb(const ivy__symbol& s);
    virtual void ext__vector__pretty__state____pop_back(vector__pretty__state__& a);
    virtual void ext__ivy__add_hasher(cpp__structdecl& s);
    virtual ivy__syntax_error ext__ivy__syntax_error__make(const str& tok);
    virtual void ext__vector__pos____pop_back(vector__pos__& a);
    virtual void ext__ivy__symbol__encode(const ivy__symbol& s, pretty& b, int prio);
    virtual ivyc_s1::annot ext__cpp__enumdecl__get_ann(const cpp__enumdecl& d);
    virtual void ext__ivy__expr__encode(ivyc_s1::ivy__expr s, pretty& b, int prio);
    virtual str ext__cpp__prog__enc(const cpp__prog& e);
    virtual ivyc_s1::cpp__stmt ext__ivy__whilest__to_cpp(const ivy__whilest& s, ivy__tocppst& st);
    virtual void ext__ivy__prog__flat(ivy__prog& p);
    virtual void ext__ivy__auto_flat(ivyc_s1::ivy__expr s, ivy__flatst& st);
    virtual bool ext__ivy__app__is_typed(const ivy__app& s, ivy__verb vrb);
    virtual void ext__ivy__push_pop_ident_set__set(ivy__push_pop_ident_set& s, ivyc_s1::ivy__ident id, bool v);
    virtual void ext__ivy__local_vec(const vector__ivy__expr__& es, bool val, ivy__flatst& st);
    virtual ivyc_s1::ivy__expr ext__ivy__expr__type_elide_int(ivyc_s1::ivy__expr e, bool b, const ivy__symeval& m, ivy__elidest& st);
    virtual ivyc_s1::cpp__stmt ext__cpp__retst__make(ivyc_s1::cpp__expr val, ivyc_s1::annot ann);
    virtual void ext__ivy__push_pop_ident_set__push(ivy__push_pop_ident_set& s);
    virtual void ext__ivy__structspec__to_destrs(const ivy__structspec& s, ivy__flatst& st, ivyc_s1::ivy__expr ty);
    virtual ivyc_s1::ivy__expr ext__ivy__app__make(ivyc_s1::ivy__expr func, const vector__ivy__expr__& args, ivyc_s1::annot ann);
    virtual bool ext__ivy__symbol__has_numident(const ivy__symbol& e);
    virtual void ext__vector__ivy__expr____extend(vector__ivy__expr__& a, const vector__ivy__expr__& b);
    virtual void ext__ivy__interpdc__reg_member(const ivy__interpdc& s, ivy__tocppst& st);
    virtual void ext__ivy__decost__typeinf_show_str(const str& s);
    virtual void ext__ivy__symeval__set(ivy__symeval& a, ivyc_s1::ivy__ident x, ivyc_s1::ivy__expr y);
    virtual str ext__env__get(const str& name);
    virtual void ext__pretty__nest(pretty& self);
    virtual bool ext__ivy__interpdc__emitted(const ivy__interpdc& s, const ivy__tocppst& st);
    virtual cpp__verb ext__cpp__expr__get_verb(ivyc_s1::cpp__expr s);
    virtual ivyc_s1::ivy__expr ext__ivy__symbol__makenum(unsigned long long num, ivyc_s1::annot ann);
    virtual ivyc_s1::cpp__expr ext__cpp__voidtype(ivyc_s1::annot ann);
    virtual ivyc_s1::ivy__expr ext__ivy__symbol__type_decorate(const ivy__symbol& e, ivy__decost& st, const ivy__symeval& m, ivyc_s1::ivy__expr& ty);
    virtual ivyc_s1::cpp__expr ext__cpp__app__get_func(const cpp__app& s);
    virtual ivyc_s1::ivy__expr ext__ivy__app__type_decorate(const ivy__app& e, ivy__decost& st, const ivy__symeval& m, ivyc_s1::ivy__expr& ty);
    virtual ivyc_s1::cpp__expr ext__cpp__equals__make(ivyc_s1::cpp__expr lhs, ivyc_s1::cpp__expr rhs, ivyc_s1::annot ann);
    virtual ivyc_s1::ivy__decl ext__ivy__decl__func_to_action(ivyc_s1::ivy__decl s);
    virtual void ext__ivy__ident_to_ident__get(const ivy__ident_to_ident& a, ivyc_s1::ivy__ident x, ivyc_s1::ivy__ident& y);
    virtual void ext__cpp__typedecl__encode(const cpp__typedecl& s, pretty& b, int prio);
    virtual void ext__cpp__whilest__encode_int(const cpp__whilest& s, pretty& b, int prio);
    virtual ivyc_s1::ivy__ident ext__ivy__make_auto_key(ivyc_s1::ivy__ident id, bool rev, ivy__symeval& pmap);
    virtual void ext__ivy__local_tracker__add_var(ivy__local_tracker& s, ivyc_s1::ivy__expr typing);
    virtual void ext__ivy__make_isa(ivyc_s1::cpp__expr& s, ivyc_s1::cpp__expr ty);
    virtual bool ext__ivy__vardc__emitted(const ivy__vardc& s, const ivy__tocppst& st);
    virtual ivyc_s1::cpp__ident ext__cpp__expr__get_name(ivyc_s1::cpp__expr s);
    virtual ivyc_s1::cpp__stmt ext__ivy__skipst__to_cpp(const ivy__skipst& s, ivy__tocppst& st);
    virtual ivyc_s1::cpp__expr ext__cpp__vardecl__get_name(const cpp__vardecl& d);
    virtual void ext__ivy__undefined__encode(const ivy__undefined& e, pretty& b);
    virtual void ext__ivy__structspec__defd(const ivy__structspec& s, ivy__flatst& st, ivyc_s1::ivy__ident id);
    virtual ivyc_s1::cpp__stmt ext__cpp__sequence__fold_right(const vector__cpp__stmt__& args, ivyc_s1::annot ann);
    virtual void ext__ivy__actdc__record_prototypes(const ivy__actdc& s, ivy__tocppst& st);
    virtual ivyc_s1::ivy__stmt ext__ivy__asgn__typeinfer(const ivy__asgn& s, ivy__typeinferst& st);
    virtual ivy__type_conversion ext__ivy__type_conversion__make(ivyc_s1::ivy__expr e, ivyc_s1::ivy__expr t1, ivyc_s1::ivy__expr t2);
    virtual bool ext__ivy__ident_to_moduledc__mem(const ivy__ident_to_moduledc& a, ivyc_s1::ivy__ident x);
    virtual cpp__varst ext__ivy__varst__to_cpp_int(const ivy__varst& s, ivy__tocppst& st);
    virtual ivyc_s1::annot ext__ivy__decl__get_ann(ivyc_s1::ivy__decl s);
    virtual ivy__type_context__stack_entry ext__vector__ivy__type_context__stack_entry____back(const vector__ivy__type_context__stack_entry__& a);
    virtual void ext__ivy__lvalue_paths(ivyc_s1::ivy__expr s, vector__ivy__access_path__& paths, bool ao);
    virtual ivyc_s1::cpp__ident ext__cpp__symbol__get_name(const cpp__symbol& s);
    virtual ivyc_s1::ivy__expr ext__ivy__expr__get_func(ivyc_s1::ivy__expr s);
    virtual ivyc_s1::ivy__expr ext__ivy__app__type_fill_in(const ivy__app& e, ivy__decost& st);
    virtual ivyc_s1::cpp__stmt ext__cpp__breakst__make(ivyc_s1::annot ann);
    virtual void ext__cpp__retst__encode_int(const cpp__retst& s, pretty& b, int prio);
    virtual void ext__vector__ivy__expr____set(vector__ivy__expr__& a, unsigned long long x, ivyc_s1::ivy__expr y);
    virtual cpp__symbol ext__ivy__symbol__to_cpp_int(const ivy__symbol& s, ivy__tocppst& st);
    virtual ivy__undefined ext__ivy__undefined__make(ivyc_s1::ivy__ident n);
    virtual ivyc_s1::cpp__expr ext__cpp__arrow__make(ivyc_s1::cpp__expr lhs, ivyc_s1::cpp__expr rhs, ivyc_s1::annot ann);
    virtual str ext__ivy__mangle(ivyc_s1::cpp__ident s);
    virtual void ext__ivy__objectdc__reg_member(const ivy__objectdc& s, ivy__tocppst& st);
    virtual ivyc_s1::cpp__ident ext__cpp__ident__get_namesp(ivyc_s1::cpp__ident s);
    virtual unsigned long long ext__vector__ivy__expr____domain__next(unsigned long long x);
    virtual void ext__pretty__add_length(pretty& self, unsigned long long len, unsigned long long at);
    virtual void ext__ivy__auto_defd(ivyc_s1::ivy__expr s, ivy__flatst& st);
    virtual void ext__cpp__dotident__encode(const cpp__dotident& s, pretty& b, int prio);
    virtual unsigned long long ext__vector__ivy__prototype_argument____domain__next(unsigned long long x);
    void __tick(int timeout);
};
inline bool operator ==(const ivyc_s1::annot &s, const ivyc_s1::annot &t);;
inline bool operator ==(const ivyc_s1::ivy__ident &s, const ivyc_s1::ivy__ident &t);;
inline bool operator ==(const ivyc_s1::ivy__expr &s, const ivyc_s1::ivy__expr &t);;
inline bool operator ==(const ivyc_s1::ivy__stmt &s, const ivyc_s1::ivy__stmt &t);;
inline bool operator ==(const ivyc_s1::ivy__decl &s, const ivyc_s1::ivy__decl &t);;
inline bool operator ==(const ivyc_s1::ivy__typespec &s, const ivyc_s1::ivy__typespec &t);;
inline bool operator ==(const ivyc_s1::ivy__error &s, const ivyc_s1::ivy__error &t);;
inline bool operator ==(const ivyc_s1::cpp__ident &s, const ivyc_s1::cpp__ident &t);;
inline bool operator ==(const ivyc_s1::cpp__expr &s, const ivyc_s1::cpp__expr &t);;
inline bool operator ==(const ivyc_s1::cpp__stmt &s, const ivyc_s1::cpp__stmt &t);;
inline bool operator ==(const ivyc_s1::cpp__decl &s, const ivyc_s1::cpp__decl &t);;
inline bool operator ==(const ivyc_s1::pretty__token &s, const ivyc_s1::pretty__token &t){
    return ((s.pair == t.pair) && (s.tdepth == t.tdepth) && (s.first == t.first) && (s.second == t.second));
}
inline bool operator ==(const ivyc_s1::pretty__state &s, const ivyc_s1::pretty__state &t){
    return ((s.begin == t.begin) && (s.total == t.total));
}
inline bool operator ==(const ivyc_s1::pretty &s, const ivyc_s1::pretty &t){
    return ((s.tokens == t.tokens) && (s.st == t.st) && (s.maxline == t.maxline) && (s.indent == t.indent) && (s.whitespace == t.whitespace) && (s.states == t.states) && (s.stack == t.stack) && (s.output == t.output) && (s.space == t.space) && (s.depth == t.depth) && (s.cppstyle == t.cppstyle));
}
inline bool operator ==(const ivyc_s1::annot_i &s, const ivyc_s1::annot_i &t){
    return ((s.comments == t.comments) && (s.line == t.line) && (s.file == t.file));
}

bool operator ==(const ivyc_s1::annot &s, const ivyc_s1::annot &t){
    if (s.tag != t.tag) return false;
    switch (s.tag) {
        case 0: return ivyc_s1::annot::unwrap< ivyc_s1::annot_i >(s) == ivyc_s1::annot::unwrap< ivyc_s1::annot_i >(t);

    }
    return true;
}
inline bool operator ==(const ivyc_s1::pstate &s, const ivyc_s1::pstate &t){
    return ((s.b == t.b) && (s.p == t.p) && (s.tok == t.tok) && (s.ann == t.ann) && (s.ok == t.ok));
}
inline bool operator ==(const ivyc_s1::ivy__strident &s, const ivyc_s1::ivy__strident &t){
    return ((s.val == t.val) && (s.subscrs == t.subscrs));
}
inline bool operator ==(const ivyc_s1::ivy__numident &s, const ivyc_s1::ivy__numident &t){
    return ((s.val == t.val));
}
inline bool operator ==(const ivyc_s1::ivy__dotident &s, const ivyc_s1::ivy__dotident &t){
    return ((s.namesp == t.namesp) && (s.member == t.member));
}

bool operator ==(const ivyc_s1::ivy__ident &s, const ivyc_s1::ivy__ident &t){
    if (s.tag != t.tag) return false;
    switch (s.tag) {
        case 0: return ivyc_s1::ivy__ident::unwrap< ivyc_s1::ivy__strident >(s) == ivyc_s1::ivy__ident::unwrap< ivyc_s1::ivy__strident >(t);
        case 1: return ivyc_s1::ivy__ident::unwrap< ivyc_s1::ivy__numident >(s) == ivyc_s1::ivy__ident::unwrap< ivyc_s1::ivy__numident >(t);
        case 2: return ivyc_s1::ivy__ident::unwrap< ivyc_s1::ivy__dotident >(s) == ivyc_s1::ivy__ident::unwrap< ivyc_s1::ivy__dotident >(t);

    }
    return true;
}
inline bool operator ==(const ivyc_s1::ivy__symbol &s, const ivyc_s1::ivy__symbol &t){
    return ((s.name == t.name) && (s.vrb == t.vrb) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::ivy__app &s, const ivyc_s1::ivy__app &t){
    return ((s.func == t.func) && (s.args == t.args) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::ivy__variable &s, const ivyc_s1::ivy__variable &t){
    return ((s.idx == t.idx) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::ivy__pi &s, const ivyc_s1::ivy__pi &t){
    return ((s.vars == t.vars) && (s.body == t.body) && (s.ann == t.ann));
}

bool operator ==(const ivyc_s1::ivy__expr &s, const ivyc_s1::ivy__expr &t){
    if (s.tag != t.tag) return false;
    switch (s.tag) {
        case 0: return ivyc_s1::ivy__expr::unwrap< ivyc_s1::ivy__symbol >(s) == ivyc_s1::ivy__expr::unwrap< ivyc_s1::ivy__symbol >(t);
        case 1: return ivyc_s1::ivy__expr::unwrap< ivyc_s1::ivy__app >(s) == ivyc_s1::ivy__expr::unwrap< ivyc_s1::ivy__app >(t);
        case 2: return ivyc_s1::ivy__expr::unwrap< ivyc_s1::ivy__variable >(s) == ivyc_s1::ivy__expr::unwrap< ivyc_s1::ivy__variable >(t);
        case 3: return ivyc_s1::ivy__expr::unwrap< ivyc_s1::ivy__pi >(s) == ivyc_s1::ivy__expr::unwrap< ivyc_s1::ivy__pi >(t);

    }
    return true;
}
inline bool operator ==(const ivyc_s1::ivy__asgn &s, const ivyc_s1::ivy__asgn &t){
    return ((s.lhs == t.lhs) && (s.rhs == t.rhs) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::ivy__sequence &s, const ivyc_s1::ivy__sequence &t){
    return ((s.lhs == t.lhs) && (s.rhs == t.rhs) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::ivy__skipst &s, const ivyc_s1::ivy__skipst &t){
    return ((s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::ivy__ifst &s, const ivyc_s1::ivy__ifst &t){
    return ((s.cond == t.cond) && (s.thenst == t.thenst) && (s.elsest == t.elsest) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::ivy__whilest &s, const ivyc_s1::ivy__whilest &t){
    return ((s.cond == t.cond) && (s.body == t.body) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::ivy__breakst &s, const ivyc_s1::ivy__breakst &t){
    return ((s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::ivy__prototype_argument &s, const ivyc_s1::ivy__prototype_argument &t){
    return ((s.name == t.name) && (s.is_input == t.is_input) && (s.inpos == t.inpos) && (s.is_output == t.is_output) && (s.outpos == t.outpos) && (s.is_ref == t.is_ref) && (s.is_const == t.is_const));
}
inline bool operator ==(const ivyc_s1::ivy__prototype &s, const ivyc_s1::ivy__prototype &t){
    return ((s.args == t.args) && (s.has_ret == t.has_ret) && (s.ret == t.ret));
}
inline bool operator ==(const ivyc_s1::ivy__actdc &s, const ivyc_s1::ivy__actdc &t){
    return ((s.name == t.name) && (s.kind == t.kind) && (s.inputs == t.inputs) && (s.outputs == t.outputs) && (s.has_body == t.has_body) && (s.body == t.body) && (s.ann == t.ann) && (s.has_proto == t.has_proto) && (s.proto == t.proto));
}
inline bool operator ==(const ivyc_s1::ivy__varst &s, const ivyc_s1::ivy__varst &t){
    return ((s.name == t.name) && (s.ann == t.ann));
}

bool operator ==(const ivyc_s1::ivy__stmt &s, const ivyc_s1::ivy__stmt &t){
    if (s.tag != t.tag) return false;
    switch (s.tag) {
        case 0: return ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__asgn >(s) == ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__asgn >(t);
        case 1: return ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__sequence >(s) == ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__sequence >(t);
        case 2: return ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__skipst >(s) == ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__skipst >(t);
        case 3: return ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__ifst >(s) == ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__ifst >(t);
        case 4: return ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__whilest >(s) == ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__whilest >(t);
        case 5: return ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__breakst >(s) == ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__breakst >(t);
        case 6: return ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__varst >(s) == ivyc_s1::ivy__stmt::unwrap< ivyc_s1::ivy__varst >(t);

    }
    return true;
}
inline bool operator ==(const ivyc_s1::ivy__groupdc &s, const ivyc_s1::ivy__groupdc &t){
    return ((s.decls == t.decls) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::ivy__enumspec &s, const ivyc_s1::ivy__enumspec &t){
    return ((s.constructors == t.constructors) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::ivy__structspec &s, const ivyc_s1::ivy__structspec &t){
    return ((s.destructors == t.destructors) && (s.ann == t.ann));
}

bool operator ==(const ivyc_s1::ivy__typespec &s, const ivyc_s1::ivy__typespec &t){
    if (s.tag != t.tag) return false;
    switch (s.tag) {
        case 0: return ivyc_s1::ivy__typespec::unwrap< ivyc_s1::ivy__enumspec >(s) == ivyc_s1::ivy__typespec::unwrap< ivyc_s1::ivy__enumspec >(t);
        case 1: return ivyc_s1::ivy__typespec::unwrap< ivyc_s1::ivy__structspec >(s) == ivyc_s1::ivy__typespec::unwrap< ivyc_s1::ivy__structspec >(t);

    }
    return true;
}
inline bool operator ==(const ivyc_s1::ivy__typedc &s, const ivyc_s1::ivy__typedc &t){
    return ((s.sort == t.sort) && (s.has_super == t.has_super) && (s.super == t.super) && (s.has_spec == t.has_spec) && (s.spec == t.spec) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::ivy__vardc &s, const ivyc_s1::ivy__vardc &t){
    return ((s.typing == t.typing) && (s.is_destructor == t.is_destructor) && (s.has_def == t.has_def) && (s.def == t.def) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::ivy__header &s, const ivyc_s1::ivy__header &t){
    return ((s.filename == t.filename) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::ivy__interpdc &s, const ivyc_s1::ivy__interpdc &t){
    return ((s.itype == t.itype) && (s.ctype == t.ctype) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::ivy__includedc &s, const ivyc_s1::ivy__includedc &t){
    return ((s.file == t.file) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::ivy__moduledc &s, const ivyc_s1::ivy__moduledc &t){
    return ((s.name == t.name) && (s.prms == t.prms) && (s.body == t.body) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::ivy__instantiatedc &s, const ivyc_s1::ivy__instantiatedc &t){
    return ((s.name == t.name) && (s.prms == t.prms) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::ivy__objectdc &s, const ivyc_s1::ivy__objectdc &t){
    return ((s.name == t.name) && (s.body == t.body) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::ivy__instancedc &s, const ivyc_s1::ivy__instancedc &t){
    return ((s.objname == t.objname) && (s.modname == t.modname) && (s.prms == t.prms) && (s.is_auto == t.is_auto) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::ivy__initdc &s, const ivyc_s1::ivy__initdc &t){
    return ((s.body == t.body) && (s.ann == t.ann));
}

bool operator ==(const ivyc_s1::ivy__decl &s, const ivyc_s1::ivy__decl &t){
    if (s.tag != t.tag) return false;
    switch (s.tag) {
        case 0: return ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__actdc >(s) == ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__actdc >(t);
        case 1: return ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__groupdc >(s) == ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__groupdc >(t);
        case 2: return ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__typedc >(s) == ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__typedc >(t);
        case 3: return ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__vardc >(s) == ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__vardc >(t);
        case 4: return ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__header >(s) == ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__header >(t);
        case 5: return ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__interpdc >(s) == ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__interpdc >(t);
        case 6: return ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__includedc >(s) == ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__includedc >(t);
        case 7: return ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__moduledc >(s) == ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__moduledc >(t);
        case 8: return ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__instantiatedc >(s) == ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__instantiatedc >(t);
        case 9: return ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__objectdc >(s) == ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__objectdc >(t);
        case 10: return ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__instancedc >(s) == ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__instancedc >(t);
        case 11: return ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__initdc >(s) == ivyc_s1::ivy__decl::unwrap< ivyc_s1::ivy__initdc >(t);

    }
    return true;
}
inline bool operator ==(const ivyc_s1::ivy__version &s, const ivyc_s1::ivy__version &t){
    return ((s.nums == t.nums));
}
inline bool operator ==(const ivyc_s1::ivy__prog &s, const ivyc_s1::ivy__prog &t){
    return ((s.vers == t.vers) && (s.decls == t.decls));
}
inline bool operator ==(const ivyc_s1::ivy__type_clash &s, const ivyc_s1::ivy__type_clash &t){
    return ((s.e == t.e) && (s.t1 == t.t1) && (s.t2 == t.t2));
}
inline bool operator ==(const ivyc_s1::ivy__type_conversion &s, const ivyc_s1::ivy__type_conversion &t){
    return ((s.e == t.e) && (s.t1 == t.t1) && (s.t2 == t.t2));
}
inline bool operator ==(const ivyc_s1::ivy__untyped &s, const ivyc_s1::ivy__untyped &t){
    return ((s.e == t.e) && (s.t1 == t.t1));
}
inline bool operator ==(const ivyc_s1::ivy__not_first_order &s, const ivyc_s1::ivy__not_first_order &t){
    return ((s.e == t.e) && (s.t1 == t.t1));
}
inline bool operator ==(const ivyc_s1::ivy__file_not_found &s, const ivyc_s1::ivy__file_not_found &t){
    return ((s.n == t.n));
}
inline bool operator ==(const ivyc_s1::ivy__cannot_write &s, const ivyc_s1::ivy__cannot_write &t){
    return ((s.n == t.n));
}
inline bool operator ==(const ivyc_s1::ivy__undefined &s, const ivyc_s1::ivy__undefined &t){
    return ((s.n == t.n));
}
inline bool operator ==(const ivyc_s1::ivy__wrong_number_params &s, const ivyc_s1::ivy__wrong_number_params &t){
    return ((s.n == t.n));
}
inline bool operator ==(const ivyc_s1::ivy__syntax_error &s, const ivyc_s1::ivy__syntax_error &t){
    return ((s.tok == t.tok));
}

bool operator ==(const ivyc_s1::ivy__error &s, const ivyc_s1::ivy__error &t){
    if (s.tag != t.tag) return false;
    switch (s.tag) {
        case 0: return ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__type_clash >(s) == ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__type_clash >(t);
        case 1: return ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__type_conversion >(s) == ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__type_conversion >(t);
        case 2: return ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__untyped >(s) == ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__untyped >(t);
        case 3: return ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__not_first_order >(s) == ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__not_first_order >(t);
        case 4: return ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__file_not_found >(s) == ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__file_not_found >(t);
        case 5: return ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__cannot_write >(s) == ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__cannot_write >(t);
        case 6: return ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__undefined >(s) == ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__undefined >(t);
        case 7: return ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__wrong_number_params >(s) == ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__wrong_number_params >(t);
        case 8: return ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__syntax_error >(s) == ivyc_s1::ivy__error::unwrap< ivyc_s1::ivy__syntax_error >(t);

    }
    return true;
}
inline bool operator ==(const ivyc_s1::ivy__prog__readst &s, const ivyc_s1::ivy__prog__readst &t){
    return ((s.have_read == t.have_read));
}
inline bool operator ==(const ivyc_s1::ivy__flatst &s, const ivyc_s1::ivy__flatst &t){
    return ((s.decls == t.decls) && (s.prmvals == t.prmvals) && (s.moddecls == t.moddecls) && (s.defs == t.defs) && (s.has_root == t.has_root) && (s.root == t.root) && (s.locals == t.locals) && (s.globals == t.globals) && (s.defining == t.defining) && (s.absolute == t.absolute) && (s.dot_rhs == t.dot_rhs) && (s.autodefs == t.autodefs) && (s.autos_pending == t.autos_pending) && (s.no_undefined == t.no_undefined));
}
inline bool operator ==(const ivyc_s1::ivy__subtypes &s, const ivyc_s1::ivy__subtypes &t){
    return ((s.subtypes_of == t.subtypes_of) && (s.supertype_of == t.supertype_of));
}
inline bool operator ==(const ivyc_s1::ivy__global_types &s, const ivyc_s1::ivy__global_types &t){
    return ((s.type_of == t.type_of) && (s.is_action == t.is_action) && (s.curried == t.curried));
}
inline bool operator ==(const ivyc_s1::ivy__push_pop_ident_set &s, const ivyc_s1::ivy__push_pop_ident_set &t){
    return ((s.map == t.map) && (s.del == t.del) && (s.stack == t.stack));
}
inline bool operator ==(const ivyc_s1::ivy__local_tracker &s, const ivyc_s1::ivy__local_tracker &t){
    return ((s.map == t.map));
}
inline bool operator ==(const ivyc_s1::ivy__decost &s, const ivyc_s1::ivy__decost &t){
    return ((s.counter == t.counter) && (s.m == t.m) && (s.ty == t.ty) && (s.member == t.member) && (s.ok == t.ok) && (s.failed == t.failed) && (s.error_reported == t.error_reported));
}
inline bool operator ==(const ivyc_s1::ivy__elidest &s, const ivyc_s1::ivy__elidest &t){
    return ((s.seen == t.seen));
}
inline bool operator ==(const ivyc_s1::ivy__type_context__stack_entry &s, const ivyc_s1::ivy__type_context__stack_entry &t){
    return ((s.id == t.id) && (s.any == t.any) && (s.val == t.val));
}
inline bool operator ==(const ivyc_s1::ivy__type_context &s, const ivyc_s1::ivy__type_context &t){
    return ((s.m == t.m) && (s.stack == t.stack));
}
inline bool operator ==(const ivyc_s1::ivy__typeinferst &s, const ivyc_s1::ivy__typeinferst &t){
    return ((s.tc == t.tc) && (s.subtype_rel == t.subtype_rel));
}
inline bool operator ==(const ivyc_s1::cpp__strident &s, const ivyc_s1::cpp__strident &t){
    return ((s.val == t.val) && (s.subscrs == t.subscrs));
}
inline bool operator ==(const ivyc_s1::cpp__numident &s, const ivyc_s1::cpp__numident &t){
    return ((s.val == t.val));
}
inline bool operator ==(const ivyc_s1::cpp__dotident &s, const ivyc_s1::cpp__dotident &t){
    return ((s.namesp == t.namesp) && (s.member == t.member));
}

bool operator ==(const ivyc_s1::cpp__ident &s, const ivyc_s1::cpp__ident &t){
    if (s.tag != t.tag) return false;
    switch (s.tag) {
        case 0: return ivyc_s1::cpp__ident::unwrap< ivyc_s1::cpp__strident >(s) == ivyc_s1::cpp__ident::unwrap< ivyc_s1::cpp__strident >(t);
        case 1: return ivyc_s1::cpp__ident::unwrap< ivyc_s1::cpp__numident >(s) == ivyc_s1::cpp__ident::unwrap< ivyc_s1::cpp__numident >(t);
        case 2: return ivyc_s1::cpp__ident::unwrap< ivyc_s1::cpp__dotident >(s) == ivyc_s1::cpp__ident::unwrap< ivyc_s1::cpp__dotident >(t);

    }
    return true;
}
inline bool operator ==(const ivyc_s1::cpp__symbol &s, const ivyc_s1::cpp__symbol &t){
    return ((s.name == t.name) && (s.vrb == t.vrb) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::cpp__app &s, const ivyc_s1::cpp__app &t){
    return ((s.func == t.func) && (s.args == t.args) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::cpp__variable &s, const ivyc_s1::cpp__variable &t){
    return ((s.idx == t.idx) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::cpp__pi &s, const ivyc_s1::cpp__pi &t){
    return ((s.vars == t.vars) && (s.body == t.body) && (s.ann == t.ann));
}

bool operator ==(const ivyc_s1::cpp__expr &s, const ivyc_s1::cpp__expr &t){
    if (s.tag != t.tag) return false;
    switch (s.tag) {
        case 0: return ivyc_s1::cpp__expr::unwrap< ivyc_s1::cpp__symbol >(s) == ivyc_s1::cpp__expr::unwrap< ivyc_s1::cpp__symbol >(t);
        case 1: return ivyc_s1::cpp__expr::unwrap< ivyc_s1::cpp__app >(s) == ivyc_s1::cpp__expr::unwrap< ivyc_s1::cpp__app >(t);
        case 2: return ivyc_s1::cpp__expr::unwrap< ivyc_s1::cpp__variable >(s) == ivyc_s1::cpp__expr::unwrap< ivyc_s1::cpp__variable >(t);
        case 3: return ivyc_s1::cpp__expr::unwrap< ivyc_s1::cpp__pi >(s) == ivyc_s1::cpp__expr::unwrap< ivyc_s1::cpp__pi >(t);

    }
    return true;
}
inline bool operator ==(const ivyc_s1::cpp__asgn &s, const ivyc_s1::cpp__asgn &t){
    return ((s.lhs == t.lhs) && (s.rhs == t.rhs) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::cpp__sequence &s, const ivyc_s1::cpp__sequence &t){
    return ((s.lhs == t.lhs) && (s.rhs == t.rhs) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::cpp__skipst &s, const ivyc_s1::cpp__skipst &t){
    return ((s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::cpp__ifst &s, const ivyc_s1::cpp__ifst &t){
    return ((s.cond == t.cond) && (s.thenst == t.thenst) && (s.elsest == t.elsest) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::cpp__whilest &s, const ivyc_s1::cpp__whilest &t){
    return ((s.cond == t.cond) && (s.body == t.body) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::cpp__breakst &s, const ivyc_s1::cpp__breakst &t){
    return ((s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::cpp__simpletype &s, const ivyc_s1::cpp__simpletype &t){
    return ((s._type == t._type) && (s.name == t.name) && (s.is_const == t.is_const) && (s.is_ref == t.is_ref));
}
inline bool operator ==(const ivyc_s1::cpp__functype &s, const ivyc_s1::cpp__functype &t){
    return ((s.base == t.base) && (s.args == t.args) && (s.is_const == t.is_const) && (s.has_initializer == t.has_initializer) && (s.initializer == t.initializer));
}
inline bool operator ==(const ivyc_s1::cpp__varst &s, const ivyc_s1::cpp__varst &t){
    return ((s.vtype == t.vtype) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::cpp__retst &s, const ivyc_s1::cpp__retst &t){
    return ((s.val == t.val) && (s.ann == t.ann));
}

bool operator ==(const ivyc_s1::cpp__stmt &s, const ivyc_s1::cpp__stmt &t){
    if (s.tag != t.tag) return false;
    switch (s.tag) {
        case 0: return ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__asgn >(s) == ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__asgn >(t);
        case 1: return ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__sequence >(s) == ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__sequence >(t);
        case 2: return ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__skipst >(s) == ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__skipst >(t);
        case 3: return ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__ifst >(s) == ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__ifst >(t);
        case 4: return ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__whilest >(s) == ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__whilest >(t);
        case 5: return ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__breakst >(s) == ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__breakst >(t);
        case 6: return ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__varst >(s) == ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__varst >(t);
        case 7: return ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__retst >(s) == ivyc_s1::cpp__stmt::unwrap< ivyc_s1::cpp__retst >(t);

    }
    return true;
}
inline bool operator ==(const ivyc_s1::cpp__header &s, const ivyc_s1::cpp__header &t){
    return ((s.filename == t.filename) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::cpp__typedecl &s, const ivyc_s1::cpp__typedecl &t){
    return ((s.ttype == t.ttype) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::cpp__enumdecl &s, const ivyc_s1::cpp__enumdecl &t){
    return ((s.name == t.name) && (s.elems == t.elems) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::cpp__vardecl &s, const ivyc_s1::cpp__vardecl &t){
    return ((s.vtype == t.vtype) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::cpp__funcdecl &s, const ivyc_s1::cpp__funcdecl &t){
    return ((s.ftype == t.ftype) && (s.has_body == t.has_body) && (s.body == t.body) && (s.is_static == t.is_static) && (s.is_virtual == t.is_virtual) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::cpp__structdecl &s, const ivyc_s1::cpp__structdecl &t){
    return ((s.name == t.name) && (s.has_super == t.has_super) && (s.super == t.super) && (s.has_members == t.has_members) && (s.members == t.members) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::cpp__namespacedecl &s, const ivyc_s1::cpp__namespacedecl &t){
    return ((s.name == t.name) && (s.members == t.members) && (s.ann == t.ann));
}
inline bool operator ==(const ivyc_s1::cpp__groupdc &s, const ivyc_s1::cpp__groupdc &t){
    return ((s.decls == t.decls) && (s.ann == t.ann));
}

bool operator ==(const ivyc_s1::cpp__decl &s, const ivyc_s1::cpp__decl &t){
    if (s.tag != t.tag) return false;
    switch (s.tag) {
        case 0: return ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__header >(s) == ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__header >(t);
        case 1: return ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__typedecl >(s) == ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__typedecl >(t);
        case 2: return ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__enumdecl >(s) == ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__enumdecl >(t);
        case 3: return ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__vardecl >(s) == ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__vardecl >(t);
        case 4: return ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__funcdecl >(s) == ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__funcdecl >(t);
        case 5: return ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__structdecl >(s) == ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__structdecl >(t);
        case 6: return ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__namespacedecl >(s) == ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__namespacedecl >(t);
        case 7: return ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__groupdc >(s) == ivyc_s1::cpp__decl::unwrap< ivyc_s1::cpp__groupdc >(t);

    }
    return true;
}
inline bool operator ==(const ivyc_s1::cpp__version &s, const ivyc_s1::cpp__version &t){
    return ((s.nums == t.nums));
}
inline bool operator ==(const ivyc_s1::cpp__prog &s, const ivyc_s1::cpp__prog &t){
    return ((s.vers == t.vers) && (s.decls == t.decls));
}
inline bool operator ==(const ivyc_s1::ivy__access_path &s, const ivyc_s1::ivy__access_path &t){
    return ((s.elems == t.elems));
}
inline bool operator ==(const ivyc_s1::ivy__lvalue_count &s, const ivyc_s1::ivy__lvalue_count &t){
    return ((s.lvalue == t.lvalue) && (s.path == t.path) && (s.cnt == t.cnt));
}
inline bool operator ==(const ivyc_s1::ivy__tocppst &s, const ivyc_s1::ivy__tocppst &t){
    return ((s.members == t.members) && (s.cppclasses == t.cppclasses) && (s.objects == t.objects) && (s.globals == t.globals) && (s.is_member == t.is_member) && (s.this_ident == t.this_ident) && (s.in_class == t.in_class) && (s.proto_only == t.proto_only) && (s.subtype_rel == t.subtype_rel) && (s.native == t.native) && (s.forward == t.forward) && (s.outputs == t.outputs) && (s.code == t.code) && (s.counter == t.counter) && (s.protos == t.protos) && (s.dead == t.dead) && (s.locals == t.locals) && (s.constructors == t.constructors) && (s.dot_rhs == t.dot_rhs));
}
