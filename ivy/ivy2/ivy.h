#include <vector>
#include <cstdint>
#include <iostream>

namespace ivy {

    struct integer {
        long long value;
        integer() {
            value = 0;
        }
        integer(long long v) {
            value = v;
        }
        integer &operator =(long long v) {
            value = v;
            return *this;
        }
        operator std::size_t() const {
            return value;
        }
    };

    template <class T, class ... RestD> struct vector;
    
    template<class T, class PrimaryD > struct vector<T, PrimaryD>  {
        typedef std::vector<T> type;
        type data;
        const T& operator() (PrimaryD idx) const {
            if (idx >= data.size()) {
                data.resize(idx+1);
            }
            return data[idx];
        }
        T& operator() (PrimaryD idx) {
            if (idx >= data.size()) {
                data.resize(idx+1);
            }
            return data[idx];
        }
    };

    template<class T, class PrimaryD, class ... RestD > struct vector<T, PrimaryD, RestD...> {
        typedef typename vector<T, RestD...>::type OneDimensionDownVectorT;
        typedef std::vector<OneDimensionDownVectorT> type;
        type data;
        const T& operator() (PrimaryD idx, RestD... parameters) const {
            if (idx >= data.size()) {
                data.resize(idx+1);
            }
            return data[idx](parameters...);
        }
        T& operator() (PrimaryD idx, RestD... parameters) {
            if (idx >= data.size()) {
                data.resize(idx+1);
            }
            return data[idx](parameters...);
        }
    };

    template <unsigned N> struct bv;

    template <typename T> struct native_int {
        T value;
        native_int() : value(0) {}
        native_int(long long value) : value(value) {}
        operator std::size_t() const {
            return value;
        }
    };

    template<typename T> T __num(long long x) {
        T res;
        res.value = x;
        return res;
    }

    template<typename T>
        static inline native_int<T> operator+(const native_int<T>& a,
                                              const native_int<T>& b) {
        return native_int<T>(a.value + b.value);
    }

    static inline void put(int c) {
        std::cout.put(c);
    }

    template <class T> static inline T from_str(const char *s) {
        T x;
        for (const char *p = s; *p; ++p) {
            x = x.append(*p);
        }
        return x;
    }
}

