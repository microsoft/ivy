#include <vector>

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
}

