#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

# A collection of C++ types used to model IVy types in compiled code.

from ivy_cpp import *
import ivy_utils as iu

class StrBV(CppClass):
    """ A type that represents text strings using a bit vector. It
    maintains a mapping from bit vector values to string values. Each
    time a new string constant is introduces, it is given an entry in
    the table. This can fail, however, if the number of string constants
    exceeds the number of bit vector values.
    """

    def __init__(self,classname,bits):
        """ bits is the number of bits in the bit vector representation """
        CppClass.__init__(self,classname,baseclass='std::string')
        self.bits = bits
        with self:
                add_member(
"""
CLASSNAME(){}
CLASSNAME(const std::string &s) : std::string(s) {}
CLASSNAME(const char *s) : std::string(s) {}
size_t __hash() const { return hash_space::hash<std::string>()(*this); }
#ifdef Z3PP_H_
static z3::sort z3_sort(z3::context &ctx) {return ctx.bv_sort(BITS);}
static hash_space::hash_map<std::string,int> string_to_bv_hash;
static hash_space::hash_map<int,std::string> bv_to_string_hash;
static int next_bv;
static int string_to_bv(const std::string &s){
    if(string_to_bv_hash.find(s) == string_to_bv_hash.end()){
        for (; next_bv < (1<<BITS); next_bv++) {
            if(bv_to_string_hash.find(next_bv) == bv_to_string_hash.end()) {
                string_to_bv_hash[s] = next_bv;
                bv_to_string_hash[next_bv] = s;
                return next_bv++;
            } 
        }
        assert(0 && "Ran out of values for type CLASSNAME");
    }
    return string_to_bv_hash[s];
}
static std::string bv_to_string(int bv){
    if(bv_to_string_hash.find(bv) == bv_to_string_hash.end()){
        int num = 0;
        while (true) {
            std::ostringstream str;
            str << num;
            std::string s = str.str();
            if(string_to_bv_hash.find(s) == string_to_bv_hash.end()){
               string_to_bv_hash[s] = bv;
               bv_to_string_hash[bv] = s;
               return s;
            }
            num++;
        }
    }
    return bv_to_string_hash[bv];
}
static void prepare() {}
static void cleanup() {
    string_to_bv_hash.clear();
    bv_to_string_hash.clear();
    next_bv = 0;
}
#endif""".replace('BITS',str(bits)).replace('CLASSNAME',classname))
    
 
    def emit_templates(self):
       add_impl(
"""
hash_space::hash_map<std::string,int> CLASSNAME::string_to_bv_hash;
hash_space::hash_map<int,std::string> CLASSNAME::bv_to_string_hash;
int CLASSNAME::next_bv = 0;

std::ostream &operator <<(std::ostream &s, const CLASSNAME &t){
    s << "\\"" << t.c_str() << "\\"";
    return s;
}
template <>
CLASSNAME _arg<CLASSNAME>(std::vector<ivy_value> &args, unsigned idx, int bound) {
    if (args[idx].fields.size())
        throw out_of_bounds(idx);
    return args[idx].atom;
}
template <>
void __ser<CLASSNAME>(ivy_ser &res, const CLASSNAME &inp) {
    res.set(inp);
}
template <>
void __deser<CLASSNAME>(ivy_deser &inp, CLASSNAME &res) {
    std::string tmp;
    inp.get(tmp);
    res = tmp;
}
#ifdef Z3PP_H_
template <>
void __from_solver<CLASSNAME>( gen &g, const  z3::expr &v, CLASSNAME &res) {
    res = CLASSNAME::bv_to_string(g.eval(v));
}
template <>
z3::expr __to_solver<CLASSNAME>( gen &g, const  z3::expr &v, CLASSNAME &val) {
//    std::cout << v << ":" << v.get_sort() << std::endl;
    return v == g.int_to_z3(v.get_sort(),CLASSNAME::string_to_bv(val));
}
template <>
void __randomize<CLASSNAME>( gen &g, const  z3::expr &apply_expr) {
    z3::sort range = apply_expr.get_sort();
    CLASSNAME value = (rand() % 2) ? "a" : "b";
    z3::expr val_expr = g.int_to_z3(range,CLASSNAME::string_to_bv(value));
    z3::expr pred = apply_expr == val_expr;
    g.add_alit(pred);
}
#endif
""".replace('CLASSNAME',self.short_name()))

    def card(self):
        return None # Note this is cardinality of the string type, not the bit vector type

    def literal(self,s):
        return '"' + (s[1:-1] if s.startswith('"') else s) + '"'

    def rand(self):
        return '((rand()%2) ? "a" : "b")' # TODO: let user control random string generation


def parse_descr(name):
    things = name.split('[')
    title = things[0]
    params = things[1:]
    if not all(t.endswith(']') for t in params):
        raise iu.IvyError(None,'bad sort descriptor: "{}"'.format(name))
    return title,[int(t[:-1]) for t in params]


cpptypes_by_title = {
    'strbv' : (StrBV,1)
}

def get_cpptype_constructor(descr):
    """ Get a cpptype constuctor with a given descriptor. The
    descriptor is a string of the form "title[int][int]...", for
    example, bv[8] to represent bit vectors of width 8.
    """
    title,params = parse_descr(descr)
    if title not in cpptypes_by_title:
        raise iu.IvyError(None,'unknown sort: "{}"'.format(title))
    cpptype,nparams = cpptypes_by_title[title]
    if len(params) != nparams:
        raise iu.IvyError(None,'expecting {} parameter in "{}"'.format(nparams,descr))
    return lambda classname: cpptype(*([classname]+params))


