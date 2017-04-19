#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

# A collection of C++ types used to model IVy types in compiled code.

from ivy_cpp import *
import ivy_utils as iu
import ivy_solver
import ivy_logic

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
static std::vector<std::string> nonces;
static std::string random_string();
static int string_to_bv(const std::string &s){
    if(string_to_bv_hash.find(s) == string_to_bv_hash.end()){
        for (; next_bv < (1<<BITS); next_bv++) {
            if(bv_to_string_hash.find(next_bv) == bv_to_string_hash.end()) {
                string_to_bv_hash[s] = next_bv;
                bv_to_string_hash[next_bv] = s;
                return next_bv++;
            } 
        }
        std::cerr << "Ran out of values for type CLASSNAME" << std::endl;
        __ivy_out << "out_of_values(CLASSNAME,\\"" << s << "\\")" << std::endl;
        for (int i = 0; i < (1<<BITS); i++)
            __ivy_out << "value(\\"" << bv_to_string_hash[i] << "\\")" << std::endl;
        __ivy_exit(1);
    }
    return string_to_bv_hash[s];
}
static std::string bv_to_string(int bv){
    if(bv_to_string_hash.find(bv) == bv_to_string_hash.end()){
        int num = 0;
        while (true) {
            // std::ostringstream str;
            // str << num;
            // std::string s = str.str();
            std::string s = random_string();
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
std::vector<std::string> CLASSNAME::nonces;
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
    CLASSNAME value;
    if (CLASSNAME::bv_to_string_hash.size() == (1<<BITS)) {
        value = CLASSNAME::bv_to_string(rand() % (1<<BITS));
    } else {
        if (CLASSNAME::nonces.size() == 0) 
           for (int i = 0; i < 2; i++)
               CLASSNAME::nonces.push_back(__random_string<CLASSNAME>());
        value = CLASSNAME::nonces[rand() % CLASSNAME::nonces.size()];
    }
    z3::expr val_expr = g.int_to_z3(range,CLASSNAME::string_to_bv(value));
    z3::expr pred = apply_expr == val_expr;
    g.add_alit(pred);
}
std::string CLASSNAME::random_string(){
    return __random_string<CLASSNAME>();
}
#endif
""".replace('BITS',str(self.bits)).replace('CLASSNAME',self.short_name()))

    def card(self):
        return None # Note this is cardinality of the string type, not the bit vector type

    def literal(self,s):
        return '"' + (s[1:-1] if s.startswith('"') else s) + '"'

    def rand(self):
        return '((rand()%2) ? "a" : "b")' # TODO: let user control random string generation


class VariantType(CppClass):
    """ A type that represents an abstract IVy type with variants.
    The parameter "variants" is a list of C types representing
    the variants. 

    The type is represented as a class with a tag field indicating
    the variant sort and a void pointer to the actual value. 

    """

    def __init__(self,classname,sort,variants):
        """ variants is the list of variant sorts """
        assert len(variants) >= 1
        CppClass.__init__(self,classname)
        self.sort = sort
        self.variants = variants
        with self:
            add_member("struct wrap {\n")
            add_member("    virtual wrap *dup() = 0;")
            add_member("    virtual ~wrap() {}")
            add_member("};\n")
            add_member("template <typename T> struct twrap : public wrap {\n")
            add_member("    T item;\n")
            add_member("    twrap(const T &item) : item(item) {}\n")
            add_member("    virtual wrap *dup() {return new twrap(item);}\n")
            add_member("};\n")
            add_member("int tag;\n")
            add_member("wrap *ptr;\n")
            add_member(classname + '(){\ntag=-1;\nptr=0;\n}\n')
            add_member(classname + '(int tag,wrap *ptr) : tag(tag),ptr(ptr) {}\n')
            add_member(classname + '(const ' + classname + '&other){\n' +
                       '    tag=other.tag;\n' +
                       '    ptr = other.ptr ? other.ptr->dup() : 0;\n' + 
                       '};\n')
            add_member(classname + '& operator=(const ' + classname + '&other){\n' +
                       '    tag=other.tag;\n' +
                       '    ptr = other.ptr ? other.ptr->dup() : 0;\n' + 
                       '    return *this;\n' +
                       '};\n')
            add_member('~' + classname + '(){if(ptr)delete ptr;}\n')
            add_member('static int temp_counter;\n')
            add_member('static void prepare() {temp_counter = 0;}\n')
            add_member('static void cleanup() {}\n')

    def isa(self,variant_idx,expr):
        """ return a test indicating whether expr is of the variant
        type with index variant_idx """
        return '(' + expr + ').tag == {}'.format(variant_idx)

    def downcast(self,variant_idx,expr):
        """ downcast an expression of this type to the given variant type.
        this is allowed to crash, if the value of the expression is not of
        the given type. """
        return '(static_cast<const {}::twrap<{}> *>(('.format(self.short_name(),self.variants[variant_idx][1]) + expr + ').ptr)->item)'

    def upcast(self,variant_idx,expr):
        return self.long_name() + '(' + str(variant_idx) + ', new ' + self.long_name() +  '::twrap<{}>('.format(self.variants[variant_idx][1]) + expr + '))'

    def card(self):
        return None

    def literal(self,s):
        return self.short_name()+'()'

    def rand(self):
        return self.short_name()+'()'

    def emit_templates(self):
       add_impl(
"""
int CLASSNAME::temp_counter = 0;

std::ostream &operator <<(std::ostream &s, const CLASSNAME &t){
    s << "{";
    switch (t.tag) {
""".replace('CLASSNAME',self.short_name()))
       for idx,var in enumerate(self.variants):
           sort,ctype = var
           add_impl('        case {}: s << "{}:" << {}; break;\n'.format(idx,sort.name,self.downcast(idx,'t')))
       add_impl(
"""
    }
    s << "}";
    return s;
}
bool operator ==(const CLASSNAME &s, const CLASSNAME &t){
    if (s.tag != t.tag) return false;
    switch (s.tag) {
""".replace('CLASSNAME',self.short_name()))
       for idx,var in enumerate(self.variants):
           sort,ctype = var
           add_impl('        case {}: return {} == {};\n'.format(idx,self.downcast(idx,'s'),self.downcast(idx,'t')))
       add_impl(
"""
    }
    return true;
}
template <>
CLASSNAME _arg<CLASSNAME>(std::vector<ivy_value> &args, unsigned idx, int bound) {
    if (args[idx].atom.size())
        throw out_of_bounds("unexpected value for sort SORTNAME: " + args[idx].atom,args[idx].pos);
    if (args[idx].fields.size() == 0)
        return CLASSNAME();
    if (args[idx].fields.size() != 1)
        throw out_of_bounds("too many fields for sort SORTNAME (expected one)",args[idx].pos);
""".replace('CLASSNAME',self.short_name()).replace('SORTNAME',self.sort.name))
       for idx,var in enumerate(self.variants):
           sort,ctype = var
           add_impl('    if (args[idx].fields[0].atom == "{}") return {};\n'.format(sort.name,self.upcast(idx,'_arg<{}>(args[idx].fields[0].fields,0,0)'.format(ctype))))
       add_impl(
"""
        throw out_of_bounds("unexpected field sort SORTNAME: " + args[idx].fields[0].atom, args[idx].pos);
}
template <>
void __ser<CLASSNAME>(ivy_ser &res, const CLASSNAME &inp) {
""".replace('CLASSNAME',self.short_name()))
       for idx,var in enumerate(self.variants):
           sort,ctype = var
           add_impl('    if (inp.tag == {}) {{res.open_tag({},"{}"); __ser(res,{}); res.close_tag();}}\n'.format(idx,idx,sort.name,self.downcast(idx,'inp')))
       add_impl(
"""
}
template <>
void __deser<CLASSNAME>(ivy_deser &res, CLASSNAME &inp) {
    std::vector<std::string> tags;
""".replace('CLASSNAME',self.short_name()))
       for idx,var in enumerate(self.variants):
           sort,ctype = var
           add_impl('    tags.push_back("{}");\n'.format(sort.name))
       add_impl(
"""
    int tag = res.open_tag(tags);
    switch (tag) {
""".replace('CLASSNAME',self.short_name()))
       for idx,var in enumerate(self.variants):
           sort,ctype = var
           add_impl('    case {}: {{{} tmp; __deser(res,tmp); inp = {}; break;}} \n'.format(idx,ctype,self.upcast(idx,'tmp')))
       add_impl(
"""
    }
    res.close_tag();
}
#ifdef Z3PP_H_
template <>
void __from_solver<CLASSNAME>( gen &g, const  z3::expr &v, CLASSNAME &res) {
""".replace('CLASSNAME',self.short_name()))
       for idx,var in enumerate(self.variants):
           sort,ctype = var
           pto = ivy_solver.solver_name(ivy_logic.Symbol('*>',ivy_logic.RelationSort([self.sort,sort])))
           add_impl('    {\n')
           add_impl('        z3::sort sort = g.sort("{}");\n'.format(sort.name))
           add_impl('        z3::func_decl pto = g.ctx.function("{}",g.sort("{}"),g.sort("{}"),g.ctx.bool_sort());\n'.format(pto,self.sort.name,sort.name))
           add_impl('        std::cout <<  g.model << std::endl;\n')
           add_impl('        Z3_ast_vector av = Z3_model_get_sort_universe(g.ctx, g.model, sort);\n')
           add_impl('        if (av) {\n')
           add_impl('            z3::expr_vector univ(g.ctx,av);\n')
           add_impl('            for (unsigned i = 0; i < univ.size(); i++){\n')
           add_impl('                if (eq(g.model.eval(pto(v,univ[i]),true),g.ctx.bool_val(true))){\n')
           add_impl('                    {} tmp;\n'.format(ctype))
           add_impl('                    __from_solver(g,univ[i],tmp);')
           add_impl('                    res = {};\n'.format(self.upcast(idx,'tmp')))
           add_impl('                }\n')
           add_impl('            }\n')
           add_impl('        }\n')
           add_impl('    }\n')
       add_impl(
"""
}
template <>
z3::expr __to_solver<CLASSNAME>( gen &g, const  z3::expr &v, CLASSNAME &val) {
//    std::cout << v << ":" << v.get_sort() << std::endl;
""".replace('CLASSNAME',self.short_name()))
       for idx,var in enumerate(self.variants):
           sort,ctype = var
           pto = ivy_solver.solver_name(ivy_logic.Symbol('*>',ivy_logic.RelationSort([self.sort,sort])))
           add_impl('    if (val.tag == {}) {{\n'.format(idx))
           add_impl('        z3::func_decl pto = g.ctx.function("{}",g.sort("{}"),g.sort("{}"),g.ctx.bool_sort());\n'.format(pto,self.sort.name,sort.name))
           add_impl('        z3::expr X = g.ctx.constant("X",g.sort("{}"));\n'.format(sort.name))
           add_impl('        {} tmp = {};\n'.format(ctype,self.downcast(idx,'val')))
           add_impl('        return exists(X,pto(v,X) && __to_solver(g,X,tmp));\n')
           add_impl('    }\n')
       add_impl(
"""
    z3::expr conj = g.ctx.bool_val(false);
""".replace('CLASSNAME',self.short_name()))
       for idx,var in enumerate(self.variants):
           sort,ctype = var
           pto = ivy_solver.solver_name(ivy_logic.Symbol('*>',ivy_logic.RelationSort([self.sort,sort])))
           add_impl('    {\n')
           add_impl('        z3::func_decl pto = g.ctx.function("{}",g.sort("{}"),g.sort("{}"),g.ctx.bool_sort());\n'.format(pto,self.sort.name,sort.name))
           add_impl('        z3::expr Y = g.ctx.constant("Y",g.sort("{}"));\n'.format(sort.name))
           add_impl('        conj = conj && forall(Y,!pto(v,Y));\n')
           add_impl('    }\n')
       add_impl(
"""
    return conj;
}
template <>
void __randomize<CLASSNAME>( gen &g, const  z3::expr &apply_expr) {
    std::ostringstream os;
    os << "__SORTNAME__tmp" << CLASSNAME::temp_counter++;
    std::string temp = os.str();
    z3::sort range = apply_expr.get_sort();
    z3::expr disj = g.ctx.bool_val(false);
""".replace('CLASSNAME',self.short_name()).replace('SORTNAME',self.sort.name))
       add_impl('int tag = rand() % {};\n'.format(len(self.variants)))
       for idx,var in enumerate(self.variants):
           sort,ctype = var
           pto = ivy_solver.solver_name(ivy_logic.Symbol('*>',ivy_logic.RelationSort([self.sort,sort])))
           add_impl('    if (tag == {}) {{\n'.format(idx))
           add_impl('        z3::func_decl pto = g.ctx.function("{}",g.sort("{}"),g.sort("{}"),g.ctx.bool_sort());\n'.format(pto,self.sort.name,sort.name))
           add_impl('        z3::expr X = g.ctx.constant(temp.c_str(),g.sort("{}"));\n'.format(sort.name))
           add_impl('        z3::expr pred = pto(apply_expr,X);\n')
           add_impl('        g.add_alit(pred);\n')
           add_impl('        __randomize<{}>(g,X);\n'.format(ctype))
           add_impl('    }\n')
       add_impl(
"""
}
#endif
""".replace('CLASSNAME',self.short_name()))

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


