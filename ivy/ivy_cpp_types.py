#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

# A collection of C++ types used to model IVy types in compiled code.

from ivy_cpp import *
import ivy_utils as iu
import ivy_solver
import ivy_logic

class XBV(CppClass):
    """ A type that represents a large type t using a bit vector. It
    maintains a mapping from bit vector values to t. Each
    time a new t constant is introduced, it is given an entry in
    the table. This can fail, however, if the number of t constants
    exceeds the number of bit vector values.
    """

    def __init__(self,classname,bits,baseclass,constructors=""):
        """ bits is the number of bits in the bit vector representation """
        CppClass.__init__(self,classname,baseclass=baseclass)
        self.bits = bits
        self.baseclass = baseclass
        with self:
                add_member(
("""
CLASSNAME(){}
CLASSNAME(const BASECLASS &s) : BASECLASS(s) {}
""" + 
constructors +
"""
size_t __hash() const { return hash_space::hash<BASECLASS>()(*this); }
#ifdef Z3PP_H_
static z3::sort z3_sort(z3::context &ctx) {return ctx.bv_sort(BITS);}
static hash_space::hash_map<BASECLASS,int> x_to_bv_hash;
static hash_space::hash_map<int,BASECLASS> bv_to_x_hash;
static int next_bv;
static std::vector<BASECLASS> nonces;
static BASECLASS random_x();
static int x_to_bv(const BASECLASS &s){
    if(x_to_bv_hash.find(s) == x_to_bv_hash.end()){
        for (; next_bv < (1<<BITS); next_bv++) {
            if(bv_to_x_hash.find(next_bv) == bv_to_x_hash.end()) {
                x_to_bv_hash[s] = next_bv;
                bv_to_x_hash[next_bv] = s;
                return next_bv++;
            } 
        }
        std::cerr << "Ran out of values for type CLASSNAME" << std::endl;
        __ivy_out << "out_of_values(CLASSNAME,\\"" << s << "\\")" << std::endl;
        for (int i = 0; i < (1<<BITS); i++)
            __ivy_out << "value(\\"" << bv_to_x_hash[i] << "\\")" << std::endl;
        __ivy_exit(1);
    }
    return x_to_bv_hash[s];
}
static BASECLASS bv_to_x(int bv){
    if(bv_to_x_hash.find(bv) == bv_to_x_hash.end()){
        int num = 0;
        while (true) {
            // std::ostringstream str;
            // str << num;
            // BASECLASS s = str.str();
            BASECLASS s = random_x();
            if(x_to_bv_hash.find(s) == x_to_bv_hash.end()){
               x_to_bv_hash[s] = bv;
               bv_to_x_hash[bv] = s;
               return s;
            }
            num++;
        }
    }
    return bv_to_x_hash[bv];
}
static void prepare() {}
static void cleanup() {
    x_to_bv_hash.clear();
    bv_to_x_hash.clear();
    next_bv = 0;
}
#endif""").replace('BITS',str(bits)).replace('CLASSNAME',classname).replace('BASECLASS',baseclass))
     
    def emit_inlines(self):
        pass

    def emit_templates(self):
       add_impl(
"""
hash_space::hash_map<BASECLASS,int> CLASSNAME::x_to_bv_hash;
hash_space::hash_map<int,BASECLASS> CLASSNAME::bv_to_x_hash;
std::vector<BASECLASS> CLASSNAME::nonces;
int CLASSNAME::next_bv = 0;

#ifdef Z3PP_H_
template <>
void __from_solver<CLASSNAME>( gen &g, const  z3::expr &v, CLASSNAME &res) {
    res = CLASSNAME::bv_to_x(g.eval(v));
}
template <>
z3::expr __to_solver<CLASSNAME>( gen &g, const  z3::expr &v, CLASSNAME &val) {
//    std::cout << v << ":" << v.get_sort() << std::endl;
    return v == g.int_to_z3(v.get_sort(),CLASSNAME::x_to_bv(val));
}
template <>
void __randomize<CLASSNAME>( gen &g, const  z3::expr &apply_expr) {
    z3::sort range = apply_expr.get_sort();
    CLASSNAME value;
    if (CLASSNAME::bv_to_x_hash.size() == (1<<BITS)) {
        value = CLASSNAME::bv_to_x(rand() % (1<<BITS));
    } else {
        if (CLASSNAME::nonces.size() == 0) 
           for (int i = 0; i < 2; i++)
               CLASSNAME::nonces.push_back(CLASSNAME::random_x());
        value = CLASSNAME::nonces[rand() % CLASSNAME::nonces.size()];
    }
    z3::expr val_expr = g.int_to_z3(range,CLASSNAME::x_to_bv(value));
    z3::expr pred = apply_expr == val_expr;
    g.add_alit(pred);
}

#endif
""".replace('BITS',str(self.bits)).replace('CLASSNAME',self.short_name()).replace('BASECLASS',self.baseclass))



class StrBV(XBV):
    """ A type that represents text strings using a bit vector. It
    maintains a mapping from bit vector values to string values. Each
    time a new string constant is introduces, it is given an entry in
    the table. This can fail, however, if the number of string constants
    exceeds the number of bit vector values.
    """
    def __init__(self,classname,bits):
        """ bits is the number of bits in the bit vector representation """
        XBV.__init__(self,classname,bits,baseclass='std::string',constructors="CLASSNAME(const char *s) : BASECLASS(s) {}")

    def emit_templates(self):
        XBV.emit_templates(self)
        add_impl(
"""
std::ostream &operator <<(std::ostream &s, const CLASSNAME &t){
    s << "\\"" << t.c_str() << "\\"";
    return s;
}
template <>
CLASSNAME _arg<CLASSNAME>(std::vector<ivy_value> &args, unsigned idx, long long bound) {
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
    BASECLASS tmp;
    inp.get(tmp);
    res = tmp;
}
//BASECLASS CLASSNAME::random_x(){
//    return __random_string<CLASSNAME>();
//}
""".replace('BITS',str(self.bits)).replace('CLASSNAME',self.short_name()).replace('BASECLASS',self.baseclass))

    def card(self):
        return None # Note this is cardinality of the string type, not the bit vector type

    def literal(self,s):
        return '"' + (s[1:-1] if s.startswith('"') else s) + '"'

    def rand(self):
        return '((rand()%2) ? "a" : "b")' # TODO: let user control random string generation

class IntBV(XBV):
    """ A type that represents a large range of integers using a small a
    bit vector. It maintains a mapping from bit vector values to
    string values. Each time a new string constant is introduces, it
    is given an entry in the table. This can fail, however, if the
    number of string constants exceeds the number of bit vector
    values.  """
    def __init__(self,classname,loval,hival,bits):
        """ bits is the number of bits in the bit vector representation """
        add_once_global("""
    struct IntClass {
        IntClass() : val(0) {}
        IntClass(long long val) : val(val) {}
        long long val;
        size_t __hash() const {return val;}
    };
""")
        add_once_global("std::ostream& operator<<(std::ostream&s, const IntClass &v) {return s << v.val;}\n")
        add_once_global("bool operator==(const IntClass &x, const IntClass &y) {return x.val == y.val;}\n")
        self.loval = loval
        self.hival = hival
        XBV.__init__(self,classname,bits,baseclass='IntClass',constructors="CLASSNAME(long long v) : BASECLASS(v) {}")

    def emit_templates(self):
        XBV.emit_templates(self)
        add_impl(
"""
std::ostream &operator <<(std::ostream &s, const CLASSNAME &t){
    s << t.val;
    return s;
}
template <>
CLASSNAME _arg<CLASSNAME>(std::vector<ivy_value> &args, unsigned idx, long long bound) {
    if (args[idx].fields.size())
        throw out_of_bounds(idx);
    CLASSNAME res;
//    res.val = atoll(args[idx].atom.c_str());
    std::istringstream s(args[idx].atom.c_str());
    s.unsetf(std::ios::dec);
    s.unsetf(std::ios::hex);
    s.unsetf(std::ios::oct);
    s  >> res.val;
//    unsigned long long res = atoll(args[idx].atom.c_str());
    return res;
}
template <>
void __ser<CLASSNAME>(ivy_ser &res, const CLASSNAME &inp) {
    res.set(inp.val);
}
template <>
void __deser<CLASSNAME>(ivy_deser &inp, CLASSNAME &res) {
    inp.get(res.val);
}
BASECLASS CLASSNAME::random_x(){
    return RAND;
}
""".replace('BITS',str(self.bits)).replace('CLASSNAME',self.short_name()).replace('BASECLASS',self.baseclass).replace('LOVAL',str(self.loval)).replace('HIVAL',str(self.hival)).replace('RAND',self.rand()))

    def card(self):
        return self.hival - self.loval + 1 # Note this is cardinality of the int type, not the bit vector type

    def literal(self,s):
        return str(s)

    def rand(self):
            return '((rand()%{}) + {})'.format(self.card(),self.loval) # TODO: let user control random string generation


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
            add_member("    virtual bool deref() = 0;")
            add_member("    virtual ~wrap() {}")
            add_member("};\n")
            add_member("template <typename T> struct twrap : public wrap {\n")
            add_member("    unsigned refs;\n")
            add_member("    T item;\n")
            add_member("    twrap(const T &item) : refs(1), item(item) {}\n")
            add_member("    virtual wrap *dup() {refs++; return this;}\n")
            add_member("    virtual bool deref() {return (--refs) != 0;}\n")
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
            add_member('~' + classname + '(){if(ptr){if (!ptr->deref()) delete ptr;}}\n')
            add_member('static int temp_counter;\n')
            add_member('static void prepare() {temp_counter = 0;}\n')
            add_member('static void cleanup() {}\n')
            add_member('size_t __hash() const {\n')
            add_member('    switch(tag) {\n')
            for idx,var in enumerate(self.variants):
                sort,ctype = var
                add_member('        case {}: return {} + hash_space::hash<{}>()({});\n'
                             .format(idx,idx,ctype,self.downcast(idx,'(*this)')))
            add_member('    }\n')
            add_member('    return 0;\n')
            add_member('}\n')
            add_member("template <typename T> static const T &unwrap(const " + classname + " &x) {\n")
            add_member("    return ((static_cast<const twrap<T> *>(x.ptr))->item);\n")
            add_member('}\n')
            add_member("template <typename T> static T &unwrap(" + classname + " &x) {\n")
            add_member("     twrap<T> *p = static_cast<twrap<T> *>(x.ptr);\n")
            add_member("     if (p->refs > 1) {\n")
            add_member("         p = new twrap<T> (p->item);\n")
            add_member("     }\n")
            add_member("     return ((static_cast<twrap<T> *>(p))->item);\n")
            add_member('}\n')


    def isa(self,variant_idx,expr):
        """ return a test indicating whether expr is of the variant
        type with index variant_idx """
        return '((' + expr + ').tag == {})'.format(variant_idx)

    def downcast(self,variant_idx,expr):
        """ downcast an expression of this type to the given variant type.
        this is allowed to crash, if the value of the expression is not of
        the given type. """
        return '{}::unwrap< {} >('.format(self.short_name(),self.variants[variant_idx][1]) + expr + ')'

    def upcast(self,variant_idx,expr):
        return self.long_name() + '(' + str(variant_idx) + ', new ' + self.long_name() +  '::twrap<{}>('.format(self.variants[variant_idx][1]) + expr + '))'

    def card(self):
        return None

    def literal(self,s):
        return self.short_name()+'()'

    def rand(self):
        return self.short_name()+'()'

    def emit_inlines(self):
        add_global(
"""
bool operator ==(const CLASSNAME &s, const CLASSNAME &t){
    if (s.tag != t.tag) return false;
    switch (s.tag) {
""".replace('CLASSNAME',self.short_name()))
        for idx,var in enumerate(self.variants):
            sort,ctype = var
            add_global('        case {}: return {} == {};\n'.format(idx,self.downcast(idx,'s'),self.downcast(idx,'t')))
        add_global(
"""
    }
    return true;
}
"""
)

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
template <>
CLASSNAME _arg<CLASSNAME>(std::vector<ivy_value> &args, unsigned idx, long long bound) {
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
           add_impl('        // std::cout <<  g.model << std::endl;\n')
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
    return title,[int(t[:-1],0) for t in params]


cpptypes_by_title = {
    'strbv' : (StrBV,1),
    'intbv' : (IntBV,3)
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


