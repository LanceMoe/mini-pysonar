# pysonar.py - a Python version of PySonar static analyzer for Python
# Copyright (C) 2011 Yin Wang (yinwang0@gmail.com)

import sys
import re
from ast import *
from lists import *


####################################################################
## global parameters
####################################################################
IS = isinstance


####################################################################
## utilities
####################################################################
def iter_fields(node):
    '''Iterate over all existing fields, excluding 'ctx'.'''
    for field in node._fields:
        try:
            if field != 'ctx':
                yield field, getattr(node, field)
        except AttributeError:
            pass

# for debugging


def sz(s):
    # return node_size(parse(s), True)
    return 0


def dp(s):
    return list(map(dump, parse(s).body))


def pf(file):
    import cProfile
    cProfile.run('sonar(' + file + ')', sort='cumulative')


####################################################################
## test on AST nodes
####################################################################
def is_atom(x):
    return type(x) in [int, str, bool, float]


def is_def(node):
    return IS(node, FunctionDef) or IS(node, ClassDef)


##################################################################
# per-node information store
##################################################################
history = {}


def put_info(exp, item):
    if exp in history:
        seen = history[exp]
    else:
        seen = []
    history[exp] = union([seen, item])


def get_info(exp):
    return history[exp]


##################################################################
# types used by pysonar
##################################################################
class Type:
    pass


unknown_count = 0


class UnknownType(Type):
    def __init__(self, name=None):
        global unknown_count
        if name != None:
            self.name = name + str(unknown_count)
        else:
            self.name = '_' + str(unknown_count)
        unknown_count += 1

    def __repr__(self):
        return str(self.name)


class PrimType(Type):
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return str(self.name)

    def __eq__(self, other):
        if IS(other, PrimType):
            return self.name == other.name
        else:
            return False

    def __ne__(self, other):
        return not self.__eq__(other)


class ClassType(Type):
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return 'class:' + self.name

    def __eq__(self, other):
        if IS(other, ClassType):
            return self.name == other.name
        else:
            return False

    def __ne__(self, other):
        return not self.__eq__(other)


class FuncType(Type):
    def __init__(self, from_type, to_type):
        self.from_type = from_type
        self.to_type = to_type

    def __repr__(self):
        return str(self.from_type) + ' -> ' + str(self.to_type)

    def __eq__(self, other):
        if IS(other, FuncType):
            return ((self.from_type == other.from_type) and
                    self.to_type == other.to_type)
        else:
            return False

    def __ne__(self, other):
        return not self.__eq__(other)


class Closure(Type):
    def __init__(self, func, env):
        self.func = func
        self.env = env
        self.defaults = []

    def __repr__(self):
        return str(self.func)


class TupleType(Type):
    def __init__(self, elts):
        self.elts = elts

    def __repr__(self):
        return 'tup:' + str(self.elts)

    def __eq__(self, other):
        if IS(other, TupleType):
            if len(self.elts) != len(other.elts):
                return False
            else:
                for i in range(len(self.elts)):
                    if self.elts[i] != other.elts[i]:
                        return False
                return True
        else:
            return False

    def __ne__(self, other):
        return not self.__eq__(other)


class ListType(Type):
    def __init__(self, elts):
        self.elts = elts

    def __repr__(self):
        return 'list:' + str(self.elts)

    def __eq__(self, other):
        if IS(other, ListType):
            if len(self.elts) != len(other.elts):
                return False
            else:
                for i in range(len(self.elts)):
                    if self.elts[i] != other.elts[i]:
                        return False
                return True
        else:
            return False

    def __ne__(self, other):
        return not self.__eq__(other)


class DictType(Type):
    def __init__(self, dic):
        self.dic = dic

    def __repr__(self):
        return 'dict:' + str(self.dic)

    # any hashable value can be used as keys
    # any object can be used as values
    # so we can know almost nothing about the dictionaries
    def __eq__(self, other):
        if IS(other, DictType):
            return True
        else:
            return False

    def __ne__(self, other):
        return not self.__eq__(other)


class UnionType(Type):
    def __init__(self, elts):
        self.elts = elts

    def __repr__(self):
        return 'U:' + str(self.elts)


# singleton primtive types
contType = PrimType('cont')             # continuation type
bottomType = PrimType('_|_')            # non-terminating recursion


# need to rewrite this when we have recursive types
def type_equal(t1, t2):
    if IS(t1, list) and IS(t2, list):
        for bd1 in t1:
            if bd1 not in t2:
                return False
        return True
    else:
        return t1 == t2


def subtype_bindings(rec1, rec2):
    def find(a, rec2):
        for b in rec2:
            if (first(a) == first(b)) and type_equal(rest(a), rest(b)):
                return True
        return False
    for a in rec1:
        if not find(a, rec2):
            return False
    return True


def union(ts):
    u = []
    for t in ts:
        if IS(t, list):                 # already a union (list)
            for b in t:
                if b not in u:
                    u.append(b)
        else:
            if t not in u:
                u.append(t)
    return u


####################################################################
## type inferencer
####################################################################
class Bind:
    def __init__(self, typ, loc):
        self.typ = typ
        self.loc = loc

    def __repr__(self):
        return '(' + str(self.typ) + ' <~~ ' + str(self.loc) + ')'

    def __iter__(self):
        return BindIterator(self)

    def __eq__(self, other):
        return IS(other, Bind) and self.typ == other.typ and self.loc == other.loc


class BindIterator:
    def __init__(self, p):
        self.p = p
        self.cur = 0

    def __next__(self):
        if self.cur == 2:
            raise StopIteration
        elif self.cur == 0:
            self.cur += 1
            return self.p.typ
        else:
            self.cur += 1
            return self.p.loc


def type_only(bs):
    return union(bs)


# test whether a type is in a union
def in_union(t, u):
    for t2 in u:
        if t == t2:
            return True
    return False


def remove_type(t, u):
    return filter(lambda x: x != t, u)


# combine two environments, make unions when necessary
# only assocs appear in both envs are preserved
# use a variable bound in only one branch will cause type error
def merge_env(env1, env2):
    ret = nil
    for p1 in env1:
        p2 = assq(first(p1), env2)
        if p2 != None:
            ret = ext(first(p1), union([rest(p1), rest(p2)]), ret)
    return ret


# compare both str's and Name's for equivalence, because
# keywords are str's (bad design of the ast)
def get_id(x):
    if IS(x, Name):
        return x.id
    else:
        return x


def bind(target, value, env):
    if IS(target, Name) or IS(target, str):
        u = value
        put_info(target, u)
        return ext(get_id(target), u, env)

    # ignored for now
    # elif IS(target, Tuple) or IS(target, List):
    #     if IS(value, TupleType) or IS(value, List):
    #         if len(target.elts) == len(value.elts):
    #             for i in range(len(value.elts)):
    #                 env = bind(target.elts[i], value.elts[i], env)
    #             return env
    #         elif len(target.elts) < len(value.elts):
    #             put_info(target, ValueError('too many values to unpack'))
    #             return env
    #         else:
    #             put_info(target, ValueError('too few values to unpack'))
    #             return env
    #     else:
    #         put_info(value, TypeError('non-iterable object'))
    #         return env
    else:
        put_info(target, SyntaxError('not assignable'))
        return env


def on_stack(call, args, stk):
    for p1 in stk:
        call2 = first(p1)
        args2 = rest(p1)
        if call == call2 and subtype_bindings(args, args2):
            return True
    return False


# invoke one closure
def invoke1(call, clo, env, stk):

    if (clo == bottomType):
        return [bottomType]

    # Even if operator is not a closure, resolve the
    # arguments for partial information.
    if not IS(clo, Closure):
        for a in call.args:
            t1 = infer(a, env, stk)
        for k in call.keywords:
            t2 = infer(k.value, env, stk)
        err = TypeError('calling non-callable', clo)
        put_info(call, err)
        return [err]

    func = clo.func
    fenv = clo.env
    pos = nil
    kwarg = nil

    # bind positionals first
    poslen = min(len(func.args.args), len(call.args))
    for i in range(poslen):
        t = infer(call.args[i], env, stk)
        pos = bind(func.args.args[i], t, pos)

    # put extra positionals into vararg if provided
    # report error and go on otherwise
    if len(call.args) > len(func.args.args):
        if func.args.vararg == None:
            err = TypeError('excess arguments to function')
            put_info(call, err)
            return [err]
        else:
            ts = []
            for i in range(len(func.args.args), len(call.args)):
                t = infer(call.args[i], env, stk)
                ts = ts + t
            pos = bind(func.args.vararg, ts, pos)

    # bind keywords, collect kwarg
    ids = list(map(get_id, func.args.args))
    for k in call.keywords:
        ts = infer(k.value, env, stk)
        tloc1 = lookup(k.arg, pos)
        if tloc1 != None:
            put_info(call, TypeError('multiple values for keyword argument',
                                     k.arg, tloc1))
        elif k.arg not in ids:
            kwarg = bind(k.arg, ts, kwarg)
        else:
            pos = bind(k.arg, ts, pos)

    # put extras in kwarg or report them
    if kwarg != nil:
        if func.args.kwarg != None:
            pos = bind(func.args.kwarg,
                       DictType(reverse(kwarg)),
                       pos)
        else:
            put_info(call, TypeError('unexpected keyword arguements', kwarg))
    elif func.args.kwarg != None:
        pos = bind(func.args.kwarg, DictType(nil), pos)

    # bind defaults, avoid overwriting bound vars
    # types for defaults are already inferred when the function was defined
    i = len(func.args.args) - len(func.args.defaults)
    ndefaults = len(func.args.args)
    for j in range(len(clo.defaults)):
        tloc = lookup(get_id(func.args.args[i]), pos)
        if tloc == None:
            pos = bind(func.args.args[i], clo.defaults[j], pos)
            i += 1

    # finish building the input type
    from_type = maplist(lambda p: Pair(first(p), type_only(rest(p))), pos)

    # check whether the same call site is on stack with same input types
    # if so, we are back to a loop, terminate
    if on_stack(call, from_type, stk):
        return [bottomType]

    # push the call site onto the stack and analyze the function body
    stk = ext(call, from_type, stk)
    fenv = append(pos, fenv)
    to = infer(func.body, fenv, stk)

    # record the function type
    put_info(func, FuncType(reverse(from_type), to))
    return to


# invoke a union of closures. call invoke1 on each of them and collect
# their return types into a union
def invoke(call, env, stk):
    clos = infer(call.func, env, stk)
    to_types = []
    for clo in clos:
        t = invoke1(call, clo, env, stk)
        to_types = to_types + t
    return to_types


# pre-bind names to functions in sequences (should add classes later)
def close(ls, env):
    for e in ls:
        if IS(e, FunctionDef):
            c = Closure(e, None)
            env = ext(e.name, [c], env)
    return env


def is_terminating(t):
    return not in_union(contType, t)


def finalize(t):
    return remove_type(contType, t)


# infer a sequence of statements
def infer_seq(exp, env, stk):

    if exp == []:                       # reached end without return
        return ([contType], env)

    e = exp[0]
    if IS(e, If):
        tt = infer(e.test, env, stk)
        (t1, env1) = infer_seq(e.body, close(e.body, env), stk)
        (t2, env2) = infer_seq(e.orelse, close(e.orelse, env), stk)

        if is_terminating(t1) and is_terminating(t2):                   # both terminates
            for e2 in exp[1:]:
                put_info(e2, TypeError('unreachable code'))
            return (union([t1, t2]), env)

        elif is_terminating(t1) and not is_terminating(t2):             # t1 terminates
            (t3, env3) = infer_seq(exp[1:], env2, stk)
            t2 = finalize(t2)
            return (union([t1, t2, t3]), env3)

        elif not is_terminating(t1) and is_terminating(t2):             # t2 terminates
            (t3, env3) = infer_seq(exp[1:], env1, stk)
            t1 = finalize(t1)
            return (union([t1, t2, t3]), env3)
        else:                                                         # both non-terminating
            (t3, env3) = infer_seq(exp[1:], merge_env(env1, env2), stk)
            t1 = finalize(t1)
            t2 = finalize(t2)
            return (union([t1, t2, t3]), env3)

    elif IS(e, Assign):
        t = infer(e.value, env, stk)
        for x in e.targets:
            env = bind(x, t, env)
        return infer_seq(exp[1:], env, stk)

    elif IS(e, FunctionDef):
        cs = lookup(e.name, env)
        for c in cs:
            c.env = env                          # create circular env to support recursion
        for d in e.args.defaults:                # infer types for default arguments
            dt = infer(d, env, stk)
            c.defaults.append(dt)
        return infer_seq(exp[1:], env, stk)

    elif IS(e, Return):
        t1 = infer(e.value, env, stk)
        (t2, env2) = infer_seq(exp[1:], env, stk)
        for e2 in exp[1:]:
            put_info(e2, TypeError('unreachable code'))
        return (t1, env)

    elif IS(e, Expr):
        t1 = infer(e.value, env, stk)
        return infer_seq(exp[1:], env, stk)

    else:
        raise TypeError('recognized node in effect context', e)


# main type inferencer
def infer(exp, env, stk):

    if IS(exp, Module):
        return infer(exp.body, env, stk)

    elif IS(exp, list):
        env = close(exp, env)
        (t, ignoreEnv) = infer_seq(exp, env, stk)    # env ignored (out of scope)
        return t

    elif IS(exp, Num):
        return [PrimType(type(exp.n))]

    elif IS(exp, Str):
        return [PrimType(type(exp.s))]

    elif IS(exp, Name):
        b = lookup(exp.id, env)
        if (b != None):
            put_info(exp, b)
            return b
        else:
            try:
                t = type(eval(exp.id))     # try use information from Python interpreter
                return [PrimType(t)]
            except NameError as err:
                put_info(exp, err)
                return [err]

    elif IS(exp, Lambda):
        c = Closure(exp, env)
        for d in exp.args.defaults:
            dt = infer(d, env, stk)
            c.defaults.append(dt)
        return [c]

    elif IS(exp, Call):
        return invoke(exp, env, stk)

    ## ignore complex types for now
    # elif IS(exp, List):
    #     eltTypes = []
    #     for e in exp.elts:
    #         t = infer(e, env, stk)
    #         eltTypes.append(t)
    #     return [Bind(ListType(eltTypes), exp)]

    # elif IS(exp, Tuple):
    #     eltTypes = []
    #     for e in exp.elts:
    #         t = infer(e, env, stk)
    #         eltTypes.append(t)
    #     return [Bind(TupleType(eltTypes), exp)]

    else:
        return [UnknownType()]


##################################################################
# drivers(wrappers)
##################################################################
def parse_file(filename):
    f = open(filename, 'r')
    return parse(f.read())


# clean up globals
def clear():
    history.clear()
    global unknown_count
    unknown_count = 0


def nodekey(node):
    if hasattr(node, 'lineno'):
        return node.lineno
    else:
        return sys.maxint


# check a single (parsed) expression
def check_exp(exp):
    clear()
    ret = infer(exp, nil, nil)
    if history.keys() != []:
        print('---------------------------- history ----------------------------')
        for k in sorted(history.keys(), key=nodekey):
            print(k, ':', history[k])
        print('\n')
    return ret


# check a string
def check_string(s):
    return check_exp(parse(s))


# check a file
def check_file(filename):
    f = open(filename, 'r')
    return check_string(f.read())


###################################################################
# hacky printing support for AST
###################################################################
def dump(node, annotate_fields=True, include_attributes=False):
    def _format(node):
        if isinstance(node, AST):
            fields = [(a, _format(b)) for a, b in iter_fields(node)]
            rv = '%s(%s' % (node.__class__.__name__, ', '.join(
                ('%s=%s' % field for field in fields)
                if annotate_fields else
                (b for a, b in fields)
            ))
            if include_attributes and node._attributes:
                rv += fields and ', ' or ' '
                rv += ', '.join('%s=%s' % (a, _format(getattr(node, a)))
                                for a in node._attributes)
            return rv + ')'
        elif isinstance(node, list):
            return '[%s]' % ', '.join(_format(x) for x in node)
        return repr(node)
    if not isinstance(node, AST):
        raise TypeError('expected AST, got %r' % node.__class__.__name__)
    return _format(node)


def print_list(ls):
    if (ls == None or ls == []):
        return ''
    elif (len(ls) == 1):
        return str(ls[0])
    else:
        return str(ls)


def print_ast(node):
    if IS(node, Module):
        ret = 'module:' + str(node.body)
    elif IS(node, FunctionDef):
        ret = 'fun:' + str(node.name)
    elif IS(node, ClassDef):
        ret = 'class:' + str(node.name)
    elif IS(node, Call):
        ret = ('call:' + str(node.func)
               + ':(' + print_list(node.args) + ')')
    elif IS(node, Assign):
        ret = ('(' + print_list(node.targets)
               + ' <- ' + print_ast(node.value) + ')')
    elif IS(node, If):
        ret = ('if ' + str(node.test)
               + ':' + print_list(node.body)
               + ':' + print_list(node.orelse))
    elif IS(node, Compare):
        ret = (str(node.left) + ':' + print_list(node.ops)
               + ':' + print_list(node.comparators))
    elif IS(node, Name):
        ret = str(node.id)
    elif IS(node, Num):
        ret = str(node.n)
    elif IS(node, Str):
        ret = f'\"{str(node.s)}\"'
    elif IS(node, Return):
        ret = 'return ' + repr(node.value)
    elif IS(node, Expr):
        ret = 'expr:' + str(node.value)
    elif IS(node, BinOp):
        ret = (str(node.left) + ' '
               + str(node.op) + ' '
               + str(node.right))
    elif IS(node, Mult):
        ret = '*'
    elif IS(node, Add):
        ret = '+'
    elif IS(node, Pass):
        ret = 'pass'
    elif IS(node, list):
        ret = print_list(node)
    else:
        ret = str(type(node))

    if hasattr(node, 'lineno'):
        return (re.sub('@[0-9]+', '', ret)
                + '@' + str(node.lineno))
    else:
        return ret


def install_printer():
    import inspect
    import ast
    for name, obj in inspect.getmembers(ast):
        if (inspect.isclass(obj) and not (obj == AST)):
            obj.__repr__ = print_ast


install_printer()


# test the checker on a file
check_file('tests/is_prime.py')
