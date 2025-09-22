# SPDX-FileCopyrightText: Copyright (c) 2022 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
# SPDX-License-Identifier: MIT
#
# Permission is hereby granted, free of charge, to any person obtaining a
# copy of this software and associated documentation files (the "Software"),
# to deal in the Software without restriction, including without limitation
# the rights to use, copy, modify, merge, publish, distribute, sublicense,
# and/or sell copies of the Software, and to permit persons to whom the
# Software is furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
# THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
# FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
# DEALINGS IN THE SOFTWARE.

from enum import Enum, auto, unique
import itertools
import os
import json
import logging
from .common import *

shift = 4
type_annotations = False

class IrContext:
    '''
    IR Context contains information to guide IR generation through the chain
    of instantiated modules
    '''

    def __init__(self, name = None, replacements = {}):
        self.name = name
        self.replacements = replacements.copy()

    def introduce(self, name, expr):
        assert name not in self.replacements, f"Name `{name}` is found in {self.replacements}"
        self.replacements[name] = expr

    def replace(self, name):
        if name in self.replacements:
            return self.replacements[name]
        return None

class IrContextStack:
    def __init__(self):
        self.stack = None
        self.is_local_defs = False
        self.extends = None

    def initialize(self):
        logging.debug(f'IR Initialize')
        top_level_context = IrContext()
        self.stack = [top_level_context]
        self.extends = []
        self.is_local_defs = False

    def new_extends(self, name):
        if name in self.extends:
            return False
        self.extends.append(name)
        return True

    def push(self, ir_context):
        self.stack.append(ir_context)

    def pop(self):
        assert len(self.stack) > 1
        self.stack = self.stack[:-1]
        # Never pop toplevel context
        assert self.stack

    def get_context(self):
        assert self.stack
        return self.stack[-1]

    def in_instance(self):
        return len(self.stack) > 1

    def start_local_defs(self):
        self.is_local_defs = True

    def end_local_defs(self):
        self.is_local_defs = False

    def introduce(self, name, is_def0):
        if self.is_local_defs:
            return name

        names = [ctx.name for ctx in self.stack if ctx.name]
        names.append(name)
        new_name = '!'.join(names)

        name_replacement = {
            "type": "Untyped",
            "kind": "NameEx",
            "name": new_name
        }

        if is_def0:
            replacement = {
                "type": "Untyped",
                "kind": "OperEx",
                "oper": "OPER_APP",
                "args": [name_replacement]
            }
        else:
            replacement = name_replacement

        logging.debug(f'IR Introduce `{name}`->`{new_name}`, is_def0={is_def0}, repl={replacement}')

        # Propagate replacement to all contexts, where it should be visible
        # Note that replacement value must be fully resolved already
        visible_name = name
        for ctx in reversed(self.stack):
            ctx.introduce(visible_name, replacement)
            visible_name = f'{ctx.name}!{visible_name}' if ctx.name else visible_name
        return new_name

    def find_subst(self, name):
        assert self.stack
        current_ctx = self.stack[-1]
        if name in current_ctx.replacements:
            return current_ctx.replacements[name]
        parent_ctx = self.stack[-2] if len(self.stack) > 1 else None
        if not parent_ctx:
            return None
        return parent_ctx.replace(name)

    def replace(self, name):
        return self.get_context().replace(name)

ir_context_stack = IrContextStack()

def ir_context_initialize():
    ir_context_stack.initialize()

def ir_context_push(name, replacements):
    ir_context_stack.push(IrContext(name, replacements))

def ir_context_pop():
    ir_context_stack.pop()

def ir_context_in_instance():
    return ir_context_stack.in_instance()

def ir_context_introduce(name, is_def0 = False):
    return ir_context_stack.introduce(name, is_def0)

def ir_context_start_local_defs():
    return ir_context_stack.start_local_defs()

def ir_context_end_local_defs():
    return ir_context_stack.end_local_defs()

def ir_context_extends(module_name):
    return ir_context_stack.new_extends(module_name)

# Finding substitution is only needed for variables and constants
# in instantiated modules: if a suitable substitution is not
# found in the current context, it is searched in the parent one
def ir_context_find_subst(name):
    return ir_context_stack.find_subst(name)

def ir_context_replace(name):
    return ir_context_stack.replace(name)

def set_type_annotations(ann):
    global type_annotations
    type_annotations = ann

def type_ann_wrap(typeStr):
    return f'\* @type: {typeStr};'

def type_ann(type):
    return type_ann_wrap(type.apalache())

def with_ann(node, ann = None):
    global type_annotations
    if not type_annotations or not ann:
        return node
    return unlines([type_ann(ann), node])

# Guess what expressions can be printed without parens
def within_parens(expr):
    r = expr.pretty()
    factors = [
        Num, Str, Bool,
        VarRef, Def0Ref, Def1Ref, ConstRef, LocalRef,
        Def1App,
        Boxed,
        Set0, Set1, Set2,
        Tuple, Fun, Record,
        Not, Prime, At, UnaryMinus]
    if any(isinstance(expr, n) for n in factors):
        return r
    return f'({r})'

class UninterpretedDef:
    def __init__(self, dfn):
        self.dfn = dfn

    def ir(self):
        assert False, "Not implemented"

    def pretty(self):
        return self.dfn

class OneLineComment:
    def __init__(self, comment):
        self.comment = comment

    def pretty(self):
        return f'\\* {self.comment}'

    def ir(self):
        return []

class MultiLineComment:
    def __init__(self, *comments):
        self.comments = comments

    def pretty(self):
        return f'(* {unlines(self.comments)} *)'

    def ir(self):
        return []

class Extends:
    def __init__(self, *modules):
        self.modules = modules

    def pretty(self):
        r = ''
        if self.modules:
            r = f'EXTENDS {commas(m.name for m in self.modules)}'
        return r

    def ir(self):
        extends_ir = []
        for module in self.modules:
            if not ir_context_extends(module.name):
                continue
            extends_ir.extend(module.ir())
        return extends_ir

class Instance:
    def __init__(self, module, with_stmt = {}, name = None):
        self.module = module
        self.with_stmt = with_stmt
        self.name = name

    def pretty(self):
        prefix = f'{self.name} == ' if self.name else ''
        instance = f'{prefix}INSTANCE {self.module.name}'
        w = [f'{n} <- {e.pretty()}' for n, e in self.with_stmt.items()]
        if w:
            ws = indent(',\n'.join(w))
            instance += ' WITH'
            instance = unlines([instance, ws])

        return instance

    def ir(self):
        replacements = {}
        for name in self.with_stmt:
            replacements[name] = self.with_stmt[name].ir()

        ir_context_push(self.name, replacements)
        decls = self.module.ir()
        ir_context_pop()

        return decls

class Constants:
    def __init__(self, consts):
        assert isinstance(consts, dict)
        assert len(consts) != 0

        self.consts = consts

    def pretty(self):
        from .type import str_t
        r = []
        for c,desc in self.consts.items():
            args = f'({commas("_" for _ in range(desc.arity))})' if desc.arity > 0 else ''
            decl = f'{c}{args}'
            # Model values in Apalache are encoded as string values
            ty = desc.type if desc.init else str_t
            r.append(with_ann(decl, ty))

        r1 = ',\n'.join(r)

        if self.consts:
            r = unlines([
                f'CONSTANT',
                indent(r1)])
        return r

    def ir(self):
        from .type import str_t
        # All constants must be replaced in INSTANCE
        if ir_context_in_instance():
            return []
        r = []
        for c,desc in self.consts.items():
            args = f'({commas("_" for _ in range(desc.arity))})' if desc.arity > 0 else ''
            decl = f'{c}{args}'
            # Model values in Apalache are encoded as string values
            ty = desc.type if desc.init else str_t
            r.append(
                {
                    "type": ty.apalache(),
                    "kind": "TlaConstDecl",
                    "name": c
                })

        return r

class Assume:
    def __init__(self, expr, name = None):
        self.expr = expr
        self.name = name

    def pretty(self):
        if self.name:
            return f'ASSUME {self.name} == {self.expr.pretty()}'
        return f'ASSUME {self.expr.pretty()}'

    def ir(self):
        assert self.name == None, "Not supported in IR"
        return {
            "type": "Untyped",
            "kind": "TlaAssumeDecl",
            "body": self.expr.ir()
        }

class At:
    def pretty(self):
        return '@'

# Order 0 definition
class Def0:
    def __init__(self, name, expr, ann = None):
        self.name = name
        self.ann = ann
        self.expr = expr

    def pretty(self):
        df = f'{self.name} == {self.expr.pretty()}'
        return with_ann(df, self.ann)

    def ir(self):
        name = ir_context_introduce(self.name, is_def0 = True)
        return {
          "type": self.ann.apalache() if self.ann else "Untyped",
          "kind": "TlaOperDecl",
          "name": name,
          "formalParams": [],
          "isRecursive": False,
          "body": self.expr.ir()
        }

# Order 1 definition
class Def1:
    def __init__(self, name, args, expr, ann = None, recursive = False):
        self.name = name
        self.ann = ann
        self.args = args
        self.expr = expr
        self.recursive = recursive
        assert len(args) > 0

    def pretty(self):
        df = f'{self.name}({commas(self.args)}) == {self.expr.pretty()}'
        rec = [f'RECURSIVE {self.name}({commas("_" for _ in self.args)})'] if self.recursive else []
        xs = rec + [with_ann(df, self.ann)]
        return unlines(xs)

    def ir(self):
        assert not self.recursive, "Not supported"

        name = ir_context_introduce(self.name)

        args = [
            {
              "kind": "OperParam",
              "name": arg,
              "arity": 0
            }
            for arg in self.args
        ]

        return {
          "type": self.ann.apalache() if self.ann else "Untyped",
          "kind": "TlaOperDecl",
          "name": name,
          "formalParams": args,
          "isRecursive": self.recursive,
          "body": self.expr.ir()
        }

# Order 2 definition
class Def2:
    def __init__(self, name, args1, args2, expr, ann = None):
        self.name = name
        self.ann = ann
        self.args1 = args1
        self.args2 = args2
        self.expr = expr
        assert len(args2) > 0

    def pretty(self):
        args2 = [f'{arg}(_)' for arg in self.args2]
        df = f'{self.name}({commas(self.args1 + args2)}) == {self.expr.pretty()}'
        return with_ann(df, self.ann)

    def ir(self):
        name = ir_context_introduce(self.name)

        args = [
            {
              "kind": "OperParam",
              "name": arg,
              "arity": 0
            }
            for arg in self.args1
        ]
        args.extend([
            {
              "kind": "OperParam",
              "name": arg,
              "arity": 1
            }
            for arg in self.args2
        ])

        return {
          "type": self.ann.apalache() if self.ann else "Untyped",
          "kind": "TlaOperDecl",
          "name": name,
          "formalParams": args,
          "isRecursive": False,
          "body": self.expr.ir()
        }

class Lambda:
    def __init__(self, args, expr, ann = None):
        self.ann = ann
        self.args = args
        self.expr = expr

    def pretty(self):
        df = indent_but_first('', f'LAMBDA {commas(self.args)} : {self.expr.pretty()}')
        return with_ann(df, self.ann)

    def ir(self):
        lam = {
            "type": "Untyped",
            "kind": "LetInEx",
            "body": {
                "type": "Untyped",
                "kind": "NameEx",
                "name": "LAMBDA"
            },
            "decls": [
                {
                    "type": self.ann.apalache() if self.ann else "Untyped",
                    "kind": "TlaOperDecl",
                    "name": "LAMBDA",
                    "formalParams": [
                        {
                            "kind": "OperParam",
                            "name": arg,
                            "arity": 0
                        }
                        for arg in self.args
                    ],
                    "isRecursive": False,
                    "body": self.expr.ir()
                }
            ]
        }
        return lam

class VarRef:
    def __init__(self, id):
        self.id = id

    def pretty(self):
        return self.id

    def ir(self):
        expr = ir_context_find_subst(self.id)
        return expr if expr else {
            "type": "Untyped",
            "kind": "NameEx",
            "name": self.id
          }

class LocalRef:
    def __init__(self, id):
        self.id = id

    def pretty(self):
        return self.id

    def ir(self):
        return {
            "type": "Untyped",
            "kind": "NameEx",
            "name": self.id
          }

class ConstRef:
    def __init__(self, id):
        self.id = id

    def pretty(self):
        return self.id

    def ir(self):
        expr = ir_context_find_subst(self.id)
        logging.debug(f'IR ConstRef: {self.id} -> {expr}')
        return expr if expr else {
            "type": "Untyped",
            "kind": "NameEx",
            "name": self.id
          }

# Apalache changes names for operators in standard modules
# if those operators are built in (not just imported from TLA+ file)
builtin_table = {
    'Len' : 'Sequences!Len',
    'Append' : 'Sequences!Append',
    'Head' : 'Sequences!Head',
    'Tail' : 'Sequences!Tail',
    'SubSeq' : 'Sequences!SubSeq',
    'Cardinality' : 'FiniteSets!Cardinality',
    'ApaFoldSet' : 'Apalache!ApaFoldSet',
}

# For standard operators, which are not builtin, IR uses their
# names without module prefix
standard_table = {
    'SelectSeq' : 'SelectSeq',
    'IsABag' : 'IsABag',
    'BagToSet' : 'BagToSet',
    'SetToBag' : 'SetToBag',
    'BagIn' : 'BagIn',
    'EmptyBag' : 'EmptyBag',
    'BagUnion' : 'BagUnion',
    'SubBag' : 'SubBag',
    'BagOfAll' : 'BagOfAll',
    'BagCardinality' : 'BagCardinality',
    'CopiesIn' : 'CopiesIn',
}

# Strip module (bang) prefix
def get_local_name(name):
    ix = name.rfind('!')
    return name[ix + 1:] if ix != -1 else name

def builtin_remap(name):
    local_name = get_local_name(name)
    logging.debug(f'IR builtin_remap: {name} -> {local_name}')
    return builtin_table.get(local_name, None)

def standard_remap(name):
    local_name = get_local_name(name)
    logging.debug(f'IR standard_remap: {name} -> {local_name}')
    return standard_table.get(local_name, None)

class DefRef:
    pass

class Def0Ref(DefRef):
    def __init__(self, id):
        self.id = id

    def pretty(self):
        return self.id

    def ir(self):
        builtin = builtin_remap(self.id)
        if builtin:
            return {
                "type": "Untyped",
                "kind": "OperEx",
                "oper": builtin,
                "args": []
            }
        replacement = ir_context_replace(self.id)
        standard = standard_remap(self.id)
        return replacement if replacement else {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "OPER_APP",
            "args": [{
                "type": "Untyped",
                "kind": "NameEx",
                "name": standard if standard else self.id
            }]
        }

class Def1Ref(DefRef):
    def __init__(self, id):
        self.id = id

    def pretty(self):
        return self.id

    def ir_ref(self):
        expr = ir_context_replace(self.id)
        standard = standard_remap(self.id)
        return expr if expr else {
            "type": "Untyped",
            "kind": "NameEx",
            "name": standard if standard else self.id
        }

    def ir(self):
        assert not builtin_remap(self.id)
        return self.ir_ref()

class Str:
    def __init__(self, s):
        self.s = s

    def pretty(self):
        return f'"{self.s}"'

    def ir(self):
        return {
            "type": "Str",
            "kind": "ValEx",
            "value": {
                "kind": "TlaStr",
                "value": self.s
            }
        }

class StrSet:
    def pretty(self):
        return f'STRING'

    def ir(self):
        return {
            "type": "Str",
            "kind": "ValEx",
            "value": {
              "kind": "TlaStrSet"
            }
        }

class Num:
    def __init__(self, num):
        self.num = num

    def pretty(self):
        return str(self.num)

    def ir(self):
        return {
            "type": "Int",
            "kind": "ValEx",
            "value": {
                "kind": "TlaInt",
                "value": self.num
            }
        }

class Range:
    def __init__(self, n, m):
        self.n = n
        self.m = m

    def pretty(self):
        return f'{within_parens(self.n)}..{within_parens(self.m)}'

    def ir(self):
        return {
            "type": "Set(Int)",
            "kind": "OperEx",
            "oper": "INT_RANGE",
            "args": [self.n.ir(), self.m.ir()]
        }

class NumSet:
    def __init__(self, is_nat):
        self.is_nat = is_nat

    def pretty(self):
        return 'Nat' if self.is_nat else 'Int'

    def ir(self):
        return {
            "type": "Set(Int)",
            "kind": "ValEx",
            "value": {
                "kind": "TlaNatSet" if self.is_nat else "TlaIntSet"
            }
        }

class Bool:
    def __init__(self, value):
        self.value = value

    def pretty(self):
        return 'TRUE' if self.value else 'FALSE'

    def ir(self):
        return {
            "type": "Bool",
            "kind": "ValEx",
            "value": {
                "kind": "TlaBool",
                "value": self.value
            }
        }

class BoolSet:
    def pretty(self):
        return 'BOOLEAN'

    def ir(self):
        return {
            "type": "Set(Bool)",
            "kind": "ValEx",
            "value": {
              "kind": "TlaBoolSet"
            }
        }

class InDef0:
    # InDef0 can be constructed by two ways:
    # - InDef0(['x', 'y'], Set(...))
    # - InDef0([(['x'], Set(...)), (['y', 'z'], Set(...))])
    #
    # The latter is more general form (and more verbose)
    def __init__(self, args, expr = None):
        if expr:
            # args is actually list of vars
            assert len(args) > 0
            self.args = [(args, expr)]
        else:
            assert len(args) > 0
            self.args = args

    def vars(self):
        r = []
        for names, _ in self.args:
            r.extend(names)
        return r

    def replace_expr(self, replacer):
        self.args = [(name, replacer(expr)) for name, expr in self.args]

    def is_single_var(self):
        return len(self.vars()) == 1

    def pretty(self):
        args = []
        for vars, expr in self.args:
            args.append(f'{commas(vars)} \in {expr.pretty()}')
        return commas(args)

    def ir(self):
        args = []
        for vars, expr in self.args:
            for var in vars:
                args.append({
                    "type": "Untyped",
                    "kind": "NameEx",
                    "name": var
                })
                args.append(expr.ir())
        return args

class InDef1:
    def __init__(self, vars, expr):
        self.vars_internal = vars
        self.expr = expr

    def is_single_var(self):
        return len(self.vars_internal) == 1

    def vars(self):
        return self.vars_internal

    def pretty(self):
        return f'<<{commas(self.vars_internal)}>> \in {self.expr.pretty()}'

    def ir(self):
        return [Tuple(*(LocalRef(v) for v in self.vars_internal)).ir(), self.expr.ir()]

class Fun:
    def __init__(self, indef, expr):
        self.indef = indef
        self.expr = expr

    def pretty(self):
        return f'[{self.indef.pretty()} |-> {self.expr.pretty()}]'

    def ir(self):
        fun = {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "FUN_CTOR",
            "args" : [self.expr.ir()]
        }

        fun['args'].extend(self.indef.ir())
        return fun

class DefFun:
    def __init__(self, name, indef, expr, ann):
        self.name = name
        self.ann = ann
        self.indef = indef
        self.expr = expr

    def pretty(self):
        df = f'{self.name}[{self.indef.pretty()}] == {self.expr.pretty()}'
        return with_ann(df, self.ann)

    def ir(self):
        return Def0(self.name, Fun(self.indef, self.expr), self.ann).ir()

class ExceptArgLhsFun:
    def __init__(self, arg):
        self.arg = arg

    def pretty(self):
        return f'[{self.arg.pretty()}]'

    def ir(self):
        return self.arg.ir()

class ExceptArgLhsTupleFun:
    def __init__(self, *args):
        self.args = args

    def pretty(self):
        args = commas(arg.pretty() for arg in self.args)
        return f'[{args}]'

    def ir(self):
        return Tuple(*self.args).ir()

class ExceptArgLhsRec:
    def __init__(self, arg):
        assert isinstance(arg, str)
        self.arg = arg

    def pretty(self):
        return f'.{self.arg}'

    def ir(self):
        return Str(self.arg).ir()

class ExceptArgLhs:
    def __init__(self, *args):
        assert all(isinstance(arg, ExceptArgLhsFun) or
                   isinstance(arg, ExceptArgLhsTupleFun) or
                   isinstance(arg, ExceptArgLhsRec)
            for arg in args)
        self.args = args

    def pretty(self):
        return ''.join(arg.pretty() for arg in self.args)

    def ir(self):
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "TUPLE",
            "args": [arg.ir() for arg in self.args]
        }

class ExceptArg:
    def __init__(self, arg, value):
        assert isinstance(arg, ExceptArgLhs)
        self.arg = arg
        self.value = value

    def pretty(self):
        return f'!{self.arg.pretty()} = {self.value.pretty()}'

    def ir(self):
        return [self.arg.ir(), self.value.ir()]

class Except:
    def __init__(self, fexpr, *args):
        self.fexpr = fexpr
        assert len(args) != 0
        assert all(isinstance(arg, ExceptArg) for arg in args)
        self.args = args

    def pretty(self):
        return f'[{self.fexpr.pretty()} EXCEPT {commas(arg.pretty() for arg in self.args)}]'

    def ir(self):
        ex = {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "EXCEPT",
            "args": []
        }

        args = [self.fexpr.ir()]

        for arg in self.args:
            assert isinstance(arg, ExceptArg)
            args.extend(arg.ir())

        ex['args'] = args
        return ex

class FunSet:
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

    def pretty(self):
        return f'[{self.lhs.pretty()} -> {self.rhs.pretty()}]'

    def ir(self):
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "FUN_SET",
            "args": [self.lhs.ir(), self.rhs.ir()]
        }

class RecordSet:
    def __init__(self, fields):
        assert isinstance(fields, dict)
        self.fields = fields

    def pretty(self):
        fields = [f'{name} : {value.pretty()}' for name, value in self.fields.items()]
        return f'[{commas(fields)}]'

    def ir(self):
        args = []
        for name, value in self.fields.items():
            args.extend([Str(name).ir(), value.ir()])

        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "RECORD_SET",
            "args": args
        }

class Record:
    def __init__(self, fields):
        self.fields = fields
        assert len(self.fields) > 0

    def pretty(self):
        r = []
        for field, expr in self.fields.items():
            r.append(f'{field} |-> {expr.pretty()}')
        return f'[{commas(r)}]'

    def ir(self):
        args = []
        for name, value in self.fields.items():
            args.extend([Str(name).ir(), value.ir()])

        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "RECORD",
            "args": args
        }

class Tuple:
    def __init__(self, *args):
        self.args = args

    def pretty(self):
        return f'<<{commas([i.pretty() for i in self.args])}>>'

    def ir(self):
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "TUPLE",
            "args": [i.ir() for i in self.args]
        }

class Set0:
    def __init__(self, *args):
        self.args = args

    def pretty(self):
        return f'{{{commas([i.pretty() for i in self.args])}}}'

    def ir(self):
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "SET_ENUM",
            "args": [i.ir() for i in self.args]
        }

class Choose:
    def __init__(self, indef, cond):
        self.indef = indef
        self.cond = cond

    def pretty(self):
        return indent_but_first('', f'CHOOSE {self.indef.pretty()} : {self.cond.pretty()}')

    def ir(self):
        args = self.indef.ir()
        args.append(self.cond.ir())
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "CHOOSE3",
            "args": args
        }

class Set1:
    def __init__(self, indef, cond):
        self.indef = indef
        self.cond = cond

    def pretty(self):
        return f'{{{self.indef.pretty()} : {self.cond.pretty()}}}'

    def ir(self):
        args = self.indef.ir()
        args.append(self.cond.ir())
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "SET_FILTER",
            "args": args
        }

class Set2:
    def __init__(self, indef, map):
        self.indef = indef
        self.map = map

    def is_in_op(self):
        if not isinstance(self.map, BinOp):
            return False
        if self.map.op not in [BinOpId.In, BinOpId.NotIn]:
            return False
        return True

    def pretty(self):
        m = self.map.pretty()
        # Take care of pathological TLA+ grammar case
        if self.is_in_op():
            m = f'({m})'
        return f'{{{m} : {self.indef.pretty()}}}'

    def ir(self):
        args = [self.map.ir()]
        args.extend(self.indef.ir())
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "SET_MAP",
            "args": args
        }

class Quantor:
    def __init__(self, indef, cond):
        self.indef = indef
        self.cond = cond

    def pretty_quantor(self):
        assert False, "Abstract class"

    def pretty(self):
        return indent_but_first('', f'{self.pretty_quantor()} {self.indef.pretty()} : {self.cond.pretty()}')

    def ir_quantor(self):
        assert False, "Abstract class"

    def ir_one(self, args):
        count = len(args)
        assert count % 2 == 0

        if count == 0:
            return self.cond.ir()

        var = args[0]
        set = args[1]
        expr = self.ir_one(args[2:])

        return {
            "type": "Bool",
            "kind": "OperEx",
            "oper": self.ir_quantor(),
            "args": [var, set, expr]
        }

    def ir(self):
        args = self.indef.ir()
        return self.ir_one(args)

class Exists(Quantor):
    def __init__(self, indef, cond):
        super().__init__(indef, cond)

    def pretty_quantor(self):
        return r'\E'

    def ir_quantor(self):
        return r'EXISTS3'

class ForAll(Quantor):
    def __init__(self, indef, cond):
        super().__init__(indef, cond)

    def pretty_quantor(self):
        return r'\A'

    def ir_quantor(self):
        return r'FORALL3'

class Def1App:
    def __init__(self, fexpr, *args):
        self.fexpr = fexpr
        self.args = args

    def pretty(self):
        args = f'({commas([i.pretty() for i in self.args])})' if self.args else ''
        return f'{self.fexpr.pretty()}{args}'

    def ir(self):
        # LHS can be LocalRef if it is used in rank-2 operators as parameter
        assert isinstance(self.fexpr, Def1Ref) or isinstance(self.fexpr, LocalRef)
        args = [arg.ir() for arg in self.args]
        builtin = builtin_remap(self.fexpr.id)
        if builtin:
            return {
                "type": "Untyped",
                "kind": "OperEx",
                "oper": builtin,
                "args": args
            }

        lhs = self.fexpr.ir_ref() if isinstance(self.fexpr, Def1Ref) else self.fexpr.ir()

        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "OPER_APP",
            "args": [lhs] + args
        }

class FunApp:
    def __init__(self, fexpr, *args):
        self.fexpr = fexpr
        self.args = args

    def pretty(self):
        if len(self.args) == 1 and isinstance(self.args[0], BinOp) and self.args[0].op == BinOpId.In:
            args = f'({self.args[0].pretty()})'
        else:
            args = commas([i.pretty() for i in self.args])
        return f'{within_parens(self.fexpr)}[{args}]'

    def ir(self):
        args = self.args[0] if len(self.args) == 1 else Tuple(self.args)
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "FUN_APP",
            "args": [self.fexpr.ir(), args.ir()]
        }

class RecField:
    def __init__(self, fexpr, field):
        self.fexpr = fexpr
        self.field = field

    def pretty(self):
        return f'{within_parens(self.fexpr)}.{self.field}'

    def ir(self):
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "FUN_APP",
            "args": [self.fexpr.ir(), Str(self.field).ir()]
        }

@unique
class BinOpId(Enum):
    And = auto()
    AndMultiLine = auto()
    Or = auto()
    OrMultiLine = auto()
    Eq = auto()
    Ne = auto()
    Gt = auto()
    Ge = auto()
    Lt = auto()
    Le = auto()
    Plus = auto()
    Minus = auto()
    Mul = auto()
    Div = auto()
    Mod = auto()
    Pow = auto()
    Imply = auto()
    Equiv = auto()
    In = auto()
    NotIn = auto()
    SubsetEq = auto()
    SetDiff = auto()
    Union = auto()
    Intersect = auto()
    Concat = auto()
    TlcSingletonFun = auto()
    TlcExtendFun = auto()
    BagAdd = auto()
    BagSub = auto()
    BagSubsetEq = auto()

class BinOp:
    def __init__(self, op : BinOpId, lhs, rhs):
        self.op = op
        self.lhs = lhs
        self.rhs = rhs

    def pretty(self):
        lhs = within_parens(self.lhs)
        rhs = within_parens(self.rhs)

        if self.op == BinOpId.AndMultiLine:
            clhs = indent_but_first(f'/\\ {lhs}')
            crhs = indent_but_first(f'/\\ {rhs}')
            return indent_but_first('(', clhs, crhs,')')

        if self.op == BinOpId.OrMultiLine:
            clhs = indent_but_first(f'\\/ {lhs}')
            crhs = indent_but_first(f'\\/ {rhs}')
            return indent_but_first('(', clhs, crhs,')')

        if self.op == BinOpId.And:
            op = '/\\'
        elif self.op == BinOpId.Or:
            op = '\\/'
        elif self.op == BinOpId.Eq:
            op = '='
        elif self.op == BinOpId.Ne:
            op = '/='
        elif self.op == BinOpId.Gt:
            op = '>'
        elif self.op == BinOpId.Ge:
            op = '>='
        elif self.op == BinOpId.Lt:
            op = '<'
        elif self.op == BinOpId.Le:
            op = '<='
        elif self.op == BinOpId.Plus:
            op = '+'
        elif self.op == BinOpId.Minus:
            op = '-'
        elif self.op == BinOpId.Mul:
            op = '*'
        elif self.op == BinOpId.Div:
            op = '\\div'
        elif self.op == BinOpId.Mod:
            op = '%'
        elif self.op == BinOpId.Pow:
            op = '^'
        elif self.op == BinOpId.Imply:
            op = '=>'
        elif self.op == BinOpId.Equiv:
            op = '<=>'
        elif self.op == BinOpId.In:
            op = '\\in'
        elif self.op == BinOpId.NotIn:
            op = '\\notin'
        elif self.op == BinOpId.SubsetEq:
            op = '\\subseteq'
        elif self.op == BinOpId.SetDiff:
            op = '\\'
        elif self.op == BinOpId.Union:
            op = '\\union'
        elif self.op == BinOpId.Intersect:
            op = '\\intersect'
        elif self.op == BinOpId.Concat:
            op = '\o'
        elif self.op == BinOpId.TlcSingletonFun:
            op = ':>'
        elif self.op == BinOpId.TlcExtendFun:
            op = '@@'
        elif self.op == BinOpId.BagAdd:
            op = '(+)'
        elif self.op == BinOpId.BagSub:
            op = '(-)'
        elif self.op == BinOpId.BagSubsetEq:
            op = r'\sqsubseteq'
        else:
            assert False, f"Unknown operation `{self.op}'"

        return f'{lhs} {op} {rhs}'

    def ir(self):
        sub_op = None

        if self.op == BinOpId.AndMultiLine:
            op = 'AND'
        elif self.op == BinOpId.OrMultiLine:
            op = 'OR'
        elif self.op == BinOpId.And:
            op = 'AND'
        elif self.op == BinOpId.Or:
            op = 'OR'
        elif self.op == BinOpId.Eq:
            op = 'EQ'
        elif self.op == BinOpId.Ne:
            op = 'NE'
        elif self.op == BinOpId.Gt:
            op = 'GT'
        elif self.op == BinOpId.Ge:
            op = 'GE'
        elif self.op == BinOpId.Lt:
            op = 'LT'
        elif self.op == BinOpId.Le:
            op = 'LE'
        elif self.op == BinOpId.Plus:
            op = 'PLUS'
        elif self.op == BinOpId.Minus:
            op = 'MINUS'
        elif self.op == BinOpId.Mul:
            op = 'MULT'
        elif self.op == BinOpId.Div:
            op = 'DIV'
        elif self.op == BinOpId.Mod:
            op = 'MOD'
        elif self.op == BinOpId.Pow:
            op = 'POW'
        elif self.op == BinOpId.Imply:
            op = 'IMPLIES'
        elif self.op == BinOpId.Equiv:
            op = 'EQUIV'
        elif self.op == BinOpId.In:
            op = 'SET_IN'
        elif self.op == BinOpId.NotIn:
            op = 'SET_NOT_IN'
        elif self.op == BinOpId.SubsetEq:
            op = 'SET_SUBSET_EQ'
        elif self.op == BinOpId.SetDiff:
            op = 'SET_MINUS'
        elif self.op == BinOpId.Union:
            op = 'SET_UNION2'
        elif self.op == BinOpId.Intersect:
            op = 'SET_INTERSECT'
        elif self.op == BinOpId.Concat:
            op = 'Sequences!Concat'
        elif self.op == BinOpId.TlcSingletonFun:
            op = 'OPER_APP'
            sub_op = ':>'
        elif self.op == BinOpId.TlcExtendFun:
            op = 'OPER_APP'
            sub_op = '@@'
        elif self.op == BinOpId.BagAdd:
            op = 'OPER_APP'
            sub_op = '\\oplus'
        elif self.op == BinOpId.BagSub:
            op = 'OPER_APP'
            sub_op = '\\ominus'
        elif self.op == BinOpId.BagSubsetEq:
            op = 'OPER_APP'
            sub_op = '\\sqsubseteq'
        else:
            assert False, f"Unknown operation `{self.op}'"

        if sub_op == None:
            return {
                "type": "Untyped",
                "kind": "OperEx",
                "oper": op,
                "args": [self.lhs.ir(), self.rhs.ir()]
            }

        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": op,
            "args": [
                {
                    "type": "Untyped",
                    "kind": "NameEx",
                    "name": sub_op
                },
                self.lhs.ir(),
                self.rhs.ir()
            ]
        }

class Not:
    def __init__(self, arg):
        self.arg = arg

    def pretty(self):
        r = f'~{within_parens(self.arg)}'
        return r

    def ir(self):
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "NOT",
            "args": [self.arg.ir()]
        }

class UnaryMinus:
    def __init__(self, arg):
        self.arg = arg

    def pretty(self):
        # Special case for -- x
        if isinstance(self.arg, UnaryMinus):
            r = f'-({self.arg.pretty()})'
        else:
            r = f'-{within_parens(self.arg)}'
        return r

    def ir(self):
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "UNARY_MINUS",
            "args": [self.arg.ir()]
        }

class Cross:
    def __init__(self, *args):
        assert len(args) > 0
        self.args = args

    def pretty(self):
        args = [within_parens(arg) for arg in self.args]
        return ' \\X '.join(args)
        return r

    def ir(self):
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "SET_TIMES",
            "args": [arg.ir() for arg in self.args]
        }

class Prime:
    def __init__(self, arg):
        self.arg = arg

    def pretty(self):
        r = f'{within_parens(self.arg)}\''
        return r

    def ir(self):
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "PRIME",
            "args": [self.arg.ir()]
        }

class Boxed:
    def __init__(self, expr, vars):
        self.expr = expr
        self.vars = vars

    def pretty(self):
        expr = self.expr.pretty()
        # Rule out pathological case ([x \in S]_u vs [x \in S |-> u])
        if isinstance(self.expr, BinOp) and self.expr.op == BinOpId.In:
            expr = f'({expr})'
        return f'[][{expr}]_{within_parens(self.vars)}'

    def ir(self):
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "GLOBALLY",
            "args": [
                {
                    "type": "Untyped",
                    "kind": "OperEx",
                    "oper": "STUTTER",
                    "args": [
                        self.expr.ir(),
                        self.vars.ir()
                    ]
                }
            ]
        }

class Always:
    def __init__(self, arg):
        self.arg = arg

    def pretty(self):
        r = f'[]{within_parens(self.arg)}'
        return r

    def ir(self):
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "GLOBALLY",
            "args": [self.arg.ir()]
        }

class Enabled:
    def __init__(self, arg):
        self.arg = arg

    def pretty(self):
        r = f'ENABLED({self.arg.pretty()})'
        return r

    def ir(self):
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "ENABLED",
            "args": [self.arg.ir()]
        }

class Domain:
    def __init__(self, fun):
        self.fun = fun

    def pretty(self):
        return f'DOMAIN {within_parens(self.fun)}'

    def ir(self):
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "DOMAIN",
            "args": [self.fun.ir()]
        }

class Union:
    def __init__(self, sets):
        self.sets = sets

    def pretty(self):
        return f'UNION {within_parens(self.sets)}'

    def ir(self):
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "SET_UNARY_UNION",
            "args": [self.sets.ir()]
        }

class Subset:
    def __init__(self, arg):
        self.arg = arg

    def pretty(self):
        r = f'SUBSET {within_parens(self.arg)}'
        return r

    def ir(self):
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "SET_POWERSET",
            "args": [self.sets.ir()]
        }

class Unchanged:
    def __init__(self, arg):
        self.arg = arg

    def pretty(self):
        r = f'UNCHANGED {within_parens(self.arg)}'
        return r

    def ir(self):
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "UNCHANGED",
            "args": [self.arg.ir()]
        }

class IfThenElse:
    def __init__(self, cond, then_side, else_side):
        self.cond = cond
        self.then_side = then_side
        self.else_side = else_side

    def pretty(self):
        r = indent_but_first('', f'IF {within_parens(self.cond)}', f'THEN {within_parens(self.then_side)}', f'ELSE {within_parens(self.else_side)}')
        return r

    def ir(self):
        return {
            "type": "Untyped",
            "kind": "OperEx",
            "oper": "IF_THEN_ELSE",
            "args": [
                self.cond.ir(),
                self.then_side.ir(),
                self.else_side.ir()
            ]
        }

class Let:
    def __init__(self, defs, expr):
        self.defs = defs
        self.expr = expr

    def pretty(self):
        defs = [d.pretty() for d in self.defs]
        expr = self.expr.pretty()
        r = indent_but_first('', 'LET', indent(*defs), f'IN {expr}')
        return r

    def ir(self):
        ir_context_start_local_defs()
        defs = [df.ir() for df in self.defs]
        ir_context_end_local_defs()
        return {
            "type": "Untyped",
            "kind": "LetInEx",
            "body": self.expr.ir(),
            "decls": defs
        }

class Variables:
    def __init__(self, vars = []):
        self.vars = vars
        self.varsvar = Def0('vars', Tuple(*[VarRef(i) for i, _ in self.vars]))

    def pretty(self):
        r = []
        for v,desc in self.vars:
            r.append(with_ann(v, desc.type))

        r1 = ',\n'.join(r)

        if self.vars:
            r = unlines([
                f'VARIABLE',
                indent(r1)])
        return r

    def ir(self):
        # All constants must be replaced in INSTANCE
        if ir_context_in_instance():
            return []
        return [
            {
                "type": desc.type.apalache(),
                "kind": "TlaVarDecl",
                "name": name
            }
            for name, desc in self.vars
        ]

class BaseModule:
    # Folder name where to put the module file
    # It is None if the module is to be rendered in the same folder as the main module
    def folder(self):
        return None

# Apalache standard module in IR
class StandardModule(BaseModule):
    def __init__(self, name):
        self.name = name

    def ir(self):
        file_path = os.path.join(os.path.dirname(__file__), f'{self.name}.json')
        with open(file_path) as h:
            return json.load(h)

# TLA+ module taken from file
class PlainFileModule(BaseModule):
    def __init__(self, name):
        self.name = name

    def pretty(self):
        file_path = os.path.join(os.path.dirname(__file__), f'{self.name}.tla')
        with open(file_path) as h:
            content = h.read()

        return content

# TLA+ module represented as AST
class Module(BaseModule):
    def __init__(self, search_path, name, *entries):
        self.search_path = search_path
        self.name = name
        self.entries = entries
        self.extends = []
        self.variables = []
        self.constants = {}

        for e in entries:
            if isinstance(e, Variables):
                self.variables.extend(e.vars)
            elif isinstance(e, Constants):
                self.constants.update(e.consts)
            elif isinstance(e, Extends):
                self.extends.extend(e.modules)

    def folder(self):
        return self.search_path

    def pretty(self):
        r = [
            f'---- MODULE {self.name} ----',
            f'{unlines([i.pretty() for i in self.entries])}',
            f'===='
        ]
        return unlines(r)

    def ir(self):
        decls = []

        for decl in self.entries:
            ir = decl.ir()
            if isinstance(ir, list):
                decls.extend(ir)
            else:
                decls.append(ir)

        return decls

class Cfg:
    def __init__(
            self,
            name,
            constants = [],
            check_deadlock = True,
            specification = 'Spec',
            invariants = ['Inv'],
            properties = ['Prop'],
            symmetry = [],
            constraints = [],
            view = None,
            action_constraints = []):

        self.name = name
        self.model_values = [n for n,d in constants.items() if d.init == None]
        self.overrides = {n : d.init for n,d in constants.items() if d.init != None }
        self.specification = specification
        self.check_deadlock = check_deadlock
        self.invariants = invariants
        self.properties = properties
        self.view = view
        self.symmetry = symmetry
        self.constraints = constraints
        self.action_constraints = action_constraints

    def aligned(self, name, *values):
        if not values:
            return []
        return [name, indent(*values), '']

    def pretty(self):
        r = [f'\* CONFIG {self.name}', '']
        model_values = [f'{mv} = {mv}' for mv in self.model_values]
        overrides = [f'{n} <- {v.pretty()}' for n,v in self.overrides.items()]
        r += self.aligned('CONSTANT', *model_values, *overrides)
        r += self.aligned('SPECIFICATION', self.specification)
        r += self.aligned('CHECK_DEADLOCK', "TRUE" if self.check_deadlock else "FALSE")
        r += self.aligned('INVARIANT', *self.invariants)
        r += self.aligned('PROPERTY', *self.properties)
        if self.symmetry:
            r += self.aligned('SYMMETRY', self.symmetry)
        if self.view:
            r += self.aligned('VIEW', self.view)
        r += self.aligned('CONSTRAINT', *self.constraints)
        r += self.aligned('ACTION_CONSTRAINT', *self.action_constraints)
        return unlines(r)

# CFG file with uninterpreted content
class RawCfg:
    def __init__(self, name, content):
        self.name = name
        self.content = content

    def pretty(self):
        return self.content

StandardSpec = Def0('Spec',
    BinOp(
        BinOpId.And,
        Def0Ref('Init'),
        Boxed(Def0Ref('Next'), Def0Ref('vars'))))
