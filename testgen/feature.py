# SPDX-FileCopyrightText: Copyright (c) 2022 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import logging
from enum import Enum, unique, auto
from .ast import *
from .common import *
from .kind import Kind, most_generic
from .type import *
from .testcase import SkipReason, ConstDesc, TlcModel, ApalacheModel, SkipCase, RefTlcCase, RefApalacheCase, build_init, find_visible_constants, get_check_deadlock, init_name, init_ref, reset_name, set_check_deadlock, testmodel_template, mk_name, new_variable, find_visible_variables

def eq(u, v):
    r = BinOp(BinOpId.Eq, u, v)
    r.type = bool_t
    return r

def ne(u, v):
    r = BinOp(BinOpId.Ne, u, v)
    r.type = bool_t
    return r

simple_kinds = [Kind.Temporal, Kind.Action, Kind.State, Kind.Const]
state_kinds = [Kind.Temporal, Kind.Action, Kind.State]

# Special cases
and_kinds = [Kind.Nice, Kind.Boxed] + simple_kinds
not_kinds = [Kind.Action, Kind.State, Kind.Const]
set_kinds = [Kind.Action, Kind.State, Kind.Const]
boxed_kinds = [Kind.Action, Kind.State, Kind.Const]

boolean = BoolSet()
boolean.type = SetT(bool_t)
boolean.kind = Kind.Const

def indef_tuple(indef):
    if indef.is_single_var():
        u = LocalRef(indef.vars()[0])
    else:
        u = Tuple(*[LocalRef(v) for v in indef.vars()])

    if isinstance(indef, InDef0):
        if indef.is_single_var():
            u.type = indef.type.type
        else:
            u.type = TupleT(*[indef.type.type for _ in indef.vars()])
    else:
        assert isinstance(indef, InDef1)
        u.type = indef.type.type
    u.kind = Kind.Const
    return u

def is_model_value(feature):
    return isinstance(feature, Constant0F) and feature.modelvalue

class Feature:
    def __init__(self):
        self.extends = []
        self.constants = {}
        self.variables = []
        self.globals = []
        self.modules = []

    # Can feature be reduced to other feature?
    # If the feature can be reduced, we do need to instantiate
    # apalache model. Instead, we can generate equivalent TLC model
    def can_be_reduced(self):
        return False
    def reduction_strategy(self):
        assert False, "No reduction strategy provided"
    def feature_name(self):
        return self.__class__.__name__
    def case(self, hole):
        raise "Not implemented"
    def plug(self, type):
        raise "Not implemented"
    def case_tlc(self, hole):
        r = self.case(hole)
        if isinstance(r, SkipReason):
            return r
        args, kw = r
        return TlcModel(*args, **kw)
    def plug_tlc(self, type):
        return self.plug(type)
    def case_tlc_reduced(self, hole):
        return self.case_tlc(hole)
    def plug_tlc_reduced(self, type):
        return self.plug_tlc(type)
    def case_apalache(self, hole):
        assert not self.can_be_reduced()
        r = self.case(hole)
        if isinstance(r, SkipReason):
            return r
        args, kw = r
        return ApalacheModel(*args, **kw)
    def plug_apalache(self, type):
        return self.plug(type)

    def model_value_allowed(self):
        return False

    def add_extends_standard(self, *module_names):
        for module_name in module_names:
            found = False
            for m in self.extends:
                if m.name == module_name:
                    found = True
                    break
            if not found:
                self.extends.append(StandardModule(module_name))

    def add_extends(self, module):
        for m in self.extends:
            if m.name == module.name:
                return
        self.extends.append(module)

    def new_const(self, type, init, name = None):
        name = name if name else mk_name()
        if isinstance(type, Def1T):
            arity = len(type.args)
        else:
            arity = 0
        self.constants[name] = ConstDesc(type, arity = arity, init = init)
        ref = ConstRef(name)
        ref.type = type
        ref.kind = Kind.Const
        return ref

    def is_const_a_model_value(self, ref):
        if not isinstance(ref, ConstRef):
            return False

        if ref.id not in self.constants:
            return False

        return self.constants[ref.id].init == None

    def new_var(self, type, name = None, init = None, unchanged = False):
        visible = find_visible_variables(self.extends, self.modules)
        return new_variable(self.variables, visible, type, name = name, init = init, unchanged = unchanged)

    def x(self):
        return self.new_var(bool_t, name = 'x')

    def y(self):
        return self.new_var(bool_t, name = 'y')

    def next_y(self, expr):
        x = self.x()
        y = self.y()
        next = BinOp(BinOpId.And,
            eq(Prime(x), Not(x)),
            eq(Prime(y), expr))
        return next

    def next_and(self, expr):
        assert expr.type == bool_t
        x = self.x()
        y = self.y()
        next = BinOp(BinOpId.And,
            BinOp(BinOpId.And,
                eq(Prime(x), Not(x)),
                eq(Prime(y), x)),
            expr)
        return next

    def add_module(self, module):
        self.modules.append(module)

    # Define a new model based on the feature state
    def def_module(self, init = None, search_path = False):
        prefix = 'TLC' if self.is_tlc else 'Apalache'
        suffix = mk_name()
        name = f'{prefix}_{suffix}'

        if init:
            self.def_expr(init, name = init_name(name))

        fs = []
        if self.extends:
            fs.append(Extends(*self.extends))
        if self.constants:
            fs.append(Constants(self.constants))
        if self.variables:
            fs.append(Variables(self.variables))
        fs.extend(self.globals)

        # Create a folder name to put the module in
        folder_name = mk_name() if self.is_tlc and search_path else None
        module = Module(folder_name, name, *fs)

        self.extends = []
        self.constants = {}
        self.variables = []
        self.globals = []
        self.modules.append(module)

        return module

    # Define toplevel expression
    def def_expr(self, e, name = None):
        n = name if name else mk_name()

        ref = Def0Ref(n)
        ref.type = e.type
        ref.kind = e.kind

        self.globals.append(Def0(n, e, e.type))
        return ref

    # Define expression indirectly via operator to please Apalache
    def def_apalache(self, e, toplevel = False):
        if self.is_tlc:
            return e

        n = mk_name()

        ref = Def0Ref(n)
        ref.type = e.type
        ref.kind = e.kind

        if toplevel:
            self.globals.append(Def0(n, e, e.type))
            return ref

        e1 = Let([Def0(n, e, e.type)], ref)
        e1.type = ref.type
        e1.kind = e.kind
        return e1

    def plug_tlc_ext(self, kinds, type):
        self.is_tlc = True
        self.is_ref = False
        self.extends = []
        self.constants = {}
        self.variables = []
        self.globals = []
        self.modules = []
        self.kinds = kinds
        return self.plug_tlc(type)

    def plug_tlc_reduced_ext(self, kinds, type):
        self.is_tlc = True
        self.is_ref = True
        self.extends = []
        self.constants = {}
        self.variables = []
        self.globals = []
        self.modules = []
        self.kinds = kinds
        return self.plug_tlc_reduced(type)

    def plug_apalache_ext(self, kinds, type):
        assert not self.can_be_reduced()
        self.is_tlc = False
        self.is_ref = True
        self.extends = []
        self.constants = {}
        self.variables = []
        self.globals = []
        self.modules = []
        self.kinds = kinds
        return self.plug_apalache(type)

    def case_tlc_ext(self, hole, extends = [], constants = {}, variables = [], globals = [], modules = []):
        self.is_tlc = True
        self.is_ref = False
        self.extends = extends
        self.constants = constants
        self.variables = variables
        self.globals = globals
        self.modules = modules

        return self.case_tlc(hole)

    def case_tlc_reduced_ext(self, hole, extends = [], constants = {}, variables = [], globals = [], modules = []):
        self.is_tlc = True
        self.is_ref = True
        self.extends = extends
        self.constants = constants
        self.variables = variables
        self.globals = globals
        self.modules = modules

        return self.case_tlc_reduced(hole)

    def case_apalache_ext(self, hole, extends = [], constants = {}, variables = [], globals = [], modules = []):
        assert not self.can_be_reduced()
        self.is_tlc = False
        self.is_ref = True
        self.extends = extends
        self.constants = constants
        self.variables = variables
        self.globals = globals
        self.modules = modules

        return self.case_apalache(hole)

    def indef0(self, type, *locals, toplevel = False):
        sample = SetT(type).sample()
        indef = InDef0(locals, self.def_apalache(sample, toplevel = toplevel))
        indef.kind = sample.kind
        return indef

    def indef1(self, type, *locals, toplevel = False):
        sample = SetT(type).sample()
        indef = InDef1(locals, self.def_apalache(sample, toplevel = toplevel))
        indef.kind = sample.kind
        return indef

    def testmodel_template(self, **kw):
        return testmodel_template(
            extends = self.extends,
            constants = self.constants,
            variables = self.variables,
            globals = self.globals,
            modules = self.modules, **kw)

class AndF(Feature):
    # What kind is expected to plug
    def kind(self):
        # AND is the only one which allows Nice kind
        return simple_kinds

    # What type is expected to be plugged in
    def type(self):
        return bool_t

    def case(self, hole):
        expr = BinOp(BinOpId.And, hole, self.x())
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        if not type.match(bool_t):
            return SkipReason.TypeMismatch

        if self.kinds == [Kind.Const]:
            lhs = Bool(True)
            rhs = Bool(False)
            kind = Kind.Const
        else:
            lhs = eq(self.x(), Bool(True))
            rhs = eq(self.x(), Bool(True))
            kind = Kind.State

        r = BinOp(BinOpId.And, lhs, rhs)
        r.type = bool_t
        r.kind = kind
        return r

class AndMultiLineF(Feature):
    def can_be_reduced(self):
        return True

    def reduction_strategy(self):
        return "\n  /\\ A\n  /\\ B\n== (A /\ B)"

    # What kind is expected to plug
    def kind(self):
        return simple_kinds

    # What type is expected to be plugged in
    def type(self):
        return bool_t

    def case_tlc(self, hole):
        expr = BinOp(BinOpId.AndMultiLine, hole, self.x())
        args, kw = self.testmodel_template(next = self.next_y(expr))
        return TlcModel(*args, **kw)

    def case_tlc_reduced(self, hole):
        expr = BinOp(BinOpId.And, hole, self.x())
        args, kw = self.testmodel_template(next = self.next_y(expr))
        return TlcModel(*args, **kw)

    def plug_tlc(self, type):
        if not type.match(bool_t):
            return SkipReason.TypeMismatch

        lhs = Bool(True)
        rhs = Bool(False)
        r = BinOp(BinOpId.AndMultiLine, lhs, rhs)
        r.type = bool_t
        r.kind = Kind.Const
        return r

    def plug_tlc_reduced(self, type):
        if not type.match(bool_t):
            return SkipReason.TypeMismatch

        lhs = Bool(True)
        rhs = Bool(False)
        r = BinOp(BinOpId.And, lhs, rhs)
        r.type = bool_t
        r.kind = Kind.Const
        return r

class AndPropF(Feature):
    # What kind is expected to plug
    def kind(self):
        # AND is the only one which allows Nice kind
        return [Kind.Nice, Kind.Temporal, Kind.Boxed] # TODO: Kind.State

    # What type is expected to be plugged in
    def type(self):
        return bool_t

    def case(self, hole):
        rhs = eq(self.x(), Bool(True))
        if self.is_tlc:
            expr = BinOp(BinOpId.And, hole, Always(rhs))
        elif hole.kind in [Kind.Nice, Kind.Boxed]:
            expr = BinOp(BinOpId.And, hole, rhs)
        else:
            def0 = self.def_expr(hole)
            ref = self.new_var(bool_t, init = def0, unchanged = True)
            expr = BinOp(BinOpId.And, ref, rhs)
        return self.testmodel_template(prop = expr)

    def plug(self, type):
        if Kind.Nice not in self.kinds:
            return SkipReason.KindMismatch
        if not type.match(bool_t):
            return SkipReason.TypeMismatch

        lhs = eq(self.x(), Bool(True))
        rhs = eq(self.y(), Bool(True))

        expr = BinOp(BinOpId.And, lhs, rhs)
        expr.type = bool_t
        expr.kind = Kind.Nice
        if not self.is_tlc:
            ref = self.def_expr(expr)
            expr = self.new_var(bool_t, init = ref, unchanged=True)
            expr.kind = Kind.Nice
        return expr

class ImplyF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return bool_t

    def case(self, hole):
        expr = BinOp(BinOpId.Imply, hole, self.x())
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        if not type.match(bool_t):
            return SkipReason.TypeMismatch

        if self.kinds == [Kind.Const]:
            lhs = Bool(True)
            rhs = Bool(False)
            kind = Kind.Const
        else:
            lhs = self.x()
            rhs = self.x()
            kind = Kind.State

        r = BinOp(BinOpId.Imply, lhs, rhs)
        r.type = bool_t
        r.kind = kind
        return r

class NotF(Feature):
    def kind(self):
        return not_kinds

    def type(self):
        return bool_t

    def case(self, hole):
        expr = Not(hole)
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        if not type.match(bool_t):
            return SkipReason.TypeMismatch
        if self.kinds == [Kind.Const]:
            e = Bool(False)
            kind = Kind.Const
        else:
            e = self.x()
            kind = Kind.State

        r = Not(e)
        r.type = bool_t
        r.kind = kind
        return r

class OrF(Feature):
    def can_be_reduced(self):
        return True

    def reduction_strategy(self):
        return "A \/ B == ~(~A /\ ~B)"

    # What kind is expected to plug
    def kind(self):
        # AND is the only one which allows Nice kind
        return simple_kinds

    # What type is expected to be plugged in
    def type(self):
        return bool_t

    def case_tlc(self, hole):
        expr = BinOp(BinOpId.Or, hole, self.x())
        args, kw = self.testmodel_template(next = self.next_y(expr))
        return TlcModel(*args, **kw)

    def case_tlc_reduced(self, hole):
        expr = Not(BinOp(BinOpId.And, Not(hole), Not(self.x())))
        args, kw = self.testmodel_template(next = self.next_y(expr))
        return TlcModel(*args, **kw)

    def plug_tlc(self, type):
        if not type.match(bool_t):
            return SkipReason.TypeMismatch

        lhs = Bool(True)
        rhs = Bool(False)
        r = BinOp(BinOpId.Or, lhs, rhs)
        r.type = bool_t
        r.kind = Kind.Const
        return r

    def plug_tlc_reduced(self, type):
        if not type.match(bool_t):
            return SkipReason.TypeMismatch

        lhs = Bool(True)
        rhs = Bool(False)
        r = Not(BinOp(BinOpId.And, Not(lhs), Not(rhs)))
        r.type = bool_t
        r.kind = Kind.Const
        return r

class OrMultiLineF(Feature):
    def can_be_reduced(self):
        return True

    def reduction_strategy(self):
        return "\n  \\/ A\n  \\/ B\n== (A \/ B)"

    # What kind is expected to plug
    def kind(self):
        return simple_kinds

    # What type is expected to be plugged in
    def type(self):
        return bool_t

    def case_tlc(self, hole):
        expr = BinOp(BinOpId.OrMultiLine, hole, self.x())
        args, kw = self.testmodel_template(next = self.next_y(expr))
        return TlcModel(*args, **kw)

    def case_tlc_reduced(self, hole):
        expr = BinOp(BinOpId.Or, hole, self.x())
        args, kw = self.testmodel_template(next = self.next_y(expr))
        return TlcModel(*args, **kw)

    def plug_tlc(self, type):
        if not type.match(bool_t):
            return SkipReason.TypeMismatch

        lhs = Bool(True)
        rhs = Bool(False)
        r = BinOp(BinOpId.OrMultiLine, lhs, rhs)
        r.type = bool_t
        r.kind = Kind.Const
        return r

    def plug_tlc_reduced(self, type):
        if not type.match(bool_t):
            return SkipReason.TypeMismatch

        lhs = Bool(True)
        rhs = Bool(False)
        r = BinOp(BinOpId.Or, lhs, rhs)
        r.type = bool_t
        r.kind = Kind.Const
        return r

class EqNeF(Feature):
    def __init__(self, op):
        super().__init__()
        assert op in [BinOpId.Eq, BinOpId.Ne]
        self.op = op

    def model_value_allowed(self):
        return True

    def kind(self):
        return simple_kinds

    def type(self):
        return any_t

    def case(self, hole):
        expr = BinOp(self.op, hole, hole)
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        if not type.match(bool_t):
            return SkipReason.TypeMismatch
        if self.kinds == [Kind.Const]:
            lhs = Bool(True)
            rhs = Bool(False)
            kind = Kind.Const
        else:
            lhs = self.x()
            rhs = self.x()
            kind = Kind.State

        r = BinOp(self.op, lhs, rhs)
        r.type = bool_t
        r.kind = kind
        return r

class EquivF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return bool_t

    def case(self, hole):
        expr = BinOp(BinOpId.Equiv, hole, hole.type.sample())
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        if not type.match(bool_t):
            return SkipReason.TypeMismatch

        lhs = Bool(True)
        rhs = Bool(False)
        r = BinOp(BinOpId.Equiv, lhs, rhs)
        r.type = bool_t
        r.kind = Kind.Const
        return r

class LetF(Feature):
    def model_value_allowed(self):
        return True

    def kind(self):
        return simple_kinds

    def type(self):
        return any_t

    def case(self, hole):
        localDef = 'LocalD0'
        def0 = Def0(localDef, hole)
        expr = Let([def0], Def0Ref(localDef))
        expr.type = hole.type
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        if not type.match(any_t):
            return SkipReason.TypeMismatch
        localDef = 'LocalD1'
        sample = type.sample()
        def0 = Def0(localDef, sample, sample.type)
        r = Let([def0], Def0Ref(localDef))
        r.type = sample.type
        r.kind = sample.kind
        return r

def any_to_bool(expr):
    if expr.type == bool_t:
        return expr
    return ne(expr, expr.type.sample())

class Def0F(Feature):
    def __init__(self, inlet):
        super().__init__()
        self.inlet = inlet

    def can_be_reduced(self):
        return self.inlet

    def reduction_strategy(self):
        return "LET definitions are reduced to global definitions"

    def model_value_allowed(self):
        return True

    def kind(self):
        return [Kind.Nice, Kind.Boxed, Kind.Temporal, Kind.Action, Kind.State, Kind.Const]

    def type(self):
        return any_t

    def new_def(self, expr, inlet):
        name = mk_name()
        d = Def0(name, expr, expr.type)
        ref = Def0Ref(name)
        if inlet:
            r = Let([d], ref)
        else:
            r = ref
            self.globals.append(d)
        r.type = expr.type
        r.kind = expr.kind
        return r

    def case_tlc(self, hole):
        ref = self.new_def(hole, self.inlet)
        r = any_to_bool(ref)

        if hole.kind in [Kind.Action, Kind.State, Kind.Const]:
            args, kw = self.testmodel_template(next = self.next_y(r))
            return TlcModel(*args, **kw)

        assert hole.kind in [Kind.Nice, Kind.Temporal, Kind.Boxed]
        args, kw = self.testmodel_template(prop = r)
        return TlcModel(*args, **kw)

    def case_tlc_reduced(self, hole):
        ref = self.new_def(hole, False)
        r = any_to_bool(ref)

        if hole.kind in [Kind.Action, Kind.State, Kind.Const]:
            args, kw = self.testmodel_template(next = self.next_y(r))
            return TlcModel(*args, **kw)

        assert hole.kind in [Kind.Nice, Kind.Temporal, Kind.Boxed]
        args, kw = self.testmodel_template(prop = r)
        return TlcModel(*args, **kw)

    def case_apalache(self, hole):
        if hole.kind in [Kind.Action, Kind.State, Kind.Const]:
            r = any_to_bool(hole)
            args, kw = self.testmodel_template(next = self.next_y(r))
            return ApalacheModel(*args, **kw)

        assert hole.kind in [Kind.Nice, Kind.Temporal, Kind.Boxed] and hole.type is bool_t
        args, kw = self.testmodel_template(prop = hole)
        return ApalacheModel(*args, **kw)

    def plug(self, type):
        if not type.match(any_t):
            return SkipReason.TypeMismatch

        return self.new_def(type.sample(), self.inlet)

    def plug_tlc_reduced(self, type):
        if not type.match(any_t):
            return SkipReason.TypeMismatch

        return self.new_def(type.sample(), False)

class Def1F(Feature):
    def __init__(self, inlet):
        super().__init__()
        self.inlet = inlet

    def can_be_reduced(self):
        return self.inlet

    def reduction_strategy(self):
        return "LET definitions are reduced to global definitions"

    def model_value_allowed(self):
        return True

    def kind(self):
        return [Kind.Nice, Kind.Boxed, Kind.Temporal, Kind.Action, Kind.State, Kind.Const]

    def type(self):
        return any_t

    def new_def(self, expr, inlet):
        name = mk_name()
        arg = 'def_arg' if not inlet else mk_name()
        arg_ref = LocalRef(arg)
        ty = Def1T(expr.type, expr.type)
        d = Def1(name, [arg], arg_ref, ty)
        ref = Def1Ref(name)
        ref.type = ty
        rval = Def1App(ref, expr)
        if inlet:
            r = Let([d], rval)
        else:
            r = rval
            self.globals.append(d)
        r.type = ty

        r.type = ty.rhs
        r.kind = expr.kind
        return r

    def case_tlc(self, hole):
        ref = self.new_def(hole, inlet = self.inlet)
        r = any_to_bool(ref)

        if hole.kind in [Kind.Action, Kind.State, Kind.Const]:
            args, kw = self.testmodel_template(next = self.next_y(r))
            return TlcModel(*args, **kw)

        assert hole.kind in [Kind.Nice, Kind.Temporal, Kind.Boxed]
        args, kw = self.testmodel_template(prop = r)
        return TlcModel(*args, **kw)

    def case_tlc_reduced(self, hole):
        ref = self.new_def(hole, inlet = False)
        r = any_to_bool(ref)

        if hole.kind in [Kind.Action, Kind.State, Kind.Const]:
            args, kw = self.testmodel_template(next = self.next_y(r))
            return TlcModel(*args, **kw)

        assert hole.kind in [Kind.Nice, Kind.Temporal, Kind.Boxed]
        args, kw = self.testmodel_template(prop = r)
        return TlcModel(*args, **kw)

    def case_apalache(self, hole):
        ref = self.new_def(hole, inlet = False)
        r = any_to_bool(ref)

        if hole.kind in [Kind.Action, Kind.State, Kind.Const]:
            r = any_to_bool(hole)
            args, kw = self.testmodel_template(next = self.next_y(r))
            return ApalacheModel(*args, **kw)

        assert hole.kind in [Kind.Nice, Kind.Temporal, Kind.Boxed] and hole.type is bool_t
        args, kw = self.testmodel_template(prop = hole)
        return ApalacheModel(*args, **kw)

    def plug(self, type):
        if not type.match(any_t):
            return SkipReason.TypeMismatch

        return self.new_def(type.sample(), inlet = self.inlet)

    def plug_tlc_reduced(self, type):
        if not type.match(any_t):
            return SkipReason.TypeMismatch

        return self.new_def(type.sample(), inlet = False)

class Def1RecursiveF(Feature):
    def __init__(self, inlet):
        super().__init__()
        self.inlet = inlet

    def can_be_reduced(self):
        return self.inlet

    def reduction_strategy(self):
        return "LET definitions are reduced to global definitions"

    def model_value_allowed(self):
        return True

    def kind(self):
        return [Kind.Nice, Kind.Boxed, Kind.Temporal, Kind.Action, Kind.State, Kind.Const]

    def type(self):
        return any_t

    def new_def(self, expr, is_tlc, inlet):
        name = mk_name()
        ty = Def1T(bool_t, expr.type)
        ref = Def1Ref(name)
        ref.type = ty
        arg = 'def_arg' if not inlet else mk_name()
        arg_ref = LocalRef(arg)
        if is_tlc:
            body = IfThenElse(arg_ref, expr, Def1App(ref, Not(arg_ref)))
        else:
            body = expr

        d = Def1(name, [arg], body, ty, recursive=is_tlc)
        rval = Def1App(ref, Bool(False))
        if inlet:
            r = Let([d], rval)
        else:
            r = rval
            self.globals.append(d)

        r.type = ty.rhs
        r.kind = expr.kind
        return r

    def case_tlc(self, hole):
        ref = self.new_def(hole, is_tlc=True, inlet = self.inlet)
        r = any_to_bool(ref)

        if hole.kind in [Kind.Action, Kind.State, Kind.Const]:
            args, kw = self.testmodel_template(next = self.next_y(r))
            return TlcModel(*args, **kw)

        assert hole.kind in [Kind.Nice, Kind.Temporal, Kind.Boxed]
        args, kw = self.testmodel_template(prop = r)
        return TlcModel(*args, **kw)

    def case_tlc_reduced(self, hole):
        ref = self.new_def(hole, is_tlc=True, inlet = False)
        r = any_to_bool(ref)

        if hole.kind in [Kind.Action, Kind.State, Kind.Const]:
            args, kw = self.testmodel_template(next = self.next_y(r))
            return TlcModel(*args, **kw)

        assert hole.kind in [Kind.Nice, Kind.Temporal, Kind.Boxed]
        args, kw = self.testmodel_template(prop = r)
        return TlcModel(*args, **kw)

    def case_apalache(self, hole):
        ref = self.new_def(hole, is_tlc=False, inlet = False)
        r = any_to_bool(ref)

        if hole.kind in [Kind.Action, Kind.State, Kind.Const]:
            r = any_to_bool(hole)
            args, kw = self.testmodel_template(next = self.next_y(r))
            return ApalacheModel(*args, **kw)

        assert hole.kind in [Kind.Nice, Kind.Temporal, Kind.Boxed] and hole.type is bool_t
        args, kw = self.testmodel_template(prop = hole)
        return ApalacheModel(*args, **kw)

    def plug_tlc(self, type):
        if not type.match(any_t):
            return SkipReason.TypeMismatch

        return self.new_def(type.sample(), is_tlc=True, inlet = self.inlet)

    def plug_tlc_reduced(self, type):
        if not type.match(any_t):
            return SkipReason.TypeMismatch

        return self.new_def(type.sample(), is_tlc=True, inlet = False)

    def plug_apalache(self, type):
        if not type.match(any_t):
            return SkipReason.TypeMismatch

        return self.new_def(type.sample(), is_tlc=False, inlet = False)

class Def2F(Feature):
    def __init__(self, inlet):
        super().__init__()
        self.inlet = inlet

    def can_be_reduced(self):
        return self.inlet

    def reduction_strategy(self):
        return "LET definitions are reduced to global definitions"

    def model_value_allowed(self):
        return True

    def kind(self):
        return [Kind.Nice, Kind.Boxed, Kind.Temporal, Kind.Action, Kind.State, Kind.Const]

    def type(self):
        return any_t

    def new_def1(self, expr):
        name = mk_name()
        arg = 'def_arg'
        arg_ref = LocalRef(arg)
        ty = Def1T(expr.type, expr.type)
        body = arg_ref
        self.globals.append(Def1(name, [arg], body, ty))
        ref = Def1Ref(name)
        ref.type = ty
        return ref

    def new_def(self, expr, inlet):
        name = mk_name()
        arg = 'def_arg' if not inlet else mk_name()
        arg_ref = LocalRef(arg)
        ty = Def1T(Def1T(expr.type, expr.type), expr.type)
        body = Def1App(arg_ref, expr)
        ref = Def1Ref(name)
        ref.type = ty

        d = Def2(name, [], [arg], body, ty)
        inner_ref = self.new_def1(expr)
        rval = Def1App(ref, inner_ref)

        if inlet:
            r = Let([d], rval)
        else:
            r = rval
            self.globals.append(d)

        r.type = ty.rhs
        r.kind = expr.kind
        return r

    def case_tlc(self, hole):
        ref = self.new_def(hole, inlet = self.inlet)
        r = any_to_bool(ref)

        if hole.kind in [Kind.Action, Kind.State, Kind.Const]:
            args, kw = self.testmodel_template(next = self.next_y(r))
            return TlcModel(*args, **kw)

        assert hole.kind in [Kind.Nice, Kind.Temporal, Kind.Boxed]
        args, kw = self.testmodel_template(prop = r)
        return TlcModel(*args, **kw)

    def case_tlc_reduced(self, hole):
        ref = self.new_def(hole, inlet = False)
        r = any_to_bool(ref)

        if hole.kind in [Kind.Action, Kind.State, Kind.Const]:
            args, kw = self.testmodel_template(next = self.next_y(r))
            return TlcModel(*args, **kw)

        assert hole.kind in [Kind.Nice, Kind.Temporal, Kind.Boxed]
        args, kw = self.testmodel_template(prop = r)
        return TlcModel(*args, **kw)

    def case_apalache(self, hole):
        ref = self.new_def(hole, inlet = False)
        r = any_to_bool(ref)

        if hole.kind in [Kind.Action, Kind.State, Kind.Const]:
            # r = any_to_bool(hole)
            args, kw = self.testmodel_template(next = self.next_y(r))
            return ApalacheModel(*args, **kw)

        assert hole.kind in [Kind.Nice, Kind.Temporal, Kind.Boxed] and hole.type is bool_t
        args, kw = self.testmodel_template(prop = hole)
        return ApalacheModel(*args, **kw)

    def plug(self, type):
        if not type.match(any_t):
            return SkipReason.TypeMismatch

        return self.new_def(type.sample(), inlet = self.inlet)

    def plug(self, type):
        if not type.match(any_t):
            return SkipReason.TypeMismatch

        return self.new_def(type.sample(), inlet = False)

class Set0F(Feature):
    def __init__(self, type = any_t):
        super().__init__()
        self.plug_type = SetT(type)

    def model_value_allowed(self):
        return True

    def kind(self):
        return set_kinds

    def type(self):
        return self.plug_type.type

    def case(self, hole):
        expr = BinOp(BinOpId.In, hole, Set0(hole))
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        new_type = type.refine(SetT(any_t))
        if not new_type:
            return SkipReason.TypeMismatch
        sample = new_type.type.sample()
        r = Set0(sample)
        r.type = SetT(sample.type)
        r.kind = sample.kind
        return r

class SetEmptyF(Feature):
    def kind(self):
        return set_kinds

    def type(self):
        return any_t

    def case(self, hole):
        return SkipReason.CanNotBeCase

    def plug(self, type):
        new_type = type.refine(SetT(any_t))
        if not new_type:
            return SkipReason.TypeMismatch
        r = Set0()
        r.type = new_type.sample().type
        r.kind = Kind.Const
        return self.def_apalache(r)

class Set1F(Feature):
    def model_value_allowed(self):
        return True

    def kind(self):
        return set_kinds

    def type(self):
        return any_t

    def case(self, hole):
        loc = mk_name()
        indef = self.indef0(hole.type, loc)
        ref = LocalRef(loc)
        expr = BinOp(BinOpId.In, hole, Set1(indef, eq(ref, hole)))
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        new_type = type.refine(SetT(any_t))
        if not new_type:
            return SkipReason.TypeMismatch
        sample = new_type.type.sample()
        loc = mk_name()
        indef = self.indef0(sample.type, loc)
        r = Set1(indef, Bool(True))
        r.type = SetT(sample.type)
        r.kind = sample.kind
        return r

class Set1InDefF(Feature):
    def kind(self):
        return set_kinds

    def type(self):
        return InDefT(any_t)

    def case(self, hole):
        # Set does not support variant: { x, y \in S : ... }
        if isinstance(hole, InDef0) and (len(hole.args) > 1 or len(hole.args[0][0]) > 1):
            return SkipReason.TypeMismatch
        indef = hole
        u = indef_tuple(indef)
        r = Set1(indef, any_to_bool(self.def_apalache(u)))
        r.type = SetT(u.type)
        expr = any_to_bool(r)
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        return SkipReason.AlreadyCombined

class Set2F(Feature):
    def __init__(self, type = any_t):
        super().__init__()
        self.plug_type = type

    def model_value_allowed(self):
        return True

    def kind(self):
        return set_kinds

    def type(self):
        return self.plug_type

    def case(self, hole):
        loc = mk_name()
        indef = self.indef0(hole.type, loc)
        expr = BinOp(BinOpId.In, hole, Set2(indef, hole))
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        new_type = type.refine(SetT(any_t))
        if not new_type:
            return SkipReason.TypeMismatch
        sample = new_type.type.sample()
        loc = mk_name()
        indef = self.indef0(sample.type, loc)
        r = Set2(indef, LocalRef(loc))
        r.type = SetT(sample.type)
        r.kind = sample.kind
        return r

class Set2InDefF(Feature):
    def kind(self):
        return set_kinds

    def type(self):
        return InDefT(any_t)

    def case(self, hole):
        indef = hole
        expr0 = indef_tuple(indef)
        r = Set2(indef, self.def_apalache(expr0))
        r.type = SetT(expr0.type)
        expr = any_to_bool(r)
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        return SkipReason.AlreadyCombined

class Except0F(Feature):
    def __init__(self, type = any_t):
        super().__init__()
        self.plug_type = type

    def kind(self):
        return set_kinds

    def type(self):
        return UnionT(
            FunT(self.plug_type, self.plug_type),
            SeqT(self.plug_type),
            RecordT({'field0' : self.plug_type}))

    def mk_arg(self, fexpr):
        return Choose(InDef0([mk_name()], Domain(fexpr)), Bool(True))

    def case_fun(self, fexpr):
        t = fexpr.type.refine(FunT(self.plug_type, self.plug_type))
        if not t:
            return None

        arg = self.mk_arg(fexpr)
        value = t.rhs.sample()
        ea = ExceptArg(ExceptArgLhs(ExceptArgLhsFun(arg)), value)
        r = Except(fexpr, ea)
        r.type = fexpr.type
        expr = eq(FunApp(r, arg), value)
        return expr

    def case_seq(self, fexpr):
        t = fexpr.type.refine(SeqT(self.plug_type))
        if not t:
            return None

        arg = self.mk_arg(fexpr)
        value = t.type.sample()
        ea = ExceptArg(ExceptArgLhs(ExceptArgLhsFun(arg)), value)
        r = Except(fexpr, ea)
        r.type = fexpr.type
        expr = eq(FunApp(r, arg), value)
        return expr

    def case_rec(self, fexpr):
        t = fexpr.type.refine(RecordT({'field0' : self.plug_type}))
        if not t:
            return None

        field, ty = list(t.fields.items())[0]
        value = ty.sample()
        ea = ExceptArg(ExceptArgLhs(ExceptArgLhsRec(field)), value)
        r = Except(fexpr, ea)
        r.type = fexpr.type
        expr = eq(RecField(r, field), value)
        return expr

    def case(self, hole):
        r = self.case_fun(hole)
        if not r:
            r = self.case_seq(hole)
        if not r:
            r = self.case_rec(hole)
        assert r

        return self.testmodel_template(next = self.next_y(r))

    def plug(self, type):
        return SkipReason.CanNotBePlug

class Except2FunF(Feature):
    def kind(self):
        return set_kinds

    def type(self):
        return any_t

    def case(self, hole):
        arg = hole
        indef = InDef0([mk_name()], Set0(arg))
        fexpr = Fun(indef, Bool(True))
        value = Bool(False)
        ea = ExceptArg(ExceptArgLhs(ExceptArgLhsFun(arg)), value)
        r = Except(fexpr, ea)
        r.type = FunT(arg.type, bool_t)

        expr = eq(FunApp(r, arg), value)
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        return SkipReason.CanNotBePlug

# Function with multiple arguments: [f EXCEPT ![x, y] = ...]
class Except2FunTupleF(Feature):
    def kind(self):
        return set_kinds

    def type(self):
        return TupleT(any_t, any_t)

    def arg_n(self, arg, n):
        assert len(arg.type.types) >= n
        applied = FunApp(arg, Num(n))
        applied.kind = arg.kind
        applied.type = arg.type.types[n - 1]
        return self.def_apalache(applied, toplevel = True)

    def case(self, hole):
        arg = self.def_apalache(hole)

        indef = InDef0([mk_name()], Set0(arg))
        fexpr = Fun(indef, Bool(True))
        value = Bool(False)

        arg1 = self.arg_n(arg, 1)
        arg2 = self.arg_n(arg, 2)
        ea = ExceptArg(ExceptArgLhs(ExceptArgLhsTupleFun(arg1, arg2)), value)
        r = Except(fexpr, ea)
        r.type = FunT(arg.type, bool_t)

        expr = eq(FunApp(r, arg), value)
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        return SkipReason.CanNotBePlug

class Except1FunF(Feature):
    def __init__(self, with_at, type = any_t):
        super().__init__()
        self.plug_type = type
        self.with_at = with_at

    def can_be_reduced(self):
        return self.with_at

    def reduction_strategy(self):
        return "@ is reduced to F[arg]"

    def kind(self):
        return set_kinds

    def type(self):
        return self.plug_type

    def mk_value(self, old, new, with_at):
        if self.with_at:
            if with_at:
                r = IfThenElse(eq(new, At()), At(), new)
            else:
                r = IfThenElse(eq(new, old), old, new)
        else:
            r = new
        r.type = new.type
        return r

    def case_template(self, hole, with_at):
        arg = Bool(True)
        old_value = hole.type.sample()
        indef = InDef0([mk_name()], Set0(arg))
        fexpr = Fun(indef, old_value)
        value = self.mk_value(old = FunApp(fexpr, arg), new = hole, with_at = with_at)
        ea = ExceptArg(ExceptArgLhs(ExceptArgLhsFun(arg)), value)
        r = Except(fexpr, ea)
        r.type = FunT(bool_t, value.type)

        expr = ne(FunApp(r, arg), hole)
        return self.testmodel_template(next = self.next_y(expr))

    def case(self, hole):
        return self.case_template(hole, with_at = self.with_at)

    def case_tlc_reduced(self, hole):
        args, kw = self.case_template(hole, with_at = False)
        return TlcModel(*args, **kw)

    def plug(self, type):
        return SkipReason.CanNotBePlug

class Except1RecF(Feature):
    def __init__(self, with_at, type = any_t):
        super().__init__()
        self.plug_type = type
        self.with_at = with_at

    def can_be_reduced(self):
        return self.with_at

    def reduction_strategy(self):
        return "@ is reduced to F.arg"

    def kind(self):
        return set_kinds

    def type(self):
        return self.plug_type

    def mk_value(self, old, new, with_at):
        if self.with_at:
            if with_at:
                r = IfThenElse(eq(new, At()), At(), new)
            else:
                r = IfThenElse(eq(new, old), old, new)
        else:
            r = new
        r.type = new.type
        return r

    def case_template(self, hole, with_at):
        field = 'field0'
        old_value = hole.type.sample()
        rec = Record({ field : old_value })
        value = self.mk_value(old = RecField(rec, field), new = hole, with_at = with_at)
        ea = ExceptArg(ExceptArgLhs(ExceptArgLhsRec(field)), value)
        r = Except(rec, ea)
        r.type = RecordT({ field : value.type })
        expr = ne(RecField(r, field), hole)
        return self.testmodel_template(next = self.next_y(expr))

    def case(self, hole):
        return self.case_template(hole, with_at = self.with_at)

    def case_tlc_reduced(self, hole):
        args, kw = self.case_template(hole, with_at = False)
        return TlcModel(*args, **kw)

    def plug(self, type):
        return SkipReason.CanNotBePlug

class FunF(Feature):
    def __init__(self, type = any_t):
        super().__init__()
        self.plug_type = type

    def model_value_allowed(self):
        return True

    def kind(self):
        return set_kinds

    def type(self):
        return self.plug_type

    def case(self, hole):
        indef = self.indef0(hole.type, mk_name())
        r = Fun(indef, hole)
        r.type = FunT(hole.type, hole.type)
        expr = any_to_bool(r)
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        new_type = type.refine(FunT(any_t, any_t))
        if not new_type:
            return SkipReason.TypeMismatch
        return new_type.sample()

class DefFunF(Feature):
    def __init__(self, inlet):
        super().__init__()
        self.inlet = inlet

    def can_be_reduced(self):
        return self.inlet

    def reduction_strategy(self):
        return "LET definitions are reduced to global definitions"

    def model_value_allowed(self):
        return True

    def kind(self):
        return set_kinds

    def type(self):
        return any_t

    def new_fun(self, expr, inlet):
        name = mk_name()
        loc_arg = mk_name() if inlet else 'arg'
        indef = self.indef0(expr.type, loc_arg, toplevel = True)
        ty = FunT(expr.type, expr.type)
        d = DefFun(name, indef, expr, ty)
        d.type = ty
        ref = Def0Ref(name)

        if not inlet:
            self.globals.append(d)
            r = ref
        else:
            r = Let([d], ref)

        r.type = d.type
        r.kind = expr.kind
        return r

    def case(self, hole):
        ref = self.new_fun(hole, self.inlet)
        expr = any_to_bool(ref)
        return self.testmodel_template(next = self.next_y(expr))

    def case_tlc_reduced(self, hole):
        ref = self.new_fun(hole, False)
        expr = any_to_bool(ref)
        args, kw = self.testmodel_template(next = self.next_y(expr))
        return TlcModel(*args, **kw)

    def plug(self, type):
        new_type = type.refine(FunT(any_t, any_t))
        if not new_type:
            return SkipReason.TypeMismatch
        ref = self.new_fun(new_type.rhs.sample(), self.inlet)
        return ref

    def plug_tlc_reduced(self, type):
        new_type = type.refine(FunT(any_t, any_t))
        if not new_type:
            return SkipReason.TypeMismatch
        ref = self.new_fun(new_type.rhs.sample(), False)
        return ref

class DefFunRecursiveF(Feature):
    def __init__(self, inlet):
        super().__init__()
        self.inlet = inlet

    def can_be_reduced(self):
        return self.inlet

    def reduction_strategy(self):
        return "LET definitions are reduced to global definitions"

    def model_value_allowed(self):
        return True

    def kind(self):
        return set_kinds

    def type(self):
        return any_t

    def new_fun(self, expr, is_ref, inlet):
        name = mk_name()
        ref = Def0Ref(name)

        arg = mk_name() if inlet else 'arg'
        arg_ref = LocalRef(arg)
        indef = InDef0([arg], self.def_apalache(boolean, toplevel = True))
        ty = FunT(bool_t, expr.type)
        if not is_ref:
            body = IfThenElse(arg_ref, expr, FunApp(ref, Not(arg_ref)))
        else:
            body = expr
        d = DefFun(name, indef, body, ty)
        d.type = ty
        if inlet:
            r = Let([d], ref)
        else:
            r = ref
            self.globals.append(d)
        r.type = d.type
        r.kind = expr.kind
        return r

    def case_tlc(self, hole):
        ref = self.new_fun(hole, is_ref = False, inlet = self.inlet)
        expr = any_to_bool(ref)
        args, kw = self.testmodel_template(next = self.next_y(expr))
        return TlcModel(*args, **kw)

    def case_tlc_reduced(self, hole):
        ref = self.new_fun(hole, is_ref = True, inlet = False)
        expr = any_to_bool(ref)
        args, kw = self.testmodel_template(next = self.next_y(expr))
        return TlcModel(*args, **kw)

    def case_apalache(self, hole):
        assert not self.inlet
        ref = self.new_fun(hole, is_ref = True, inlet = False)
        expr = any_to_bool(ref)
        args, kw = self.testmodel_template(next = self.next_y(expr))
        return ApalacheModel(*args, **kw)

    def plug_tlc(self, type):
        new_type = type.refine(FunT(any_t, any_t))
        if not new_type:
            return SkipReason.TypeMismatch
        ref = self.new_fun(new_type.rhs.sample(), is_ref = False, inlet = self.inlet)
        return ref

    def plug_tlc_reduced(self, type):
        new_type = type.refine(FunT(any_t, any_t))
        if not new_type:
            return SkipReason.TypeMismatch
        ref = self.new_fun(new_type.rhs.sample(), is_ref = True, inlet = False)
        return ref

    def plug_apalache(self, type):
        new_type = type.refine(FunT(any_t, any_t))
        if not new_type:
            return SkipReason.TypeMismatch
        ref = self.new_fun(new_type.rhs.sample(), is_ref = True, inlet = False)
        return ref

class FunInDefF(Feature):
    def kind(self):
        return set_kinds

    def type(self):
        return InDefT(TupleT(any_t, any_t))

    def case(self, hole):
        indef = hole
        value = indef_tuple(indef)
        r = Fun(indef, self.def_apalache(value))
        r.type = FunT(value.type, value.type)
        expr = any_to_bool(r)
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        return SkipReason.AlreadyCombined

class RecordF(Feature):
    def __init__(self, type = any_t):
        super().__init__()
        self.plug_type = type

    def model_value_allowed(self):
        return True

    def kind(self):
        return set_kinds

    def type(self):
        return self.plug_type

    def case(self, hole):
        r = Record({"field0" : hole})
        r.type = RecordT({"field0" : hole.type})
        expr = any_to_bool(r)
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        ty = type.refine(RecordT({"field0" : self.plug_type}))
        if ty:
            return ty.sample()
        ty = type.refine(FunT(SetT(str_t), self.plug_type))
        if ty:
            r = RecordT({"field0" : ty.rhs}).sample()
            r.type = FunT(str_t, r.type.fields["field0"])
        return SkipReason.TypeMismatch

class TupleF(Feature):
    def __init__(self, type = any_t):
        super().__init__()
        self.plug_type = type

    def model_value_allowed(self):
        return True

    def kind(self):
        return set_kinds

    def type(self):
        return self.plug_type

    def case_expr(self, hole):
        r = Tuple(hole)
        r.type = SeqT(hole.type)
        r.kind = hole.kind
        return r

    def case(self, hole):
        r = self.case_expr(hole)
        expr = any_to_bool(self.def_apalache(r))
        return self.testmodel_template(next = self.next_y(expr))

    def plug_tlc(self, type):
        if type.match(SeqT(any_t)):
            new_type = type.refine(SeqT(self.plug_type))
        elif type.match(TupleT(any_t)):
            new_type = type.refine(TupleT(self.plug_type))
        else:
            return SkipReason.TypeMismatch
        r = new_type.sample()
        return r

    def plug_apalache(self, type):
        r = self.plug_tlc(type)
        if isinstance(r, SkipReason):
            return r
        return self.def_apalache(r)

class TupleEmptyF(Feature):
    def kind(self):
        return set_kinds

    def type(self):
        return any_t

    def case(self, hole):
        return SkipReason.CanNotBeCase

    def plug_tlc(self, type):
        if not type.match(SeqT(any_t)):
            return SkipReason.TypeMismatch
        r = Tuple()
        r.type = type.refine(SeqT(any_t)).sample().type
        r.kind = Kind.Const
        return r

    def plug_apalache(self, type):
        r = self.plug_tlc(type)
        if isinstance(r, SkipReason):
            return r
        r.kind = Kind.Const
        return self.def_apalache(r)

class QuantorF(Feature):
    def __init__(self, quantor):
        super().__init__()
        assert quantor in [Exists, ForAll]
        self.quantor = quantor

    def kind(self):
        return simple_kinds

    def feature_name(self):
        fn = super().feature_name()
        return f'{fn}({self.quantor.__name__})'

    def type(self):
        return bool_t

    def case(self, hole):
        loc = mk_name()
        indef = self.indef0(any_t, loc)
        expr = self.quantor(indef, hole)
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        if not type.match(bool_t):
            return SkipReason.TypeMismatch

        loc = mk_name()
        indef = self.indef0(any_t, loc)
        r = self.quantor(indef, Bool(True))
        r.type = bool_t
        r.kind = Kind.Const
        return r

class QuantorInDefF(Feature):
    def __init__(self, quantor):
        super().__init__()
        assert quantor in [Exists, ForAll]
        self.quantor = quantor

    def kind(self):
        return simple_kinds

    def feature_name(self):
        fn = super().feature_name()
        return f'{fn}({self.quantor.__name__})'

    def type(self):
        return InDefT(any_t)

    def case(self, hole):
        indef = hole
        value = indef_tuple(indef)
        expr = self.quantor(indef, any_to_bool(self.def_apalache(value)))
        expr.type = bool_t
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        return SkipReason.AlreadyCombined

class ChooseInDefF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return InDefT(TupleT(any_t, any_t))

    def case(self, hole):
        # CHOOSE does not support variant: CHOOSE x, y \in S : ...
        if isinstance(hole, InDef0) and len(hole.vars()) > 1:
            return SkipReason.TypeMismatch
        indef = hole
        value = indef_tuple(indef)
        expr = Choose(indef, any_to_bool(self.def_apalache(value)))
        expr.type = value.type
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        return SkipReason.AlreadyCombined

class ChooseF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return bool_t

    def case(self, hole):
        arg = mk_name()
        type = any_t.sample().type
        indef = self.indef0(type, arg)
        expr = Choose(indef, hole)
        expr.type = type
        expr.kind = hole.kind
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        if not type.match(any_t):
            return SkipReason.TypeMismatch

        ty = type.sample().type
        arg = mk_name()
        indef = self.indef0(ty, arg)
        r = Choose(indef, Bool(True))
        r.type = ty
        r.kind = Kind.Const
        return r

class InF(Feature):
    def __init__(self, op):
        super().__init__()
        assert op in [BinOpId.In, BinOpId.NotIn]
        self.op = op

    def model_value_allowed(self):
        return True

    def kind(self):
        return simple_kinds

    def type(self):
        return UnionT(any_t, InfSetT(any_t))

    def case(self, hole):
        if hole.type.match(SetT(any_t)) or hole.type.match(InfSetT(any_t)):
            lhs = hole.type.type.sample()
            rhs = hole
        else:
            lhs = hole
            rhs = Set0(hole)
        expr = BinOp(self.op, lhs, rhs)
        expr.type = bool_t
        expr.kind = hole.kind
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        if not type.match(bool_t):
            return SkipReason.TypeMismatch
        sample = any_t.sample()
        r = BinOp(self.op, sample, Set0(sample))
        r.type = bool_t
        r.kind = sample.kind
        return r

class InDef0F(Feature):
    # InDef0 can be used in two forms:
    # 1. F[u, v \in S] == ...
    # 2. F[u \in S, v \in S] == ...
    def __init__(self, extended):
        self.extended = extended

    def kind(self):
        return []

    def type(self):
        return any_t

    def case(self, hole):
        return SkipReason.CanNotBeCase

    def plug(self, type):
        if not type.match(InDefT(any_t)):
            return SkipReason.TypeMismatch
        r = InDefT(any_t).sample(self.extended)

        # Wrap set(s) into definition
        def replacer(expr):
            return self.def_apalache(expr, toplevel = True)
        r.replace_expr(replacer)
        return r

class InDef1F(Feature):
    def kind(self):
        return []

    def type(self):
        return any_t

    def case(self, hole):
        return SkipReason.CanNotBeCase

    def plug(self, type):
        if not type.match(InDefT(TupleT(any_t, any_t))):
            return SkipReason.TypeMismatch
        r = InDefT(TupleT(any_t, any_t)).sample()
        r.expr = self.def_apalache(r.expr, toplevel = True)
        return r

class BoxedF(Feature):
    def __init__(self):
        super().__init__()
        self.vars = Def0Ref('vars')

    def kind(self):
        return boxed_kinds

    def type(self):
        return bool_t

    def new_prop(self, expr, vars):
        if self.is_tlc:
            r = Boxed(expr, vars)
            r.type = bool_t
            r.kind = Kind.Boxed
            return r
        else:
            r = BinOp(BinOpId.Or, expr, eq(vars, Prime(vars)))
            r.type = bool_t
            r.kind = Kind.Boxed
            return r

    def case(self, hole):
        prop = self.new_prop(hole, self.vars)
        return self.testmodel_template(prop = prop)

    def plug(self, type):
        if Kind.Boxed not in self.kinds:
            return SkipReason.KindMismatch
        assert type.match(bool_t)

        expr = Prime(self.x())

        visible_variables = find_visible_variables(self.extends, self.modules)
        all_variables = visible_variables + self.variables

        vars = Tuple(*[LocalRef(v) for v, _ in all_variables])
        vars.type = TupleT(*[d.type for _, d in all_variables])
        vars.kind = Kind.State
        vars_def = self.def_expr(vars)
        prop = self.new_prop(expr, vars_def)
        return prop

class PrimeF(Feature):
    def kind(self):
        return [Kind.Const, Kind.State]

    def model_value_allowed(self):
        return True

    def type(self):
        return any_t

    def case(self, hole):
        expr = Prime(hole)
        expr.type = hole.type
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        if Kind.Action not in self.kinds:
            return SkipReason.KindMismatch
        if not type.match(any_t):
            return SkipReason.TypeMismatch
        if type.match(bool_t):
            expr = self.x()
        else:
            expr = type.sample()
        r = Prime(expr)
        r.type = expr.type
        r.kind = Kind.Action
        return r

class VariableF(Feature):
    def __init__(self, view_exclude = False):
        """
        If view_exclude is True, this variable will be excluded from TLC VIEW
        """
        super().__init__()
        self.view_exclude = view_exclude

    def can_be_reduced(self):
        return self.view_exclude

    def reduction_strategy(self):
        return "Model with VIEW is reduced to the same model without VIEW: VIEW must not change TLC behavior"

    def kind(self):
        return [Kind.State, Kind.Action]

    def model_value_allowed(self):
        return True

    def type(self):
        return any_t

    def case(self, hole):
        ref = self.new_var(hole.type, init = hole.type.sample())
        next = self.next_and(eq(Prime(ref), hole))
        if self.view_exclude:
            return self.testmodel_template(next = next, view_exclude = [ref.id])
        else:
            return self.testmodel_template(next = next)

    def case_tlc_reduced(self, hole):
        ref = self.new_var(hole.type, init = hole.type.sample())
        next = self.next_and(eq(Prime(ref), hole))
        args, kw = self.testmodel_template(next = next)
        return TlcModel(*args, **kw)

    def plug(self, type):
        if self.view_exclude:
            return SkipReason.VariableExcludedFromView
        if Kind.State not in self.kinds:
            return SkipReason.KindMismatch
        if not type.match(any_t):
            return SkipReason.TypeMismatch
        expr = type.sample()
        ref = self.new_var(expr.type, init = expr, unchanged=True)
        return ref

class Constant0F(Feature):
    def __init__(self, modelvalue):
        super().__init__()
        assert isinstance(modelvalue, bool)
        self.modelvalue = modelvalue

    def model_value_allowed(self):
        return True

    def feature_name(self):
        return f'{self.__class__.__name__}({str(self.modelvalue)})'

    def kind(self):
        return [Kind.Const]

    def type(self):
        return any_t

    def case(self, hole):
        if self.modelvalue:
            return SkipReason.CanNotBeCase

        assert hole.kind == Kind.Const

        if self.modelvalue:
            ref = self.new_const(hole.type, init = None)
            next = self.next_y(eq(ref, hole))
        else:
            subst = self.def_expr(hole)
            r = self.new_const(hole.type, init = subst)
            next = self.next_y(any_to_bool(r))

        return self.testmodel_template(next = next)

    def plug(self, type):
        if Kind.Const not in self.kinds:
            return SkipReason.KindMismatch
        if not type.match(any_t):
            return SkipReason.TypeMismatch

        if self.modelvalue:
            ty = type.refine(str_t)
            if not ty:
                # Try to use STRING as type for modelvalue (if possible), otherwise give up
                # Apalache does not support true model values and we stub them with strings
                ty = type
            expr = ty.sample()
            ref = self.new_const(expr.type, init = None)
        else:
            expr = type.sample()
            subst = self.def_expr(expr)
            ref = self.new_const(expr.type, init = subst)
        return ref

class Constant1F(Feature):
    def model_value_allowed(self):
        return True

    def kind(self):
        return [Kind.Const]

    def type(self):
        return any_t

    def new_def(self, expr):
        name = mk_name()
        arg = 'def_arg'
        arg_ref = LocalRef(arg)
        ty = Def1T(expr.type, expr.type)
        body = arg_ref
        self.globals.append(Def1(name, [arg], body, ty))
        ref = Def1Ref(name)
        ref.type = ty
        return ref

    def case(self, hole):
        assert hole.kind == Kind.Const

        if not self.is_ref:
            # TLC does not support constants of higher ranks
            if isinstance(hole, Def1App) and all(not isinstance(ty, Def1T) for ty in hole.fexpr.type.args):
                ref = self.new_const(hole.fexpr.type, init = hole.fexpr)
                r = Def1App(ref, *hole.args)
                r.type = hole.type
                r.kind = hole.kind
            else:
                subst = self.new_def(hole)
                ref = self.new_const(subst.type, init = subst)
                r = Def1App(ref, hole)
                r.type = hole.type
                r.kind = hole.kind
        else:
            r = hole
        next = self.next_y(any_to_bool(r))

        return self.testmodel_template(next = next)

    def plug(self, type):
        if Kind.Const not in self.kinds:
            return SkipReason.KindMismatch
        if not type.match(any_t):
            return SkipReason.TypeMismatch

        expr = type.sample()

        if not self.is_tlc:
            return expr

        subst = self.new_def(expr)
        ref = self.new_const(subst.type, init = subst)
        r = Def1App(ref, expr)
        r.type = expr.type
        r.kind = expr.kind
        return r

class FunAppF(Feature):
    def model_value_allowed(self):
        return True

    def kind(self):
        return set_kinds

    def type(self):
        return UnionT(
            FunT(any_t, any_t),
            RecordT({"field0" : any_t}),
            TupleT(any_t),
            SeqT(any_t),
            any_t)

    def case(self, hole):
        if not self.is_const_a_model_value(hole) and isinstance(hole.type, FunT):
            fexpr = self.def_apalache(hole)
            type = hole.type.rhs
            choose = Choose(InDef0(['fun_app_v0'], Domain(fexpr)), Bool(True))
            choose.type = hole.type.lhs
            choose.kind = hole.kind
            arg = self.def_expr(choose)
        elif not self.is_const_a_model_value(hole) and isinstance(hole.type, SeqT):
            fexpr = self.def_apalache(hole)
            type = hole.type.type
            arg = Num(1)
        elif not self.is_const_a_model_value(hole) and isinstance(hole.type, TupleT):
            fexpr = self.def_apalache(hole)
            assert len(hole.type.types) == 1
            type = hole.type.types[0]
            arg = Num(1)
        elif not self.is_const_a_model_value(hole) and isinstance(hole.type, RecordT):
            fexpr = self.def_apalache(hole)
            assert hole.type.match(RecordT({"field0" : any_t}))
            type = hole.type.fields["field0"]
            arg = Str("field0")
        else:
            arg = self.def_apalache(hole)
            f = Fun(InDef0(['v'], Set0(arg)), LocalRef('v'))
            f.type = FunT(arg.type, arg.type)
            f.kind = arg.kind
            fexpr = self.def_expr(f)
            type = hole.type
        r = FunApp(fexpr, arg)
        r.type = type
        expr = any_to_bool(r)
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        if not type.match(any_t):
            return SkipReason.TypeMismatch
        value = type.sample()
        f = Fun(InDef0(['v'], Set0(value)), LocalRef('v'))
        f.type = FunT(value.type, value.type)
        f.kind = value.kind
        fexpr = self.def_expr(f)
        expr = FunApp(fexpr, value)
        expr.type = value.type
        expr.kind = value.kind
        return expr

class BoolF(Feature):
    def __init__(self, value):
        super().__init__()
        self.value = value

    def kind(self):
        return simple_kinds

    def type(self):
        return bool_t

    def case(self, hole):
        return SkipReason.CanNotBeCase

    def plug(self, type):
        if not type.match(bool_t):
            return SkipReason.TypeMismatch
        expr = Bool(self.value)
        expr.type = bool_t
        expr.kind = Kind.Const
        return expr

class IntF(Feature):
    def __init__(self, value):
        super().__init__()
        self.value = value

    def kind(self):
        return simple_kinds

    def type(self):
        return num_t

    def case(self, hole):
        return SkipReason.CanNotBeCase

    def plug(self, type):
        if not type.match(num_t):
            return SkipReason.TypeMismatch
        self.add_extends_standard('Naturals')
        expr = Num(self.value)
        expr.type = num_t
        expr.kind = Kind.Const
        return expr

class NumBinaryF(Feature):
    def __init__(self, op, ty):
        super().__init__()
        self.op = op
        self.result_type = ty

    def kind(self):
        return simple_kinds

    def type(self):
        return num_t

    def case(self, hole):
        self.add_extends_standard('Naturals')
        expr = BinOp(self.op, hole, hole.type.sample())
        expr.type = self.result_type
        expr.kind = hole.kind
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        if not type.match(self.result_type):
            return SkipReason.TypeMismatch

        self.add_extends_standard('Naturals')

        lhs = Num(2)
        rhs = Num(1)

        r = BinOp(self.op, lhs, rhs)
        r.type = self.result_type
        r.kind = Kind.Const
        return r

class NumUnaryMinusF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return num_t

    def case(self, hole):
        self.add_extends_standard('Integers')
        expr = UnaryMinus(hole)
        expr.type = num_t
        expr.kind = hole.kind
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        if not type.match(num_t):
            return SkipReason.TypeMismatch

        self.add_extends_standard('Integers')

        r = UnaryMinus(Num(2))
        r.type = num_t
        r.kind = Kind.Const
        return r

class ExtendsF(Feature):
    def __init__(self, search_path):
        super().__init__()
        self.search_path = search_path

    def model_value_allowed(self):
        return True

    def kind(self):
        return [Kind.Nice, Kind.Boxed, Kind.Temporal, Kind.Action, Kind.State, Kind.Const]

    def type(self):
        return any_t

    def new_module(self):
        conjunction = build_init(self.variables, self.extends, self.modules)
        module = self.def_module(init = conjunction, search_path = self.search_path)
        self.add_extends(module)
        return module

    def case(self, hole):
        if isinstance(hole, DefRef):
            expr = hole
        elif isinstance(hole, Def1App):
            expr = hole
        elif isinstance(hole, FunApp) and isinstance(hole.fexpr, Def0Ref):
            expr = hole
        else:
            expr = self.def_expr(hole)

        m = self.new_module()
        r = any_to_bool(expr)

        if hole.kind in [Kind.Action, Kind.State, Kind.Const]:
            return self.testmodel_template(next = self.next_y(r))

        assert hole.kind in [Kind.Nice, Kind.Temporal, Kind.Boxed]
        return self.testmodel_template(prop = r)

    def plug(self, type):
        if not type.match(any_t):
            return SkipReason.TypeMismatch

        ref = self.def_expr(type.sample())
        self.new_module()
        return ref

class InstanceF(Feature):
    def __init__(self, with_stmt, named, search_path):
        super().__init__()
        self.with_stmt = with_stmt
        self.named = named
        self.search_path = search_path

    def model_value_allowed(self):
        return True

    def kind(self):
        return [Kind.Nice, Kind.Boxed, Kind.Temporal, Kind.Action, Kind.State, Kind.Const]

    def type(self):
        return any_t

    def new_module(self):
        module = self.def_module(search_path = self.search_path)
        return module

    def bang(self, instance_name, ref):
        name = f'{instance_name}!{ref.id}'
        if isinstance(ref, Def0Ref):
            return Def0Ref(name)
        if isinstance(ref, Def1Ref):
            return Def1Ref(name)
        assert isinstance(ref, ConstRef)
        return ConstRef(name)

    def instance(self, instance_stmt, expr):
        instance_ref = instance_stmt.name
        assert (self.named and instance_stmt.name) or (not self.named and not instance_ref)
        if instance_ref:
            if isinstance(expr, DefRef):
                expr = self.bang(instance_ref, expr)
            elif isinstance(expr, Def1App) and isinstance(expr.fexpr, DefRef):
                args = []
                for arg in expr.args:
                    if isinstance(arg, DefRef):
                        arg = self.bang(instance_ref, arg)
                    args.append(arg)
                expr = Def1App(self.bang(instance_ref, expr.fexpr), *args)
            elif isinstance(expr, FunApp) and isinstance(expr.fexpr, DefRef):
                expr = FunApp(self.bang(instance_ref, expr.fexpr), *expr.args)
            else:
                assert False, "Unreachable code"
        self.globals.append(instance_stmt)

        return expr

    # Take definition from instantiated module and make proxy one with the same type
    # to use as initializer in CFG
    def forward_definition(self, instance_ref, ref):
        assert isinstance(ref, DefRef)

        imported_ref = self.bang(instance_ref, ref)
        imported_ref.type = ref.type
        imported_ref.kind = Kind.Const

        name = mk_name()
        if isinstance(ref.type, Def1T):
            # This code handles single argument operators only, because
            # the generator does not produce more complex operators
            arg = 'def_arg'
            arg_ref = LocalRef(arg)
            body = Def1App(imported_ref, arg_ref)
            g = Def1(name, [arg], body, ref.type)
            r = Def1Ref(name)
        else:
            g = Def0(name, imported_ref, ref.type)
            r = Def0Ref(name)

        r.type = ref.type
        r.kind = Kind.Const

        return (r, g)

    def case(self, hole):
        if isinstance(hole, DefRef):
            expr = hole
        elif isinstance(hole, Def1App) and isinstance(hole.fexpr, DefRef):
            expr = hole
        elif isinstance(hole, FunApp) and isinstance(hole.fexpr, DefRef):
            expr = hole
        else:
            expr = self.def_expr(hole)

        constants = {}
        constants.update(self.constants)
        constants.update(find_visible_constants(self.extends, self.modules))

        # Collect all the variables; order matters
        variables = []
        variables.extend(find_visible_variables(self.extends, self.modules))
        variables.extend(self.variables)

        m = self.new_module()

        with_stmt = {}

        instance_ref = mk_name() if self.named else None

        # For every constant visible in `m` make constant with the same name
        # and localize its initializer
        forward_defs = []
        for n, desc in constants.items():
            name = n if not self.with_stmt else None
            if self.named and desc.init:
                # Constant initializer in instantiated module is not visible anymore
                (init, fwd) = self.forward_definition(instance_ref, desc.init)
                forward_defs.append(fwd)
            else:
                init = desc.init
            ref = self.new_const(desc.type, init = init, name = name)
            with_stmt[n] = ref

        # For every variable visible in `m` make a corresponding variable
        for name, desc in variables:
            if self.with_stmt:
                # Generate new name
                var_name = None
                # Make next action complete (simplest way)
                unchanged = True
            else:
                # Reuse exiting variable name
                var_name = name
                unchanged = desc.unchanged

            init = desc.init
            if self.named and isinstance(init, DefRef):
                init = self.bang(instance_ref, init)
            ref = self.new_var(desc.type, name = var_name, init = init, unchanged = unchanged)
            with_stmt[name] = ref

        instance_stmt = Instance(m, with_stmt = with_stmt if self.with_stmt else {}, name = instance_ref)
        expr = self.instance(instance_stmt, expr)
        expr.type = hole.type
        expr.kind = hole.kind

        self.globals.extend(forward_defs)

        r = any_to_bool(expr)

        if hole.kind in [Kind.Action, Kind.State, Kind.Const]:
            return self.testmodel_template(next = self.next_y(r))

        assert hole.kind in [Kind.Nice, Kind.Temporal, Kind.Boxed]
        return self.testmodel_template(prop = r)

    def plug(self, type):
        if not type.match(any_t):
            return SkipReason.TypeMismatch

        expr = type.sample()
        const = self.new_const(expr.type, init = expr)
        ref = self.def_expr(const)
        m = self.new_module()

        if not self.with_stmt:
            const_name = const.id
        else:
            const_name = None

        const_replace = self.def_expr(expr, name = const_name)

        instance_ref = mk_name() if self.named else None
        if self.with_stmt:
            instance_stmt = Instance(m, { const.id : const_replace }, name = instance_ref)
        else:
            instance_stmt = Instance(m, name = instance_ref)

        r = self.instance(instance_stmt, ref)
        r.type = ref.type
        r.kind = ref.kind
        return r

class EnabledF(Feature):
    # What kind is expected to plug
    def kind(self):
        return simple_kinds

    # What type is expected to be plugged in
    def type(self):
        return bool_t

    def case_tlc(self, hole):
        expr = Enabled(eq(hole, Bool(True)))
        expr.type = bool_t
        expr.kind = Kind.State
        args, kw = self.testmodel_template(inv = expr)
        return TlcModel(*args, **kw)

    def case_apalache(self, hole):
        if hole.kind in [Kind.Const, Kind.State]:
            # ENABLED e == e, if e is state predicate
            expr = eq(hole, Bool(True))
        else:
            # Apalache does not support ENABLED
            # so this will result in crash to be
            # investigated manually
            expr = Enabled(eq(hole, Bool(True)))
            expr.type = bool_t
        expr.kind = Kind.State

        args, kw = self.testmodel_template(inv = expr)
        return ApalacheModel(*args, **kw)

    def plug_tlc(self, type):
        if self.kinds == [Kind.Const]:
            return SkipReason.KindMismatch

        if not type.match(bool_t):
            return SkipReason.TypeMismatch

        r = Enabled(Bool(True))
        r.type = bool_t
        r.kind = Kind.State
        return r

    def plug_apalache(self, type):
        if self.kinds == [Kind.Const]:
            return SkipReason.KindMismatch

        if not type.match(bool_t):
            return SkipReason.TypeMismatch

        r = Bool(True)
        r.type = bool_t
        r.kind = Kind.State
        return r

class AssumeF(Feature):
    def __init__(self, named):
        super().__init__()
        self.named = named

    # What kind is expected to plug
    def kind(self):
        return [Kind.Const]

    # What type is expected to be plugged in
    def type(self):
        return bool_t

    def case_tlc(self, hole):
        name = mk_name() if self.named else None
        assume = Assume(hole, name = name)
        trivial = eq(Bool(True), Bool(True))
        self.globals.append(assume)
        args, kw = self.testmodel_template(inv = trivial)
        return TlcModel(*args, **kw)

    def case_apalache(self, hole):
        args, kw = self.testmodel_template(inv = hole)
        return ApalacheModel(*args, **kw)

    def plug(self, type):
        return SkipReason.AssumeIsNotEmbeddable

class LambdaF(Feature):
    def model_value_allowed(self):
        return True

    def kind(self):
        return [Kind.Nice, Kind.Boxed, Kind.Temporal, Kind.Action, Kind.State, Kind.Const]

    def type(self):
        return any_t

    def lam(self, expr):
        arg = mk_name()
        ty = Def1T(bool_t, expr.type)
        body = expr
        l = Lambda([arg], body, ty)
        l.type = ty
        l.kind = expr.kind
        return l

    def new_def(self, expr):
        name = mk_name()
        arg = mk_name()
        arg_ref = LocalRef(arg)
        ty = Def1T(Def1T(bool_t, expr.type), expr.type)
        body = Def1App(arg_ref, Bool(False))
        self.globals.append(Def2(name, [], [arg], body, ty))
        ref = Def1Ref(name)
        ref.type = ty

        lam = self.lam(expr)

        r = Def1App(ref, lam)
        r.type = ty.rhs
        r.kind = expr.kind
        return r

    def case_tlc(self, hole):
        ref = self.new_def(hole)
        r = any_to_bool(ref)

        if hole.kind in [Kind.Action, Kind.State, Kind.Const]:
            args, kw = self.testmodel_template(next = self.next_y(r))
            return TlcModel(*args, **kw)

        assert hole.kind in [Kind.Nice, Kind.Temporal, Kind.Boxed]
        args, kw = self.testmodel_template(prop = r)
        return TlcModel(*args, **kw)

    def case_apalache(self, hole):
        if hole.kind in [Kind.Action, Kind.State, Kind.Const]:
            r = any_to_bool(hole)
            args, kw = self.testmodel_template(next = self.next_y(r))
            return ApalacheModel(*args, **kw)

        assert hole.kind in [Kind.Nice, Kind.Temporal, Kind.Boxed] and hole.type is bool_t
        args, kw = self.testmodel_template(prop = hole)
        return ApalacheModel(*args, **kw)

    def plug(self, type):
        ty = type.refine(Def1T(any_t, any_t))
        if not ty:
            return SkipReason.TypeMismatch;

        ty1 = Def1T(ty.lhs.sample().type, ty.rhs.sample().type)
        arg = mk_name()
        arg_ref = LocalRef(arg)
        arg_ref.type = ty1.lhs
        arg_ref.kind = Kind.Const

        if ty1.lhs == ty1.rhs:
            body = arg_ref
        elif ty1.rhs == bool_t:
            body = any_to_bool(arg_ref)
        else:
            body = ty1.rhs.sample()
        r = Lambda([arg], body, ty1)
        r.type = ty1
        r.kind = Kind.Const
        return r

class DefFunInDefF(Feature):
    def __init__(self, inlet):
        super().__init__()
        self.inlet = inlet

    def can_be_reduced(self):
        return self.inlet

    def reduction_strategy(self):
        return "LET definitions are reduced to global definitions"

    def model_value_allowed(self):
        return True

    def kind(self):
        return set_kinds

    def type(self):
        return InDefT(TupleT(any_t, any_t))

    def new_fun(self, indef, inlet):
        name = mk_name()
        value = indef_tuple(indef)
        ty = FunT(value.type, value.type)
        ref = Def0Ref(name)
        d = DefFun(name, indef, self.def_apalache(value), ty)
        d.type = ty
        if inlet:
            r = Let([d], ref)
        else:
            self.globals.append(d)
            r = ref
        r.type = ty
        r.kind = indef.kind
        return r

    def case(self, hole):
        r = self.new_fun(hole, self.inlet)
        expr = any_to_bool(r)
        return self.testmodel_template(next = self.next_y(expr))

    def case_tlc_reduced(self, hole):
        r = self.new_fun(hole, False)
        expr = any_to_bool(r)
        args, kw = self.testmodel_template(next = self.next_y(expr))
        return TlcModel(*args, **kw)

    def plug(self, type):
        return SkipReason.AlreadyCombined

class OneLineCommentF(Feature):
    def can_be_reduced(self):
        return True

    def reduction_strategy(self):
        return "Replace spec with the same without comments"

    def kind(self):
        return simple_kinds

    def type(self):
        return any_t

    def case(self, hole):
        return SkipReason.CanNotBeCase

    def plug(self, type):
        # There is no sense in combining comments with features of irregular type
        if not type.regular():
            return SkipReason.TypeMismatch

        if not self.is_ref:
            self.globals.append(OneLineComment('one line comment'))
        return type.sample()

class MultiLineCommentF(Feature):
    def can_be_reduced(self):
        return True

    def reduction_strategy(self):
        return "Replace spec with the same without comments"

    def kind(self):
        return simple_kinds

    def type(self):
        return any_t

    def case(self, hole):
        return SkipReason.CanNotBeCase

    def plug(self, type):
        # There is no sense in combining comments with features of irregular type
        if not type.regular():
            return SkipReason.TypeMismatch

        if not self.is_ref:
            self.globals.append(MultiLineComment('multi', 'line', 'comment'))
        return type.sample()

class Cross2F(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return SetT(any_t)

    def case(self, hole):
        lhs = hole
        sample = SetT(any_t).sample()
        rhs = self.def_expr(sample)
        expr = Cross(lhs, rhs)
        expr.type = SetT(TupleT(lhs.type.type, rhs.type.type))
        r = any_to_bool(expr)
        return self.testmodel_template(next = self.next_y(r))

    def plug(self, type):
        ty = type.refine(SetT(TupleT(any_t, any_t)))
        if not ty:
            return SkipReason.TypeMismatch
        lhs_ty = SetT(ty.type.types[0])
        rhs_ty = SetT(ty.type.types[1])
        lhs = self.def_expr(lhs_ty.sample())
        rhs = self.def_expr(rhs_ty.sample())
        expr = Cross(lhs, rhs)
        expr.type = SetT(TupleT(lhs.type.type, rhs.type.type))
        expr.kind = Kind.Const

        return expr

class Cross3F(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return SetT(any_t)

    def case(self, hole):
        lhs = hole
        sample = SetT(any_t).sample()
        rhs = self.def_expr(sample)
        expr = Cross(lhs, rhs, rhs)
        expr.type = SetT(TupleT(lhs.type.type, rhs.type.type, rhs.type.type))
        r = any_to_bool(expr)
        return self.testmodel_template(next = self.next_y(r))

    def plug(self, type):
        ty = type.refine(SetT(TupleT(any_t, any_t, any_t)))
        if not ty:
            return SkipReason.TypeMismatch
        lhs_ty = SetT(ty.type.types[0])
        rhs_ty = SetT(ty.type.types[1])
        lhs = self.def_expr(lhs_ty.sample())
        rhs = self.def_expr(rhs_ty.sample())
        expr = Cross(lhs, rhs, rhs)
        expr.type = SetT(TupleT(lhs.type.type, rhs.type.type, rhs.type.type))
        expr.kind = Kind.Const

        return expr

def SetOfFunctions(name):
    return UninterpretedDef(r'''
%s(D, R) ==
    LET
        F[n \in 0..Cardinality(D)] ==
            IF n = 0
            THEN {<<>>}
            ELSE
                LET
                    F0 == F[n - 1]
                    \* All functions in F0 have the same domain, choose any one
                    f0 == CHOOSE f \in F0 : TRUE
                    D_smaller == DOMAIN f0
                    d1 == CHOOSE d \in (D \ D_smaller) : TRUE
                    D_bigger == D_smaller \union {d1}
                IN
                    {
                        [d \in D_bigger |-> IF d \in DOMAIN f THEN f[d] ELSE r]
                        : f \in F0, r \in R
                    }
    IN
        F[Cardinality(D)]''' % name)

class FunSetF(Feature):
    def can_be_reduced(self):
        return True

    def reduction_strategy(self):
        return r"For finite R replace [D -> R] with explicit function set enumeration; for infinite R replace (f \in [D -> R]) with conjunction (DOMAIN f = D /\ (\A x \in D : f[x] \in R))"

    def kind(self):
        return simple_kinds

    def type(self):
        return UnionT(SetT(any_t), InfSetT(any_t))

    def fsets(self, lhs, rhs):
        self.add_extends_standard('Naturals', 'FiniteSets')

        assert isinstance(lhs.type, SetT)
        assert isinstance(rhs.type, SetT)

        name = mk_name()
        def1 = SetOfFunctions(name)
        self.globals.append(def1)
        ref = Def1Ref(name)
        # That's not correct in general, but it is OK for reduced testcase
        ref.type = bool_t
        expr = Def1App(ref, lhs, rhs)
        expr.type = SetT(FunT(lhs.type.type, rhs.type.type))
        return expr

    def case(self, hole):
        sample = SetT(any_t).sample()
        lhs = self.def_expr(sample)
        rhs = hole
        fset = FunSet(lhs, rhs)
        assert isinstance(lhs.type, SetT)
        assert isinstance(rhs.type, SetT) or isinstance(rhs.type, InfSetT)
        fset.type = SetT(FunT(lhs.type.type, rhs.type.type))

        felem = FunT(lhs.type.type, rhs.type.type).sample()
        r = BinOp(BinOpId.In, felem, fset)
        r.type = bool_t
        r.kind = hole.kind
        return self.testmodel_template(next = self.next_y(r))

    def case_tlc_reduced(self, hole):
        sample = SetT(any_t).sample()
        lhs = self.def_expr(sample)
        rhs = hole

        felem = self.def_expr(FunT(lhs.type.type, rhs.type.type).sample())

        if isinstance(hole, SetT):
            fset = self.fsets(lhs, rhs)
            r = BinOp(BinOpId.In, felem, fset)
        else:
            arg = mk_name()
            r = BinOp(BinOpId.AndMultiLine,
                BinOp(BinOpId.Eq, Domain(felem), lhs),
                ForAll(
                    InDef0([arg], lhs),
                    BinOp(BinOpId.In,
                        FunApp(felem, LocalRef(arg)),
                        rhs)))

        r.type = bool_t
        r.kind = hole.kind
        args, kw = self.testmodel_template(next = self.next_y(r))
        return TlcModel(*args, **kw)

    def plug_template(self, type, combiner):
        ty = type.refine(SetT(FunT(any_t, any_t)))
        if not ty:
            return SkipReason.TypeMismatch
        lhs_ty = SetT(ty.type.lhs)
        rhs_ty = SetT(ty.type.rhs)
        lhs = self.def_expr(lhs_ty.sample())
        rhs = self.def_expr(rhs_ty.sample())
        expr = combiner(lhs, rhs)
        u = lhs.type.type
        v = rhs.type.type
        expr.type = SetT(FunT(u, v))
        expr.kind = Kind.Const

        return expr

    def plug(self, type):
        return self.plug_template(type, FunSet)

    def plug_tlc_reduced(self, type):
        def combiner(lhs, rhs):
            return self.fsets(lhs, rhs)

        return self.plug_template(type, combiner)

class RecordSetF(Feature):
    def __init__(self):
        self.field = 'field'

    def can_be_reduced(self):
        return True

    def reduction_strategy(self):
        return "For finite R replace [field : R] with explicit function set enumeration; for infinite R replace (f \in [field : R]) with conjunction (DOMAIN f = {'field'} /\ f['field'] \in R)"

    def kind(self):
        return simple_kinds

    def type(self):
        return UnionT(SetT(any_t), InfSetT(any_t))

    def fsets(self, rhs):
        global function_set

        self.add_extends_standard('Naturals', 'FiniteSets')

        lhs = Set0(Str(self.field))
        lhs.type = SetT(str_t)
        assert isinstance(rhs.type, SetT)

        name = mk_name()
        def1 = SetOfFunctions(name)
        self.globals.append(def1)
        ref = Def1Ref(name)
        # That's not correct in general, but it is OK for reduced testcase
        ref.type = bool_t
        expr = Def1App(ref, lhs, rhs)
        expr.type = SetT(FunT(lhs.type.type, rhs.type.type))
        return expr

    def case(self, hole):
        rset = RecordSet({ self.field : hole })
        rset.type = SetT(FunT(str_t, hole.type.type))

        rec = rset.type.type.sample()
        r = BinOp(BinOpId.In, rec, rset)
        r.type = bool_t
        r.kind = hole.kind
        return self.testmodel_template(next = self.next_y(r))

    def case_tlc_reduced(self, hole):
        rhs = hole

        felem = self.def_expr(FunT(str_t, rhs.type.type).sample())

        if isinstance(hole, SetT):
            fset = self.fsets(rhs)
            r = BinOp(BinOpId.In, felem, fset)
        else:
            arg = Str(self.field)
            r = BinOp(BinOpId.AndMultiLine,
                BinOp(BinOpId.Eq, Domain(felem), Set0(arg)),
                BinOp(BinOpId.In, FunApp(felem, arg), rhs))

        r.type = bool_t
        r.kind = hole.kind
        args, kw = self.testmodel_template(next = self.next_y(r))
        return TlcModel(*args, **kw)

    def plug_template(self, type, combiner):
        ty = type.refine(SetT(FunT(str_t, any_t)))
        if not ty:
            return SkipReason.TypeMismatch
        rhs_ty = SetT(ty.type.rhs)
        rhs = self.def_expr(rhs_ty.sample())
        expr = combiner(rhs)
        v = rhs.type.type
        expr.type = SetT(FunT(str_t, v))
        expr.kind = Kind.Const

        return expr

    def plug(self, type):
        def combiner(rhs):
            return RecordSet({ self.field : rhs })
        return self.plug_template(type, combiner)

    def plug_tlc_reduced(self, type):
        def combiner(rhs):
            return self.fsets(rhs)

        return self.plug_template(type, combiner)

class SetUnionInterceptDifferenceF(Feature):
    def __init__(self, op):
        super().__init__()
        assert op in [BinOpId.SetDiff, BinOpId.Union, BinOpId.Intersect]
        self.op = op

    def kind(self):
        return simple_kinds

    def type(self):
        return SetT(any_t)

    def case(self, hole):
        expr = BinOp(self.op, hole, hole.type.sample())
        expr.type = hole.type
        expr.kind = hole.kind
        r = any_to_bool(expr)
        return self.testmodel_template(next = self.next_y(r))

    def plug(self, type):
        ty = type.refine(SetT(any_t))
        if not ty:
            return SkipReason.TypeMismatch

        lhs = ty.sample()
        rhs = lhs.type.sample()

        r = BinOp(self.op, lhs, rhs)
        r.type = lhs.type
        r.kind = lhs.kind
        return r

class SubsetEqF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return SetT(any_t)

    def case(self, hole):
        expr = BinOp(BinOpId.SubsetEq, hole, hole.type.sample())
        expr.type = bool_t
        expr.kind = hole.kind
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        if not type.match(bool_t):
            return SkipReason.TypeMismatch

        lhs = SetT(any_t).sample()
        rhs = lhs.type.sample()

        r = BinOp(BinOpId.SubsetEq, lhs, rhs)
        r.type = bool_t
        r.kind = Kind.Const
        return r

# TODO: This is not used anymore, but still here as a reference
# for AST version
def SetOfSets(name):
    return UninterpretedDef(r'''
\* @type: Set(a) => Set(Set(a));
%s(D) ==
    LET
        \* @type: (Set(Set(a)), a) => Set(Set(a));
        F(sets, e) == { set \union {e} : set \in sets } \union sets
    IN
        ApaFoldSet(F, {{}}, D)
''' % name)

class SubsetF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return SetT(any_t)

    def fold_set(self, func, dom):
        self.add_extends_standard('Apalache')
        ref = Def1Ref('ApaFoldSet')
        r = Def1App(ref, func, Set0(Set0()), dom)
        r.type = SetT(dom.type)
        r.kind = dom.kind
        return r

    def func_decl(self, elem_type):
        # Encoding following declaration:
        #   \* @type: (Set(Set(a)), a) => Set(Set(a));
        #   F(sets, e) == { set \union {e} : set \in sets } \union sets
        name = mk_name()
        set_name = mk_name()
        sets_name = mk_name()
        elem_name = mk_name()
        set = LocalRef(set_name)
        sets = LocalRef(sets_name)
        elem = LocalRef(elem_name)
        ty = Def1T(SetT(SetT(elem_type)), SetT(SetT(elem_type)), rest_args = [elem_type])
        body = BinOp(BinOpId.Union,
            sets,
            Set2(
                InDef0([set_name], sets),
                BinOp(BinOpId.Union, set, Set0(elem))
                )
            )
        return (LocalRef(name), Def1(name, [sets_name, elem_name], body, ann = ty))

    def subsets(self, set):
        name = mk_name()
        arg_name = mk_name()
        arg = LocalRef(arg_name)
        arg.type = set.type
        arg.kind = set.kind

        ref, decl = self.func_decl(set.type.type)
        body = Let([decl], self.fold_set(ref, arg))

        df = Def1(name, [arg_name], body)
        self.globals.append(df)

        expr = Def1App(Def1Ref(name), set)
        expr.type = SetT(set.type)
        expr.kind = set.kind
        return expr

    def case(self, hole):
        expr = Subset(hole)
        expr.type = SetT(hole.type)
        expr.kind = hole.kind
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def case_apalache(self, hole):
        expr = self.subsets(hole)
        args, kw = self.testmodel_template(next = self.next_y(any_to_bool(expr)))
        return ApalacheModel(*args, **kw)

    def plug_template(self, type, subsets):
        ty = type.refine(SetT(SetT(any_t)))
        if not ty:
            return SkipReason.TypeMismatch

        arg = ty.type.sample()
        arg.kind = Kind.Const

        r = subsets(arg)

        r.type = SetT(arg.type)
        r.kind = Kind.Const
        return r

    def plug_tlc(self, type):
        return self.plug_template(type, Subset)

    def plug_apalache(self, type):
        def f(arg):
            return self.subsets(arg)
        return self.plug_template(type, f)

@unique
class IfCheck(Enum):
    If = auto()
    Then = auto()
    Else = auto()

class IfF(Feature):
    def __init__(self, check : IfCheck):
        super().__init__()
        self.check = check

    def kind(self):
        return simple_kinds

    def type(self):
        if self.check == IfCheck.If:
            return bool_t
        return any_t

    def case(self, hole):
        if self.check == IfCheck.If:
            if self.is_const_a_model_value(hole):
                return SkipReason.ModelValueCanNotBeUsed
            expr = IfThenElse(hole, Bool(False), Bool(True))
            expr.type = bool_t
        elif self.check == IfCheck.Then:
            expr = IfThenElse(Bool(True), hole, hole.type.sample())
            expr.type = hole.type
        else:
            assert self.check == IfCheck.Else
            expr = IfThenElse(Bool(False), hole.type.sample(), hole)
            expr.type = hole.type
        expr.kind = hole.kind
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug_tlc(self, type):
        if not type.match(any_t):
            return SkipReason.TypeMismatch
        u = type.sample()
        expr = IfThenElse(Bool(False), Set0(u), u)
        expr.type = u.type
        expr.kind = u.kind
        return expr

    def plug_apalache(self, type):
        if not type.match(any_t):
            return SkipReason.TypeMismatch
        u = type.sample()
        return u

class DomainF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return FunT(any_t, any_t)

    def case(self, hole):
        expr = Domain(hole)
        expr.type = SetT(hole.type.lhs)
        expr.kind = hole.kind
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        ty = type.refine(SetT(any_t))
        if not ty:
            return SkipReason.TypeMismatch

        fun = FunT(ty.type, any_t).sample()
        r = Domain(fun)
        r.type = SetT(fun.type.lhs)
        r.kind = Kind.Const
        return r

class UnionF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return SetT(SetT(any_t))

    def case(self, hole):
        expr = Union(hole)
        assert isinstance(hole.type, SetT)
        expr.type = hole.type.type
        expr.kind = hole.kind
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        ty = type.refine(SetT(any_t))
        if not ty:
            return SkipReason.TypeMismatch

        sets = SetT(ty).sample()
        r = Union(sets)
        r.type = sets.type.type
        r.kind = Kind.Const
        return r

class UnchangedF(Feature):
    def kind(self):
        return [Kind.State]

    def type(self):
        return any_t

    def case(self, hole):
        expr = Unchanged(hole)
        expr.type = bool_t
        expr.kind = Kind.Action
        return self.testmodel_template(next = self.next_and(expr))

    def plug(self, type):
        if Kind.Action not in self.kinds:
            return SkipReason.KindMismatch

        if not type.match(bool_t):
            return SkipReason.TypeMismatch

        arg = any_t.sample()
        r = Unchanged(arg)
        r.type = bool_t
        r.kind = Kind.Const
        return r

class StrF(Feature):
    def __init__(self, value):
        super().__init__()
        self.value = value

    def kind(self):
        return simple_kinds

    def type(self):
        return str_t

    def case(self, hole):
        return SkipReason.CanNotBeCase

    def plug(self, type):
        if not type.match(str_t):
            return SkipReason.TypeMismatch
        expr = Str(self.value)
        expr.type = str_t
        expr.kind = Kind.Const
        return expr

class SeqLenF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return UnionT(SeqT(any_t), TupleT(), TupleT(any_t), TupleT(any_t, any_t), str_t)

    def seq_len(self, arg):
        self.add_extends_standard('Sequences')
        ref = Def1Ref('Len')
        ref.type = Def1T(arg.type, num_t)
        r = Def1App(ref, arg)
        r.type = num_t
        r.kind = arg.kind
        return r

    def case(self, hole):
        expr = self.seq_len(hole)
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def case_apalache(self, hole):
        if hole.type == str_t:
            expr = Num(len(hole.s))
            expr.type = num_t
        else:
            expr = self.seq_len(hole)
        args, kw = self.testmodel_template(next = self.next_y(any_to_bool(expr)))
        return ApalacheModel(*args, **kw)

    def plug(self, type):
        if not type.match(num_t):
            return SkipReason.TypeMismatch

        arg = SeqT(any_t).sample()
        return self.seq_len(arg)

class SeqConcatF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return UnionT(SeqT(any_t), str_t)

    def seq_concat(self, lhs):
        self.add_extends_standard('Sequences')
        l = self.def_apalache(lhs)
        r = self.def_apalache(lhs.type.sample())
        r = BinOp(BinOpId.Concat, l, r)
        r.type = lhs.type
        r.kind = lhs.kind
        return r

    def seq_string(self, lhs):
        expr = Str(lhs.s + str_t.sample().s)
        expr.type = str_t
        expr.kind = Kind.Const
        return expr

    def case(self, hole):
        expr = self.seq_concat(hole)
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def case_apalache(self, hole):
        if hole.type == str_t:
            expr = self.seq_string(hole)
        else:
            expr = self.seq_concat(hole)
        args, kw = self.testmodel_template(next = self.next_y(any_to_bool(expr)))
        return ApalacheModel(*args, **kw)

    def plug(self, type):
        if type.match(SeqT(any_t)):
            ty = type.refine(SeqT(any_t))
            arg = ty.sample()
            return self.seq_concat(arg)
        elif type.match(str_t):
            arg = type.sample()
            return self.seq_concat(arg)
        else:
            return SkipReason.TypeMismatch

    def plug_apalache(self, type):
        if type.match(SeqT(any_t)):
            ty = type.refine(SeqT(any_t))
            arg = ty.sample()
            return self.seq_concat(arg)
        elif type == str_t:
            arg = type.sample()
            return self.seq_string(arg)
        else:
            return SkipReason.TypeMismatch

# TODO: This is not used anymore, but still here as a reference
# for AST version
def SetOfSeqs(name, len):
    return UninterpretedDef(r'''
\* @type: Set(a) => Set(Seq(a));
%s(D) ==
    LET
        \* @type: (Set(Seq(a)), Int) => Set(Seq(a));
        F(sets, ix) == { Append(seq, e) : seq \in sets, e \in D } \union sets
    IN
        ApaFoldSet(F, {<<>>}, 1..%d)
''' % (name, len))

class SeqSeqF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return UnionT(SetT(any_t), InfSetT(any_t))

    # Apalache does not support Seq(_). Use workaround: https://apalache.informal.systems/docs/apalache/known-issues.html#using-seqs
    # The test generator never produces sequences larger than 2.
    # False negative still possible, where TLC crashes (because Set(_) is infinite) and Apalache not
    def fold_set(self, func):
        self.add_extends_standard('Apalache')
        ref = Def1Ref('ApaFoldSet')
        return Def1App(ref, func, Set0(Tuple()), Set0(*(Num(i) for i in range(1, 3))))

    def func_decl(self, dom):
        self.add_extends_standard('Sequences')
        # Encoding following declaration:
        #   \* @type: (Set(Seq(a)), Int) => Set(Seq(a));
        #   F(sets, ix) == { Append(seq, e) : seq \in sets, e \in D } \union sets
        name = mk_name()
        ix_name = mk_name()
        seq_name = mk_name()
        sets_name = mk_name()
        elem_name = mk_name()
        seq = LocalRef(seq_name)
        sets = LocalRef(sets_name)
        elem = LocalRef(elem_name)
        elem_type = dom.type.type
        ty = Def1T(SetT(SeqT(elem_type)), SetT(SeqT(elem_type)), rest_args = [num_t])
        body = BinOp(BinOpId.Union,
            sets,
            Set2(
                InDef0(args = [([seq_name], sets), ([elem_name], dom)]),
                Def1App(Def1Ref('Append'), seq, elem)
                )
            )
        return (LocalRef(name), Def1(name, [sets_name, ix_name], body, ann = ty))

    def seq_seq_apa(self, set):
        name = mk_name()
        arg_name = mk_name()
        arg = LocalRef(arg_name)
        arg.type = set.type
        arg.kind = set.kind

        ref, decl = self.func_decl(arg)
        body = Let([decl], self.fold_set(ref))

        df = Def1(name, [arg_name], body)
        self.globals.append(df)

        expr = Def1App(Def1Ref(name), set)
        expr.type = InfSetT(SeqT(set.type.type))
        expr.kind = set.kind
        return expr

    def seq_seq(self, arg):
        self.add_extends_standard('Sequences')
        ref = Def1Ref('Seq')
        ty = InfSetT(SeqT(arg.type.type))
        ref.type = Def1T(arg.type, ty)
        r = Def1App(ref, arg)
        r.type = ty
        r.kind = arg.kind
        return r

    def case(self, hole):
        set = self.seq_seq(hole)
        elem = SeqT(hole.type.type).sample()
        expr = BinOp(BinOpId.In, elem, set)
        expr.kind = hole.kind
        expr.type = bool_t

        return self.testmodel_template(next = self.next_y(expr))

    def case_apalache(self, hole):
        set = self.seq_seq_apa(hole)
        elem = SeqT(hole.type.type).sample()
        expr = BinOp(BinOpId.In, elem, set)
        expr.kind = hole.kind
        expr.type = bool_t

        args, kw = self.testmodel_template(next = self.next_y(expr))
        return ApalacheModel(*args, **kw)

    def plug(self, type):
        ty = type.refine(InfSetT(SeqT(any_t)))
        if not ty:
            return SkipReason.TypeMismatch

        arg = SetT(ty.type.type).sample()
        return self.seq_seq(arg)

    def plug_apalache(self, type):
        ty = type.refine(InfSetT(SeqT(any_t)))
        if not ty:
            return SkipReason.TypeMismatch

        arg = SetT(ty.type.type).sample()
        return self.seq_seq_apa(arg)

class NumSetF(Feature):
    def __init__(self, is_nat):
        super().__init__()
        self.is_nat = is_nat

    def kind(self):
        return simple_kinds

    def type(self):
        return any_t

    def case(self, hole):
        return SkipReason.CanNotBeCase

    def plug(self, type):
        ty = type.refine(InfSetT(num_t))
        if not ty:
            return SkipReason.TypeMismatch

        self.add_extends_standard('Naturals' if self.is_nat else 'Integers')

        r = NumSet(self.is_nat)
        r.type = InfSetT(num_t)
        r.kind = Kind.Const
        return r

class StringSetF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return any_t

    def case(self, hole):
        return SkipReason.CanNotBeCase

    def plug(self, type):
        ty = type.refine(InfSetT(str_t))
        if not ty:
            return SkipReason.TypeMismatch

        r = StrSet()
        r.type = InfSetT(str_t)
        r.kind = Kind.Const
        return r

class BoolSetF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return any_t

    def case(self, hole):
        return SkipReason.CanNotBeCase

    def plug(self, type):
        ty = type.refine(SetT(bool_t))
        if not ty:
            return SkipReason.TypeMismatch

        r = BoolSet()
        r.type = SetT(bool_t)
        r.kind = Kind.Const
        return r

class SeqSelectSeqF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return UnionT(SeqT(any_t), TupleT(), TupleT(any_t), TupleT(any_t, any_t), Def1T(any_t, bool_t))

    def seq_select(self, seq, fltr):
        self.add_extends_standard('Sequences')
        ref = Def1Ref('SelectSeq')
        ref.type = Def1T(seq.type, seq.type, rest_args = [fltr.type])
        r = Def1App(ref, seq, fltr)
        r.type = seq.type
        r.kind = seq.kind
        return r

    def case(self, hole):
        if hole.type.match(Def1T(any_t, bool_t)):
            expr = self.seq_select(SeqT(hole.type.lhs).sample(), hole)
        else:
            if hole.type.match(SeqT(any_t)):
                elem_ty = hole.type.type
            elif hole.type.match(TupleT(any_t)) or hole.type.match(TupleT(any_t, any_t)):
                elem_ty = hole.type.types[0]
            elif hole.type.match(TupleT()):
                elem_ty = bool_t
            u = mk_name()
            ref = LocalRef(u)
            ref.type = elem_ty
            ref.kind = hole.kind
            lam = Lambda([u], any_to_bool(ref))
            lam.type = Def1T(elem_ty, bool_t)
            expr = self.seq_select(hole, lam)

        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        if not type.match(SeqT(any_t)):
            return SkipReason.TypeMismatch

        ty = type.refine(SeqT(any_t))
        seq = ty.sample()
        u = mk_name()
        ref = LocalRef(u)
        ref.type = seq.type.type
        ref.kind = Kind.Const
        lam = Lambda([u], any_to_bool(ref))
        lam.type = Def1T(seq.type.type, bool_t)
        return self.seq_select(seq, lam)

class SeqAppendF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return UnionT(SeqT(any_t), any_t)

    def seq_append(self, seq, elem):
        self.add_extends_standard('Sequences')
        ref = Def1Ref('Append')
        ref.type = Def1T(seq.type, seq.type, rest_args = [elem.type])
        r = Def1App(ref, seq, elem)
        r.type = ref.type.rhs
        r.kind = seq.kind
        return r

    def case(self, hole):
        if hole.type.match(SeqT(any_t)):
            expr = self.seq_append(hole, hole.type.type.sample())
        else:
            expr = self.seq_append(SeqT(hole.type).sample(), hole)
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        ty = type.refine(SeqT(any_t))
        if not ty:
            return SkipReason.TypeMismatch

        seq = ty.sample()
        elem = seq.type.type.sample()
        return self.seq_append(seq, elem)

class SeqHeadF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return SeqT(any_t)

    def seq_head(self, seq):
        self.add_extends_standard('Sequences')
        ref = Def1Ref('Head')
        ref.type = Def1T(seq.type, seq.type.type)
        r = Def1App(ref, seq)
        r.type = ref.type.rhs
        r.kind = seq.kind
        return r

    def case(self, hole):
        expr = self.seq_head(hole)
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        if not type.match(any_t):
            return SkipReason.TypeMismatch

        seq = SeqT(type).sample()
        return self.seq_head(seq)

class SeqTailF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return SeqT(any_t)

    def seq_tail(self, seq):
        self.add_extends_standard('Sequences')
        ref = Def1Ref('Tail')
        ref.type = Def1T(seq.type, seq.type)
        r = Def1App(ref, seq)
        r.type = ref.type.rhs
        r.kind = seq.kind
        return r

    def case(self, hole):
        expr = self.seq_tail(hole)
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        ty = type.refine(SeqT(any_t))
        if not ty:
            return SkipReason.TypeMismatch

        seq = ty.sample()
        return self.seq_tail(seq)

class SeqSubSeqF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return UnionT(SeqT(any_t), TupleT(), TupleT(any_t), TupleT(any_t, any_t), num_t)

    def seq_subseq(self, seq, n):
        self.add_extends_standard('Sequences')
        ref = Def1Ref('SubSeq')
        ref.type = Def1T(seq.type, seq.type, rest_args = [num_t, num_t])
        r = Def1App(ref, seq, n, Num(1))
        r.type = seq.type
        r.kind = seq.kind
        return r

    def case(self, hole):
        if hole.type.match(num_t):
            expr = self.seq_subseq(SeqT(any_t).sample(), hole)
        else:
            expr = self.seq_subseq(hole, num_t.sample())

        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        if not type.match(SeqT(any_t)):
            return SkipReason.TypeMismatch

        ty = type.refine(SeqT(any_t))
        seq = ty.sample()
        return self.seq_subseq(seq, num_t.sample())

def NumRangeSet(name):
    return UninterpretedDef(r'''
%s(n, m) ==
    IF m > n + 3
    THEN CHOOSE w \in {1} : w > 1 \* Reject such input
    ELSE { w \in { n, n + 1, n + 2, n + 3 } : w <= m }
''' % name)

class RangeF(Feature):
    def can_be_reduced(self):
        return True

    def reduction_strategy(self):
        return "n..m is replaced with  { x \in { n, n + 1, ... } : x <= m }; it falls back to crash (through CHOOSE Q : FALSE) if m is too big: this crash forces to do manual test review"

    def kind(self):
        return simple_kinds

    def type(self):
        return num_t

    def range(self, n):
        self.add_extends_standard('Naturals')
        r = Range(Num(0), n)
        r.type = SetT(n.type)
        r.kind = n.kind
        return r

    def range_replace(self, n):
        self.add_extends_standard('Naturals')
        name = mk_name()
        def1 = NumRangeSet(name)
        self.globals.append(def1)
        ref = Def1Ref(name)
        ref.type = Def1T(num_t, SetT(num_t), rest_args = [num_t])
        r = Def1App(ref, Num(0), n)
        r.type = SetT(num_t)
        r.kind = n.kind
        return r

    def case(self, hole):
        expr = self.range(hole)
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def case_tlc_reduced(self, hole):
        expr = self.range_replace(hole)
        args, kw = self.testmodel_template(next = self.next_y(any_to_bool(expr)))
        return TlcModel(*args, **kw)

    def plug(self, type):
        if not type.match(SetT(num_t)):
            return SkipReason.TypeMismatch

        return self.range(num_t.sample())

    def plug_tlc_reduced(self, type):
        if not type.match(SetT(num_t)):
            return SkipReason.TypeMismatch

        return self.range_replace(num_t.sample())

class TlcSingletonFunF(Feature):
    def can_be_reduced(self):
        return True

    def reduction_strategy(self):
        return r"x :> y is replaced with equivalent [u \in {x} |-> y]"

    def kind(self):
        return simple_kinds

    def type(self):
        return any_t

    def fun(self, type, v):
        self.add_extends_standard('TLC')
        ty = type.refine(FunT(any_t, v.type))
        assert ty
        lhs = ty.lhs.sample()
        r = BinOp(BinOpId.TlcSingletonFun, lhs, v)
        r.type = FunT(lhs.type, v.type)
        r.kind = v.kind
        return r

    def fun_replace(self, type, v):
        ty0 = type.refine(FunT(any_t, v.type))
        assert ty0
        lhs = ty0.lhs.sample()

        name = mk_name()
        loc_arg = mk_name()
        indef = InDef0([loc_arg], Set0(lhs))
        ty = FunT(lhs.type, v.type)
        r = Fun(indef, v)
        r.type = ty
        r.kind = v.kind
        return r

    def case(self, hole):
        expr = self.fun(FunT(any_t, hole.type), hole)
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def case_tlc_reduced(self, hole):
        expr = self.fun_replace(FunT(any_t, hole.type), hole)
        args, kw = self.testmodel_template(next = self.next_y(any_to_bool(expr)))
        return TlcModel(*args, **kw)

    def plug(self, type):
        ty0 = type.refine(FunT(any_t, any_t))
        if not ty0:
            return SkipReason.TypeMismatch
        rhs = ty0.rhs.sample()
        ty = FunT(ty0.lhs, rhs.type)

        return self.fun(ty, rhs)

    def plug_tlc_reduced(self, type):
        ty0 = type.refine(FunT(any_t, any_t))
        if not ty0:
            return SkipReason.TypeMismatch
        rhs = ty0.rhs.sample()
        ty = FunT(ty0.lhs, rhs.type)

        return self.fun_replace(ty, rhs)

def TlcExtendOp(name):
    return UninterpretedDef(r'''
%s(f, g) ==
    LET
        DomF == DOMAIN f
        DomG == DOMAIN g
    IN [u \in DomF \union DomG |-> IF u \in DomF THEN f[u] ELSE g[u]]
''' % name)

class TlcExtendFunF(Feature):
    def can_be_reduced(self):
        return True

    def reduction_strategy(self):
        return r"f @@ g is replaced with equivalent: LET DomF == DOMAIN f IN [u \in DomF \union DOMAIN g |-> IF u \in DomF THEN f[u] ELSE g[x]]"

    def kind(self):
        return simple_kinds

    def type(self):
        return FunT(any_t, any_t)

    def extend(self, f):
        self.add_extends_standard('TLC')
        g = f.type.sample()
        r = BinOp(BinOpId.TlcExtendFun, f, g)
        r.type = f.type
        r.kind = f.kind
        return r

    def extend_replace(self, f):
        name = mk_name()
        def1 = TlcExtendOp(name)
        self.globals.append(def1)
        ref = Def1Ref(name)
        ref.type = Def1T(f.type, f.type, rest_args = [f.type])
        g = f.type.sample()
        r = Def1App(ref, f, g)
        r.type = f.type
        r.kind = f.kind
        return r

    def case(self, hole):
        expr = self.extend(hole)
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def case_tlc_reduced(self, hole):
        expr = self.extend_replace(hole)
        args, kw = self.testmodel_template(next = self.next_y(any_to_bool(expr)))
        return TlcModel(*args, **kw)

    def plug(self, type):
        ty0 = type.refine(FunT(any_t, any_t))
        if not ty0:
            return SkipReason.TypeMismatch
        f = ty0.sample()
        return self.extend(f)

    def plug_tlc_reduced(self, type):
        ty0 = type.refine(FunT(any_t, any_t))
        if not ty0:
            return SkipReason.TypeMismatch
        f = ty0.sample()
        return self.extend_replace(f)

def TlcPermute(name):
    return UninterpretedDef(r'''
%s(S) == { f \in [S -> S] : { f[u] : u \in S } = S }
''' % name)

class TlcPermuteFunF(Feature):
    def can_be_reduced(self):
        return True

    def reduction_strategy(self):
        return r"Permutations(S) is reduced to equivalent: { f \in [S -> S] : { f[u] : u \in S } = S }"

    def kind(self):
        return simple_kinds

    def type(self):
        return SetT(any_t)

    def permute(self, s):
        self.add_extends_standard('TLC')

        ref = Def1Ref('Permutations')
        ref.type = Def1T(s.type, SetT(FunT(s.type.type, s.type.type)))
        r = Def1App(ref, s)
        r.type = ref.type.rhs
        r.kind = s.kind
        return r

    def permute_replace(self, s):
        name = mk_name()
        def1 = TlcPermute(name)
        self.globals.append(def1)
        ref = Def1Ref(name)
        ref.type = Def1T(s.type, SetT(FunT(s.type.type, s.type.type)))
        r = Def1App(ref, s)
        r.type = ref.type.rhs
        r.kind = s.kind
        return r

    def case(self, hole):
        expr = self.permute(hole)
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def case_tlc_reduced(self, hole):
        expr = self.permute_replace(hole)
        args, kw = self.testmodel_template(next = self.next_y(any_to_bool(expr)))
        return TlcModel(*args, **kw)

    def plug(self, type):
        ty = type.refine(SetT(FunT(any_t, any_t)))
        if not ty:
            return SkipReason.TypeMismatch
        s = SetT(ty.type.lhs).sample()
        return self.permute(s)

    def plug_tlc_reduced(self, type):
        ty = type.refine(SetT(FunT(any_t, any_t)))
        if not ty:
            return SkipReason.TypeMismatch
        s = SetT(ty.type.lhs).sample()
        return self.permute_replace(s)

def TlcSortSeq(name):
    return UninterpretedDef(r'''
%s(s, Op(_, _)) ==
    LET
        dom == 1..Len(s)
        opts == { f \in [dom -> dom] : { f[u] : u \in dom } = dom /\ \A i, j \in dom : i >= j \/ Op(s[f[i]], s[f[j]]) }
    IN
        IF s = <<>>
        THEN <<>>
        ELSE
            LET
                g == CHOOSE o \in opts : TRUE
            IN
                [w \in dom |-> s[g[w]]]
''' % name)

class TlcSortSeqF(Feature):
    def can_be_reduced(self):
        return True

    def reduction_strategy(self):
        return r"SortSeq(S) is reduced to equivalent sort implementation"

    def kind(self):
        return simple_kinds

    def type(self):
        return SeqT(any_t)

    def op(self, type):
        n = mk_name()
        ref = Def1Ref(n)
        ref.type = Def1T(type, bool_t, rest_args = [type])
        ref.kind = Kind.Const

        u = 'u'
        v = 'v'

        if type.match(num_t):
            self.add_extends_standard('Naturals')
            expr = BinOp(BinOpId.Le, LocalRef(u), LocalRef(v))
        elif type.match(bool_t):
            expr = IfThenElse(BinOp(BinOpId.And, Not(LocalRef(u)), LocalRef(v)), Bool(False), Bool(True))
        elif type.match(str_t):
            self.add_extends_standard('Sequences', 'Naturals')
            expr = BinOp(BinOpId.Le, Def1App(Def1Ref('Len'), LocalRef(u)), Def1App(Def1Ref('Len'), LocalRef(v)))
        else:
            assert False, f"Not supported: {type.apalache()}"

        self.globals.append(Def1(n, [u, v], expr))

        return ref

    def sort(self, s):
        self.add_extends_standard('TLC')
        ref = Def1Ref('SortSeq')
        ref.type = Def1T(s.type, s.type, rest_args = [Def1T(s.type.type, bool_t, rest_args = [s.type.type])])
        r = Def1App(ref, s, self.op(s.type.type))
        r.type = ref.type.rhs
        r.kind = s.kind
        return r

    def sort_replace(self, s):
        name = mk_name()
        def1 = TlcSortSeq(name)
        self.globals.append(def1)
        ref = Def1Ref(name)
        ref.type = Def1T(s.type, s.type, rest_args = [Def1T(s.type.type, bool_t, rest_args = [s.type.type])])
        r = Def1App(ref, s, self.op(s.type.type))
        r.type = ref.type.rhs
        r.kind = s.kind
        return r

    def case(self, hole):
        expr = self.sort(hole)
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def case_tlc_reduced(self, hole):
        expr = self.sort_replace(hole)
        args, kw = self.testmodel_template(next = self.next_y(any_to_bool(expr)))
        return TlcModel(*args, **kw)

    def plug(self, type):
        ty = type.refine(SeqT(any_t))
        if not ty:
            return SkipReason.TypeMismatch
        s = ty.sample()
        return self.sort(s)

    def plug_tlc_reduced(self, type):
        ty = type.refine(SeqT(any_t))
        if not ty:
            return SkipReason.TypeMismatch
        s = ty.sample()
        return self.sort_replace(s)

class TlcEvalF(Feature):
    def can_be_reduced(self):
        return True

    def reduction_strategy(self):
        return r"TLCEval(expr) is reduced to just expr"

    def kind(self):
        return simple_kinds

    def type(self):
        return any_t

    def teval(self, expr):
        self.add_extends_standard('TLC')
        ref = Def1Ref('TLCEval')
        ref.type = Def1T(expr.type, expr.type)
        r = Def1App(ref, expr)
        r.type = ref.type.rhs
        r.kind = expr.kind
        return r

    def teval_reduced(self, expr):
        return expr

    def case(self, hole):
        expr = self.teval(hole)
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def case_tlc_reduced(self, hole):
        expr = self.teval_reduced(hole)
        args, kw = self.testmodel_template(next = self.next_y(any_to_bool(expr)))
        return TlcModel(*args, **kw)

    def plug(self, type):
        if not type.match(any_t):
            return SkipReason.TypeMismatch

        expr = type.sample()
        return self.teval(expr)

    def plug_tlc_reduced(self, type):
        if not type.match(any_t):
            return SkipReason.TypeMismatch

        expr = type.sample()
        return self.teval_reduced(expr)

class BagBagToSetF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return BagT(any_t)

    def bag_to_set(self, bag):
        self.add_extends_standard('Bags')
        ref = Def1Ref('BagToSet')
        ref.type = Def1T(bag.type, SetT(bag.type.type))
        r = Def1App(ref, bag)
        r.type = ref.type.rhs
        r.kind = bag.kind
        return r

    def case(self, hole):
        expr = self.bag_to_set(hole)
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        ty = type.refine(SetT(any_t))
        if not ty:
            return SkipReason.TypeMismatch
        bag = BagT(ty.type).sample()
        return self.bag_to_set(bag)

class BagSetToBagF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return SetT(any_t)

    def set_to_bag(self, set):
        self.add_extends_standard('Bags')
        ref = Def1Ref('SetToBag')
        ref.type = Def1T(set.type, BagT(set.type.type))
        r = Def1App(ref, set)
        r.type = ref.type.rhs
        r.kind = set.kind
        return r

    def case(self, hole):
        expr = self.set_to_bag(hole)
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        ty = type.refine(BagT(any_t))
        if not ty:
            return SkipReason.TypeMismatch
        s = SetT(ty.type).sample()
        return self.set_to_bag(s)

class BagBagInF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return UnionT(BagT(any_t), any_t)

    def bag_in(self, elem, bag):
        self.add_extends_standard('Bags')
        ref = Def1Ref('BagIn')
        ref.type = Def1T(elem.type, bool_t, rest_args = [bag.type])
        r = Def1App(ref, elem, bag)
        r.type = bool_t
        r.kind = bag.kind
        return r

    def case(self, hole):
        ty = hole.type.match(BagT(any_t))
        if ty:
            lhs = hole.type.type.sample()
            rhs = hole
        else:
            lhs = hole
            rhs = BagT(hole.type).sample()
        expr = self.bag_in(lhs, rhs)
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        if not type.match(bool_t):
            return SkipReason.TypeMismatch

        lhs = any_t.sample()
        rhs = BagT(lhs.type).sample()
        return self.bag_in(lhs, rhs)

class BagEmptyBagF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return any_t

    def empty_bag(self, ty):
        assert isinstance(ty, BagT)
        self.add_extends_standard('Bags')
        r = Def0Ref('EmptyBag')
        r.type = ty
        r.kind = Kind.Const
        return r

    def case(self, hole):
        return SkipReason.CanNotBeCase

    def plug_tlc(self, type):
        ty0 = type.refine(BagT(any_t))
        if not ty0:
            return SkipReason.TypeMismatch
        ty = ty0.sample().type
        return self.empty_bag(ty)

    def plug_apalache(self, type):
        r = self.plug_tlc(type)
        if isinstance(r, SkipReason):
            return r
        # Apalache is not always able to type check inlined let definitions,
        # so it is made global
        return self.def_expr(r)

class BagBagBinOpF(Feature):
    def __init__(self, op):
        super().__init__()
        assert op in [BinOpId.BagAdd, BinOpId.BagSub]
        self.op = op

    def kind(self):
        return simple_kinds

    def type(self):
        return BagT(any_t)

    def bag_op(self, bag):
        self.add_extends_standard('Bags')
        r = BinOp(self.op, bag, bag.type.sample())
        r.type = bag.type
        r.kind = bag.kind
        return r

    def case(self, hole):
        expr = self.bag_op(hole)
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        ty = type.refine(BagT(any_t))
        if not ty:
            return SkipReason.TypeMismatch

        bag = ty.sample()
        return self.bag_op(bag)

class BagBagSubsetEqF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return BagT(any_t)

    def bag_op(self, bag):
        self.add_extends_standard('Bags')
        r = BinOp(BinOpId.BagSubsetEq, bag, bag.type.sample())
        r.type = bool_t
        r.kind = bag.kind
        return r

    def case(self, hole):
        expr = self.bag_op(hole)
        return self.testmodel_template(next = self.next_y(expr))

    def plug(self, type):
        if not type.match(bool_t):
            return SkipReason.TypeMismatch

        bag = BagT(any_t).sample()
        return self.bag_op(bag)

class BagBagUnionF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return SetT(BagT(any_t))

    def bag_union(self, set):
        assert set.type.match(SetT(BagT(any_t)))
        self.add_extends_standard('Bags')
        ref = Def1Ref('BagUnion')
        ref.type = Def1T(set.type, set.type.type)
        r = Def1App(ref, set)
        r.type = ref.type.rhs
        r.kind = set.kind
        return r

    def case(self, hole):
        expr = self.bag_union(hole)
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        ty = type.refine(BagT(any_t))
        if not ty:
            return SkipReason.TypeMismatch
        s = SetT(ty).sample()
        return self.bag_union(s)

class BagBagCardinalityF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return BagT(any_t)

    def bag_cardinality(self, bag):
        assert bag.type.match(BagT(any_t))
        self.add_extends_standard('Bags')
        ref = Def1Ref('BagCardinality')
        ref.type = Def1T(bag.type, num_t)
        r = Def1App(ref, bag)
        r.type = ref.type.rhs
        r.kind = bag.kind
        return r

    def case(self, hole):
        expr = self.bag_cardinality(hole)
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        if not type.match(num_t):
            return SkipReason.TypeMismatch
        s = BagT(any_t).sample()
        return self.bag_cardinality(s)

class BagCopiesInF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return UnionT(BagT(any_t), any_t)

    def bag_copies_in(self, elem, bag):
        assert elem.type == bag.type.type, f'{elem.type.apalache()} != {bag.type.type.apalache()}'
        self.add_extends_standard('Bags')
        ref = Def1Ref('CopiesIn')
        ref.type = Def1T(elem.type, num_t, rest_args = [bag.type])
        r = Def1App(ref, elem, bag)
        r.type = ref.type.rhs
        r.kind = most_generic(elem.kind, bag.kind)
        return r

    def case(self, hole):
        if hole.type.match(BagT(any_t)):
            lhs = hole.type.type.sample()
            rhs = hole
        else:
            lhs = hole
            rhs = BagT(hole.type).sample()
        expr = self.bag_copies_in(lhs, rhs)
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        if not type.match(num_t):
            return SkipReason.TypeMismatch
        bag = BagT(any_t).sample()
        elem = bag.type.type.sample()
        return self.bag_copies_in(elem, bag)

class BagBagOfAllF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return BagT(any_t)

    def op(self, type):
        n = mk_name()
        ref = Def1Ref(n)
        ref.type = Def1T(type, type)
        ref.kind = Kind.Const

        u = 'u'

        if type.match(num_t):
            self.add_extends_standard('Naturals')
            expr = BinOp(BinOpId.Add, LocalRef(u), Num(1))
        elif type.match(bool_t):
            expr = Not(LocalRef(u))
        else:
            expr = LocalRef(u)

        self.globals.append(Def1(n, [u], expr))

        return ref

    def bag_of_all(self, bag):
        self.add_extends_standard('Bags')
        ref = Def1Ref('BagOfAll')
        ref.type = Def1T(Def1T(bag.type, bag.type), bag.type, rest_args = [bag.type])
        r = Def1App(ref, self.op(bag.type), bag)
        r.type = ref.type.rhs
        r.kind = bag.kind
        return r

    def case(self, hole):
        expr = self.bag_of_all(hole)
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        ty = type.refine(BagT(any_t))
        if not ty:
            return SkipReason.TypeMismatch
        bag = ty.sample()
        return self.bag_of_all(bag)

def BagSubBagR(name):
    return UninterpretedDef(r'''
%s_BagToSeq(B) ==
    LET
        Dom == { u \in DOMAIN B : B[u] > 0 }
        Range(f) == { f[q] : q \in DOMAIN f }
        F[n \in 0..Cardinality(Dom)] ==
            IF n = 0
            THEN <<>>
            ELSE
                Append(F[n - 1], CHOOSE w \in (Dom \ Range(F[n - 1])) : TRUE)
    IN
        F[Cardinality(Dom)]

%s(B) ==
    LET seq == %s_BagToSeq(B)
        F[e \in 0..Len(seq)] ==
            IF e = 0
            THEN {<<>>}
            ELSE
                LET
                    elem == seq[e]
                    n == B[elem]
                IN
                    F[e - 1] \union { f @@ (elem :> cnt) : f \in F[e - 1], cnt \in 1..n }
    IN F[Len(seq)]
''' % (name, name, name))

class BagSubBagF(Feature):
    def can_be_reduced(self):
        return True

    def reduction_strategy(self):
        return r"SubBag(B) is reduced to equivalent SubBagR implementation"

    def kind(self):
        return simple_kinds

    def type(self):
        return BagT(any_t)

    def sub_bag(self, bag):
        assert bag.type.match(BagT(any_t))
        self.add_extends_standard('Bags')
        ref = Def1Ref('SubBag')
        ref.type = Def1T(bag.type, SetT(bag.type))
        r = Def1App(ref, bag)
        r.type = ref.type.rhs
        r.kind = bag.kind
        return r

    def sub_bag_replace(self, bag):
        assert bag.type.match(BagT(any_t))
        self.add_extends_standard('Bags', 'TLC', 'Sequences', 'Naturals', 'FiniteSets')

        name = mk_name()
        def1 = BagSubBagR(name)
        self.globals.append(def1)

        ref = Def1Ref(name)
        ref.type = Def1T(bag.type, SetT(bag.type))
        r = Def1App(ref, bag)
        r.type = ref.type.rhs
        r.kind = bag.kind
        return r

    def case(self, hole):
        expr = self.sub_bag(hole)
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def case_tlc_reduced(self, hole):
        expr = self.sub_bag_replace(hole)
        args, kw = self.testmodel_template(next = self.next_y(any_to_bool(expr)))
        return TlcModel(*args, **kw)

    def plug(self, type):
        ty = type.refine(SetT(BagT(any_t)))
        if not ty:
            return SkipReason.TypeMismatch
        s = ty.type.sample()
        return self.sub_bag(s)

    def plug_tlc_reduced(self, type):
        ty = type.refine(SetT(BagT(any_t)))
        if not ty:
            return SkipReason.TypeMismatch
        s = ty.type.sample()
        return self.sub_bag_replace(s)

class FiniteSetsIsFiniteSetF(Feature):
    def can_be_reduced(self):
        return True

    def reduction_strategy(self):
        return r"IsFiniteSet(B) is reduced to either TRUE or FALSE, depending on type information (finite and infinite sets have different types)"

    def kind(self):
        return simple_kinds

    def type(self):
        return UnionT(SetT(any_t), InfSetT(any_t))

    def is_finite(self, s):
        self.add_extends_standard('FiniteSets')
        ref = Def1Ref('IsFiniteSet')
        ref.type = Def1T(s.type, bool_t)
        r = Def1App(ref, s)
        r.type = bool_t
        r.kind = s.kind
        return r

    def case(self, hole):
        expr = self.is_finite(hole)
        return self.testmodel_template(next = self.next_y(expr))

    def case_tlc_reduced(self, hole):
        is_inf = hole.type.match(InfSetT(any_t))
        expr = Bool(not is_inf)
        expr.type = bool_t
        expr.kind = Kind.Const
        args, kw = self.testmodel_template(next = self.next_y(expr))
        return TlcModel(*args, **kw)

    def plug(self, type):
        if not type.match(bool_t):
            return SkipReason.TypeMismatch
        expr = SetT(any_t).sample()
        return self.is_finite(expr)

    def plug_tlc_reduced(self, type):
        if not type.match(bool_t):
            return SkipReason.TypeMismatch
        expr = Bool(True)
        expr.type = bool_t
        expr.kind = Kind.Const
        return expr

class FiniteSetsCardinalityF(Feature):
    def kind(self):
        return simple_kinds

    def type(self):
        return SetT(any_t)

    def cardinality(self, s):
        self.add_extends_standard('FiniteSets')
        ref = Def1Ref('Cardinality')
        ref.type = Def1T(s.type, num_t)
        r = Def1App(ref, s)
        r.type = ref.type.rhs
        r.kind = s.kind
        return r

    def case(self, hole):
        expr = self.cardinality(hole)
        return self.testmodel_template(next = self.next_y(any_to_bool(expr)))

    def plug(self, type):
        if not type.match(num_t):
            return SkipReason.TypeMismatch
        expr = SetT(any_t).sample()
        return self.cardinality(expr)

# TODO: Consider feature removal: that's not an appropriate way to test SYMMETRY
class SymmetryF(Feature):
    def can_be_reduced(self):
        return True

    def reduction_strategy(self):
        return r"Model with SYMMETRY(S) is reduced to the same model without SYMMETRY (they are equivalent if safety manual is followed)"

    def kind(self):
        return [Kind.Const]

    def type(self):
        return SetT(any_t)

    def permute(self, s):
        assert isinstance(s.type, SetT)
        assert s.kind == Kind.Const

        self.add_extends_standard('TLC')
        ref = Def1Ref('Permutations')
        ref.type = Def1T(s.type, SetT(FunT(s.type.type, s.type.type)))
        df = Def1App(ref, s)
        df.type = ref.type.rhs
        df.kind = s.kind
        r = self.def_expr(df)
        r.type = ref.type.rhs
        r.kind = s.kind
        return r.id

    def case_template(self, hole):
        loc = mk_name()
        indef = InDef0([loc], hole)
        return ForAll(indef, BinOp(BinOpId.In, LocalRef(loc), hole))

    def case(self, hole):
        expr = self.case_template(hole)
        return self.testmodel_template(next = self.next_y(expr), symmetry = self.permute(hole))

    def case_tlc_reduced(self, hole):
        expr = self.case_template(hole)
        args, kw = self.testmodel_template(next = self.next_y(expr))
        return TlcModel(*args, **kw)

    def plug(self, type):
        return SkipReason.CanNotBePlug

def combine_tlc(f1, f2):
    reset_name()
    r = f2.plug_tlc_ext(f1.kind(), f1.type())
    if isinstance(r, SkipReason):
        return r
    tc = f1.case_tlc_ext(
        r,
        extends = f2.extends,
        constants = f2.constants,
        variables = f2.variables,
        globals = f2.globals,
        modules = f2.modules)
    return tc

def combine_tlc_reduced(f1, f2):
    reset_name()
    r = f2.plug_tlc_reduced_ext(f1.kind(), f1.type())
    if isinstance(r, SkipReason):
        return r
    tc = f1.case_tlc_reduced_ext(
        r,
        extends = f2.extends,
        constants = f2.constants,
        variables = f2.variables,
        globals = f2.globals,
        modules = f2.modules)
    return tc

def combine_apalache(f1, f2):
    reset_name()
    r = f2.plug_apalache_ext(f1.kind(), f1.type())
    if isinstance(r, SkipReason):
        return r
    tc = f1.case_apalache_ext(
        r,
        extends = f2.extends,
        constants = f2.constants,
        variables = f2.variables,
        globals = f2.globals,
        modules = f2.modules)
    return tc

def combine_single(f1, f2):
    desc = {
        'case_feature' : f1.name,
        'plug_feature' : f2.name,
        'check_deadlock' : get_check_deadlock()
    }

    if is_model_value(f2.feature) and not f1.feature.model_value_allowed():
        return SkipCase(desc = desc, reason = SkipReason.ModelValueCanNotBeUsed)

    reducible = f1.feature.can_be_reduced() or f2.feature.can_be_reduced()

    tlc = combine_tlc(f1.feature, f2.feature)
    if reducible:
        ref = combine_tlc_reduced(f1.feature, f2.feature)
        reduction_strategy = {}
        if f1.feature.can_be_reduced():
            reduction_strategy['feature_case'] = f1.feature.reduction_strategy()
        if f2.feature.can_be_reduced():
            reduction_strategy['feature_plug'] = f2.feature.reduction_strategy()
        desc['reduction_strategy'] = reduction_strategy
        assert len(desc['reduction_strategy']) > 0
        case = RefTlcCase
    else:
        ref = combine_apalache(f1.feature, f2.feature)
        case = RefApalacheCase

    r_tlc = isinstance(tlc, SkipReason)
    r_ref = isinstance(ref, SkipReason)

    assert (r_tlc == r_ref)

    if r_tlc:
        return SkipCase(desc = desc, reason = tlc)

    return case(tlc, ref, desc)

def combine(f1, f2):
    cases = []

    # CHECK_DEADLOCK TRUE
    set_check_deadlock(True)
    case = combine_single(f1, f2)
    cases.append(case)

    # CHECK_DEADLOCK FALSE
    set_check_deadlock(False)
    case = combine_single(f1, f2)
    cases.append(case)

    # Debug output
    if all(isinstance(i, SkipCase) for i in cases):
        r = 'SKIPPED'
    elif any(isinstance(i, SkipCase) for i in cases):
        r = 'MIXED'
    else:
        r = 'OK'
    logging.debug(f'Combining {f1.name} and {f2.name}: {r}')

    return cases
