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

from .ast import *
from .common import *
from .kind import Kind, most_generic

def within_parens(t):
    ty = t.apalache()
    if isinstance(t, FunT) or isinstance(t, BagT) or isinstance(t, Def1T):
        ty = f'({ty})'
    return ty

class TypeT:
    # Is the type is a regular expression type?
    def regular(self):
        return True

    # Derive type which is both subtype of self and t
    def refine(self, t):
        return True

    # Override default equality operator
    def __eq__(self, other):
            return (isinstance(other, self.__class__) and self.__dict__ == other.__dict__)

class UnionT(TypeT):
    def __init__(self, *ts):
        super().__init__()
        self.types = ts

    def regular(self):
        assert "undefined"

    def match(self, t):
        return any(ty.match(t) for ty in self.types)

    def refine(self, t):
        refines = [ty.refine(t) for ty in self.types if ty.match(t)]
        if not refines:
            return None
        return refines[0]
        # return UnionT(*refines) if len(refines) > 1 else refines[0]

    def sample(self):
        assert self.types
        return self.types[0].sample()

class AnyT(TypeT):
    def match(self, t):
        if not t.regular():
            return False
        return True

    def refine(self, t):
        if not self.match(t):
            return None
        return t

    def sample(self):
        # Generate strings to minimize Apalache/TLC discrepancy due to model value interpretation
        # It doesn't matter for TLC, but a big deal for Apalache
        r = Str("S")
        r.type = str_t
        r.kind = Kind.Const
        return r

class BoolT(TypeT):
    def match(self, t):
        return isinstance(t, AnyT) or isinstance(t, BoolT)

    def refine(self, t):
        if not self.match(t):
            return None
        return self

    def sample(self):
        r = Bool(True)
        r.type = bool_t
        r.kind = Kind.Const
        return r

    def apalache(self):
        return "Bool"

class NumT(TypeT):
    def match(self, t):
        return isinstance(t, AnyT) or isinstance(t, NumT)

    def refine(self, t):
        if not self.match(t):
            return None
        return self

    def sample(self):
        r = Num(1)
        r.type = num_t
        r.kind = Kind.Const
        return r

    def apalache(self):
        return "Int"

class StrT(TypeT):
    def match(self, t):
        return isinstance(t, AnyT) or isinstance(t, StrT)

    def refine(self, t):
        if not self.match(t):
            return None
        return self

    def sample(self):
        r = Str("Z")
        r.type = str_t
        r.kind = Kind.Const
        return r

    def apalache(self):
        return "Str"

class Def1T(TypeT):
    def __init__(self, lhs, rhs, rest_args = []):
        super().__init__()
        assert isinstance(lhs, TypeT)
        assert isinstance(rhs, TypeT)
        self.lhs = lhs if len(rest_args) == 0 else None
        self.rhs = rhs
        self.args = [lhs] + rest_args

    def regular(self):
        return False

    def match(self, t):
        if isinstance(t, AnyT):
            return True
        if isinstance(t, Def1T):
            assert self.lhs
            return self.lhs.match(t.lhs) and self.rhs.match(t.rhs)
        return False

    def refine(self, t):
        if isinstance(t, AnyT):
            return self
        if isinstance(t, Def1T):
            assert self.lhs, f'{self.apalache()}'
            lhs = self.lhs.refine(t.lhs)
            rhs = self.rhs.refine(t.rhs)
            if not lhs or not rhs:
                return None
            return Def1T(lhs, rhs)
        return None

    def sample(self):
        raise "Not implemented"

    def apalache(self):
        args = f'({commas([ty.apalache() for ty in self.args])})'
        return f'{args} => {within_parens(self.rhs)}'

class FunT(TypeT):
    def __init__(self, lhs, rhs):
        super().__init__()
        assert isinstance(lhs, TypeT)
        assert isinstance(rhs, TypeT)
        self.lhs = lhs
        self.rhs = rhs

    def match(self, t):
        if isinstance(t, AnyT):
            return True
        if isinstance(t, FunT):
            return self.lhs.match(t.lhs) and self.rhs.match(t.rhs)
        return False

    def refine(self, t):
        if isinstance(t, AnyT):
            return self
        if isinstance(t, FunT):
            lhs = self.lhs.refine(t.lhs)
            rhs = self.rhs.refine(t.rhs)
            if not lhs or not rhs:
                return None
            return FunT(lhs, rhs)
        return None

    def sample(self):
        lhs = SetT(self.lhs).sample()
        rhs = self.rhs.sample()
        r = Fun(InDef0([mk_name()], lhs), rhs)
        r.type = FunT(lhs.type.type, rhs.type)
        r.kind = most_generic(lhs.kind, rhs.kind)
        return r

    def apalache(self):
        return f'{within_parens(self.lhs)} -> {within_parens(self.rhs)}'

class RecordT(TypeT):
    def __init__(self, fields):
        super().__init__()
        self.fields = fields

    def match(self, t):
        if isinstance(t, AnyT):
            return True
        if isinstance(t, RecordT):
            if t.fields.keys() != self.fields.keys():
                return False

            for fn, ft in self.fields.items():
                if not ft.match(t.fields[fn]):
                    return False
            return True
        return False

    def refine(self, t):
        if isinstance(t, AnyT):
            return self
        if isinstance(t, RecordT) and self.fields.keys() == t.fields.keys():
            fields = {}
            for k,v in self.fields.items():
                fields[k] = v.refine(t.fields[k])
                if fields[k] is None:
                    return None
            return RecordT(fields)
        return None

    def sample(self):
        new_types = {}
        new_values = {}

        for f,t in self.fields.items():
            new_values[f] = t.sample()
            new_types[f] = new_values[f].type

        rec_t = RecordT(new_types)
        rec = Record(new_values)
        rec.type = rec_t
        v = list(new_values.values())[0]
        rec.kind = v.kind

        assert self.match(rec.type)
        return rec

    def apalache(self):
        fields = [f'{f} : {t.apalache()}' for f,t in self.fields.items()]
        return f'[{commas(fields)}]'

class BagT(TypeT):
    def __init__(self, ty):
        super().__init__()
        assert isinstance(ty, TypeT)
        self.type = ty

    def match(self, t):
        if isinstance(t, AnyT):
            return True
        if isinstance(t, BagT):
            return self.type.match(t.type)
        return False

    def refine(self, t):
        if isinstance(t, AnyT):
            return self
        if isinstance(t, BagT):
            ty = self.type.refine(t.type)
            if not ty:
                return None
            return BagT(ty)
        return None

    def sample(self):
        dom = SetT(self.type).sample()
        r = Fun(InDef0([mk_name()], dom), Num(1))
        r.type = BagT(dom.type.type)
        r.kind = Kind.Const
        return r

    def apalache(self):
        return f'{within_parens(self.type)} -> {num_t.apalache()}'

class SetT(TypeT):
    def __init__(self, t):
        super().__init__()
        assert isinstance(t, TypeT)
        self.type = t

    def match(self, ty):
        if isinstance(ty, AnyT):
            return True
        if isinstance(ty, SetT):
            return self.type.match(ty.type)
        return False

    def refine(self, ty):
        if isinstance(ty, AnyT):
            return self
        if isinstance(ty, SetT):
            elem = self.type.refine(ty.type)
            return SetT(elem) if elem else None
        return None

    def sample(self):
        e = self.type.sample()
        r = Set0(e)
        r.type = SetT(e.type)
        r.kind = e.kind
        assert self.match(r.type)
        return r

    def apalache(self):
        return f'Set({self.type.apalache()})'

class InfSetT(TypeT):
    def __init__(self, t):
        super().__init__()
        assert isinstance(t, TypeT)
        self.type = t

    def regular(self):
        return False

    def match(self, ty):
        if isinstance(ty, AnyT):
            return False
        if isinstance(ty, InfSetT):
            return self.type.match(ty.type)
        return False

    def refine(self, ty):
        if isinstance(ty, InfSetT):
            elem = self.type.refine(ty.type)
            return InfSetT(elem) if elem else None
        return None

    def sample(self):
        assert False, "Not supported"

    def apalache(self):
        return f'Set({self.type.apalache()})'

class TupleT(TypeT):
    def __init__(self, *ts):
        super().__init__()
        for t in ts:
            assert t.regular()
        self.types = ts

    def match(self, ty):
        if isinstance(ty, AnyT):
            return True
        if isinstance(ty, TupleT) and len(self.types) == len(ty.types):
            for u,v in zip(self.types, ty.types):
                if not u.match(v):
                    return False
            return True
        return False

    def refine(self, ty):
        if isinstance(ty, AnyT):
            return self
        if isinstance(ty, TupleT) and len(ty.types) == len(self.types):
            elems = []
            for u, v in zip(self.types, ty.types):
                r = u.refine(v)
                if not r:
                    return None
                elems.append(r)
            return TupleT(*elems) if elems else None
        return None

    def sample(self):
        elems = [ty.sample() for ty in self.types]
        types = [s.type for s in elems]
        r = Tuple(*elems)
        r.type = TupleT(*types)
        r.kind = elems[0].kind if elems else Kind.Const
        return r

    def apalache(self):
        return f'<<{commas([ty.apalache() for ty in self.types])}>>'

class SeqT(TypeT):
    def __init__(self, t):
        super().__init__()
        self.type = t

    def match(self, ty):
        if isinstance(ty, AnyT):
            return True
        if isinstance(ty, SeqT):
            return self.type.match(ty.type)
        return False

    def refine(self, ty):
        if isinstance(ty, AnyT):
            return self
        if isinstance(ty, SeqT):
            return SeqT(self.type.refine(ty.type))
        return None

    def sample(self):
        elem = self.type.sample()
        r = Tuple(elem)
        r.type = SeqT(elem.type)
        r.kind = elem.kind
        return r

    def apalache(self):
        return f'Seq({self.type.apalache()})'

class InDefT(TypeT):
    def __init__(self, ty):
        super().__init__()
        self.type = ty

    def regular(self):
        return False

    def match(self, ty):
        if isinstance(ty, InDefT):
            return self.type.match(ty.type)
        return False

    def refine(self, ty):
        if not isinstance(ty, InDefT):
            return None
        inner = self.type.refine(ty.type)
        return InDefT(*inner) if inner else None

    # Extended version produces equivalent definition but
    # in a different syntactic form
    def sample(self, extended = False):
        if not isinstance(self.type, TupleT):
            e = SetT(self.type).sample()
            if extended:
                locs = [(['u_0'], e), (['u_1'], e)]
                r = InDef0(locs)
            else:
                locs = ['u_0', 'u_1']
                e = SetT(self.type).sample()
                r = InDef0(locs, e)
            r.type = InDefT(e.type.type)
            r.kind = e.kind
        else:
            locs = [f'u_{i}' for i in range(len(self.type.types))]
            e = SetT(self.type).sample()
            r = InDef1(locs, e)
            r.type = InDefT(e.type.type)
            r.kind = e.kind
        return r

    def apalache(self):
        assert "Not implemented"

any_t = AnyT()
bool_t = BoolT()
num_t = NumT()
str_t = StrT()
