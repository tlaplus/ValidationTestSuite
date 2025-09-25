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

from dataclasses import dataclass
import copy

from .ast import *
from .feature import *
from .testcase import *
from .symmetry import *
from .anomalous import anomalous_cases

@dataclass
class FeatureId:
    name: str
    desc: str
    feature: Feature

feature_ids = [
    ("OneLineComment", "\* one line comment", OneLineCommentF()),
    ("MultiLineComment", "(* multiline line comment *)", MultiLineCommentF()),
    ("BoolTrue", 'TRUE', BoolF(True)),
    ("BoolFalse", 'FALSE', BoolF(False)),
    ("BoolSet", 'BOOLEAN', BoolSetF()),
    ("And", "Non temporal /\\", AndF()),
    ("AndMultiLine", "Multiline /\\", AndMultiLineF()),
    ("Imply", "=>", ImplyF()),
    ("Not", "~", NotF()),
    ("Or", r"\/", OrF()),
    ("OrMultiLine", "Multiline /\\", OrMultiLineF()),
    ("AndProp", "Temporal /\\", AndPropF()),
    ("Boxed", "[][<expr>]_u", BoxedF()),
    ("Eq", "=", EqNeF(BinOpId.Eq)),
    ("Ne", "/=", EqNeF(BinOpId.Ne)),
    ("Let", "LET .. IN ..", LetF()),
    ("SetEmpty", "{}", SetEmptyF()),
    ("Set0", "{x, y, ..}", Set0F()),
    ("Set1", r"{x \in S : P(x)}", Set1F()),
    ("Set2", r"{P(x) : x \in S}", Set2F()),
    ("Set1InDef", "{ <in-def-decl> : P(x) }", Set1InDefF()),
    ("Set2InDef", "{ P(x) : <in-def-decl> }", Set2InDefF()),
    ("InDef0", r"x, y \in S", InDef0F(extended = False)),
    ("InDef1", r"x \in S, y \in S", InDef0F(extended = True)),
    ("InDef2", r"<<x, y>> \in S", InDef1F()),
    ("Fun", r"[x \in S |-> <expr>]", FunF()),
    ("FunInDef", "[<in-def-decl> |-> P]", FunInDefF()),
    ("In", r"\in", InF(BinOpId.In)),
    ("NotIn", r"\notin", InF(BinOpId.NotIn)),
    ("Exists", r"\E x \in S : <expr>", QuantorF(Exists)),
    ("Forall", r"\A x \in S : <expr>", QuantorF(ForAll)),
    ("ExistsInDef", r"\E <in-def-decl> : P", QuantorInDefF(Exists)),
    ("ForallInDef", r"\A <in-def-decl> : P", QuantorInDefF(ForAll)),
    ("Choose", "CHOOSE x \in S : <expr>", ChooseF()),
    ("ChooseInDef", "CHOOSE <in-def-decl> : P", ChooseInDefF()),
    ("Record", "[field0 |-> <expr>]", RecordF()),
    ("Tuple", "<<x, y>>", TupleF()),
    ("TupleEmpty", "<<>>", TupleEmptyF()),
    ("FunApp", "<fexpr>[arg]", FunAppF()),
    ("Except0", "[<fexpr> EXCEPT !<fexpr-kind> = arg]", Except0F()),
    ("Except1Fun", "[F EXCEPT ![arg] = <expr>]", Except1FunF(with_at = False)),
    ("Except1FunWithAt", "[F EXCEPT ![arg] = IF <expr> = @ THEN @ ELSE <expr>]", Except1FunF(with_at = True)),
    ("Except1Rec", "[F EXCEPT ![arg] = <expr>]", Except1RecF(with_at = False)),
    ("Except1RecWithAt", "[F EXCEPT ![arg] = <expr>]", Except1RecF(with_at = True)),
    ("Except2Fun", "[F EXCEPT ![<expr>] = FALSE]", Except2FunF()),
    ("Except2FunTuple", "[F EXCEPT ![<expr>, <expr>] = FALSE]", Except2FunTupleF()),
    ("Prime", "<expr>'", PrimeF()),
    ("NumZero", "0", IntF(0)),
    ("NumOne", "1", IntF(1)),
    ("NumMaxInt", "(2^31 - 1)", IntF(2**31 - 1)),
    ("NumUnaryMinus", "-u", NumUnaryMinusF()),
    ("NumPlus", "u + v", NumBinaryF(BinOpId.Plus, num_t)),
    ("NumMinus", "u - v", NumBinaryF(BinOpId.Minus, num_t)),
    ("NumMul", "u * v", NumBinaryF(BinOpId.Mul, num_t)),
    ("NumDiv", r"u \div v", NumBinaryF(BinOpId.Div, num_t)),
    ("NumMod", "u % v", NumBinaryF(BinOpId.Mod, num_t)),
    ("NumPow", "u ^ v", NumBinaryF(BinOpId.Pow, num_t)),
    ("NumGt", "u > v", NumBinaryF(BinOpId.Gt, bool_t)),
    ("NumGe", "u >= v", NumBinaryF(BinOpId.Ge, bool_t)),
    ("NumLt", "u < v", NumBinaryF(BinOpId.Lt, bool_t)),
    ("NumLe", "u <= v", NumBinaryF(BinOpId.Le, bool_t)),
    ("DefFun", r"F[x \in S] == <expr>", DefFunF(inlet = False)),
    ("LetDefFun", r"LET F[x \in S] == <expr> IN F", DefFunF(inlet = True)),
    ("DefFunRecursive", r"F[x \in BOOLEAN] == IF x THEN <expr> ELSE F[~x]", DefFunRecursiveF(inlet = False)),
    ("LetDefFunRecursive", r"LET F[x \in BOOLEAN] == IF x THEN <expr> ELSE F[~x]", DefFunRecursiveF(inlet = True)),
    ("DefFunInDef", r"F[x, y | <<x, y>> \in S] == <expr>", DefFunInDefF(inlet = False)),
    ("LetDefFunInDef", r"LET F[x, y | <<x, y>> \in S] == <expr>", DefFunInDefF(inlet = True)),
    ("Def0", "D0 == <expr>", Def0F(inlet = False)),
    ("LetDef0", "LET D0 == <expr> IN D0", Def0F(inlet = True)),
    ("Def1", "D1(x) == <expr>", Def1F(inlet = False)),
    ("LetDef1", "LET D1(x) == <expr> IN D1(<expr>)", Def1F(inlet = True)),
    ("Def2", "D1(x, E(_)) == <expr>", Def2F(inlet = False)),
    ("LetDef2", "LET D1(x, E(_)) == <expr>", Def2F(inlet = True)),
    ("Def1Recursive", "RECURSIVE DR(x) == IF x THEN <expr> ELSE D2(~x)", Def1RecursiveF(inlet = False)),
    ("LetDef1Recursive", "LET RECURSIVE DR(x) == IF x THEN <expr> ELSE D2(~x)", Def1RecursiveF(inlet = True)),
    ("Extends", "EXTENDS: use definition from extended module", ExtendsF(search_path = False)),
    ("ExtendsInDifferentFolder", "EXTENDS: use definition from extended module, located in different folder", ExtendsF(search_path = True)),
    ("Variable", "Introduce and use variable", VariableF(view_exclude = False)),
    ("VariableViewExclude", "Variable, which is excluded from TLC VIEW", VariableF(view_exclude = True)),
    ("Constant", "CONSTANT C0: substituted with definition", Constant0F(False)),
    ("ConstantModelValue", "CONSTANT C0: substituted with model value", Constant0F(True)),
    ("ConstantRank1", "CONSTANT C1(_)", Constant1F()),
    ("Instance", "INSTANCE <module>", InstanceF(with_stmt = False, named = False, search_path = False)),
    ("InstanceWith", "INSTANCE <module> WITH <bindings>", InstanceF(with_stmt = True, named = False, search_path = False)),
    ("InstanceNamed", "M == INSTANCE <module>InstanceF", InstanceF(with_stmt = False, named = True, search_path = False)),
    ("InstanceNamedWith", "M == INSTANCE <module> WITH <bindings>", InstanceF(with_stmt = True, named = True, search_path = False)),
    ("InstanceInFolder", "INSTANCE <module>", InstanceF(with_stmt = False, named = False, search_path = True)),
    ("InstanceWithInFolder", "INSTANCE <module> WITH <bindings>", InstanceF(with_stmt = True, named = False, search_path = True)),
    ("InstanceNamedInFolder", "M == INSTANCE <module>InstanceF", InstanceF(with_stmt = False, named = True, search_path = True)),
    ("InstanceNamedWithInFolder", "M == INSTANCE <module> WITH <bindings>", InstanceF(with_stmt = True, named = True, search_path = True)),
    ("Enabled", "ENABLED <expr>", EnabledF()),
    ("Assume", "ASSUME <expr>", AssumeF(named = False)),
    ("AssumeNamed", "ASSUME Name == <expr>", AssumeF(named = True)),
    ("Lambda", "LAMBDA x : <expr>", LambdaF()),
    ("Cross2", r"A \X B", Cross2F()),
    ("Cross3", r"A \X B \X C", Cross3F()),
    ("FunSet", "[A -> B]", FunSetF()),
    ("RecordSet", "[field : B]", RecordSetF()),
    ("SetDiff", r"A \ B", SetUnionInterceptDifferenceF(BinOpId.SetDiff)),
    ("SetUnion", r"A \union B", SetUnionInterceptDifferenceF(BinOpId.Union)),
    ("SetIntersect", r"A \intersect B", SetUnionInterceptDifferenceF(BinOpId.Intersect)),
    ("SubsetEq", r"A \subseteq B", SubsetEqF()),
    ("IfCond", r"IF <expr> THEN ... ELSE ...", IfF(IfCheck.If)),
    ("IfThen", r"IF ... THEN <expr> ELSE ...", IfF(IfCheck.Then)),
    ("IfElse", r"IF ... THEN ... ELSE <expr>", IfF(IfCheck.Else)),
    ("Subset", r"SUBSET A", SubsetF()),
    ("Domain", r"DOMAIN A", DomainF()),
    ("Union", r"UNION A", UnionF()),
    ("Unchanged", r"UNCHANGED A", UnchangedF()),
    ("Equivalence", "A <=> B", EquivF()),
    ("StringEmpty", 'Empty string ""', StrF('')),
    ("String", '"Q"', StrF('Q')),
    ("SeqLen", 'Len(<<...>>) | Len("abc")', SeqLenF()),
    ("SeqConcat", '<<..>> \o <<..>> | "ab" \o "bc")', SeqConcatF()),
    ("SeqSeq", 'Seq({..})', SeqSeqF()),
    ("NatSet", 'Nat', NumSetF(is_nat = True)),
    ("IntSet", 'Int', NumSetF(is_nat = False)),
    ("StringSet", 'STRING', StringSetF()),
    ("SeqSelectSeq", 'SelectSeq(<<..>>, T(_))', SeqSelectSeqF()),
    ("SeqSubSeq", 'SubSeq(<<..>>, n, m)', SeqSubSeqF()),
    ("NumRange", 'n .. m', RangeF()),
    ("TlcSingletonFun", 'x :> y', TlcSingletonFunF()),
    ("TlcExtendFun", 'f @@ g', TlcExtendFunF()),
    ("TlcPermuteFun", 'Permutations(S)', TlcPermuteFunF()),
    ("TlcSortSeq", 'SortSeq(<<...>>, Op)', TlcSortSeqF()),
    ("TlcEval", 'TLCEval(expr)', TlcEvalF()),
    ("BagBagToSet", 'BagToSet(expr)', BagBagToSetF()),
    ("BagSetToBag", 'SetToBag(S)', BagSetToBagF()),
    ("BagBagIn", 'BagIn(e, B)', BagBagInF()),
    ("BagEmptyBag", 'EmptyBag', BagEmptyBagF()),
    ("BagAddBag", 'B0 (+) B1', BagBagBinOpF(BinOpId.BagAdd)),
    ("BagBagSub", 'B0 (-) B1', BagBagBinOpF(BinOpId.BagSub)),
    ("BagCopiesIn", 'CopiesIn(e, B)', BagCopiesInF()),
    ("BagSubsetEqBag", r'B0 \sqsubseteq B1', BagBagSubsetEqF()),
    ("BagBagUnion", 'BagUnion(S)', BagBagUnionF()),
    ("BagBagCardinality", 'BagCardinality(B)', BagBagCardinalityF()),
    ("BagBagOfAll", 'BagOfAll(Op(_), B', BagBagOfAllF()),
    ("BagSubBag", 'SubBag(B)', BagSubBagF()),
    ("FiniteSetsIsFiniteSet", 'IsFiniteSet(S)', FiniteSetsIsFiniteSetF()),
    ("FiniteSetsCardinality", 'Cardinality(S)', FiniteSetsCardinalityF()),
    ("SeqHead", 'Head(S)', SeqHeadF()),
    ("SeqTail", 'Tail(S)', SeqTailF()),
    ("SeqAppend", 'Append(S, e)', SeqAppendF()),
]

# All ids in feature_ids must be unique
def consistency(fs):
    s = set(f.name for f in fs)
    assert(len(s) == len(fs))

# Get FeatureIds
def make_feature_list():
    fs = [FeatureId(*f) for f in feature_ids]
    consistency(fs)
    return fs

# Wrapper class to generate testcases for different option combinations
class OptionTestCase(TestCase):
    def __init__(self, inner, option):
        self.inner = inner
        self.inner.desc['reduction_strategy'] = {
            'configuration' : f'Replace `{option}` option with the `-workers 1`'
        }

        self.option = option

    def render(self, path : str) -> dict:
        new_path = os.path.join(path, self.option)
        return self.inner.render(new_path)

def prepare_testcases(feature_filter, symmetry, anomalous):
    features = make_feature_list()
    testcases = []

    # Pairwise feature combination
    for f1 in features:
        for f2 in features:
            if feature_filter(f1.name, f2.name):
                testcases.extend(combine(f1, f2))

    # SYMMETRY cases
    if symmetry:
        testcases.extend(symmetry_cases())

    # CMD options combinations
    # So far only `-workers` option varies
    cmd_options_ref = ['-workers', '1']
    workers_options = ['2']
    cmd_options_variants = [(f'-workers {opt}', ['-workers', opt]) for opt in workers_options]

    new_testcases = []

    # Add derived test cases for alternative cmd_options
    for testcase in testcases:
        if isinstance(testcase, SkipCase):
            new_testcases.append(testcase)
            continue

        # Keep options from the original tlc model
        ref_options = copy.deepcopy(testcase.tlc.cmd_options)

        orig_testcase = copy.deepcopy(testcase)
        orig_testcase.tlc.cmd_options = orig_testcase.tlc.cmd_options + cmd_options_ref
        if isinstance(orig_testcase, RefTlcCase):
            orig_testcase.ref.cmd_options = orig_testcase.ref.cmd_options + cmd_options_ref

        new_testcases.append(orig_testcase)

        constructor = TlcSymmetryCase if isinstance(testcase, TlcSymmetryCase) else RefTlcCase

        for desc, options in cmd_options_variants:
            tlc_variant = copy.deepcopy(orig_testcase.tlc)
            tlc_variant.cmd_options = ref_options + options
            new_tc = OptionTestCase(constructor(tlc_variant, orig_testcase.tlc, copy.deepcopy(orig_testcase.desc)), desc)
            new_testcases.append(new_tc)

    # Add test cases for anomalous conditions
    if anomalous:
        new_testcases.extend(anomalous_cases())

    return new_testcases

def render_testcases(cases, path):
    report = {}
    for case in cases:
        meta = case.render(path)
        assert not (meta['id'] in report)
        report[meta['id']] = meta
    return report

def render_spec(spec_dir, spec_file, feature_filter, symmetry, anomalous):
    cases = prepare_testcases(feature_filter, symmetry = symmetry, anomalous = anomalous)
    report = render_testcases(cases, spec_dir)
    with open(spec_file, 'w') as h:
        json.dump(report, h, indent = 2)
