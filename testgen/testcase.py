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

from dataclasses import dataclass
import typing
import os
import hashlib
import json
from .ast import *
from .common import *
from .type import *
from .testcasedefs import *

@unique
class SkipReason(Enum):
    TypeMismatch = auto()
    KindMismatch = auto()
    CanNotBeCase = auto()
    CanNotBePlug = auto()
    ModelValueCanNotBeUsed = auto()
    AssumeIsNotEmbeddable = auto()
    AlreadyCombined = auto()
    VariableExcludedFromView = auto()

def enum_str(self):
    return self.name

SkipReason.__str__ = enum_str

@dataclass
class ConstDesc:
    type: TypeT
    arity: int
    init: typing.Any

@dataclass
class VarDesc:
    type: TypeT
    init: typing.Any
    unchanged: bool

def append_list(stmts, *stmt):
    for s in stmt:
        if s is not None:
            stmts.append(s)

# Global per model check_deadlock flag

check_deadlock = None
def set_check_deadlock(v):
    global check_deadlock
    check_deadlock = v

def get_check_deadlock():
    global check_deadlock
    return check_deadlock

def init_name(module_name):
    return f'Init_{module_name}'

def init_ref(module_name):
    ref = Def0Ref(init_name(module_name))
    ref.type = bool_t
    ref.kind = Kind.State
    return ref

def find_visible_variables(extends, modules):
    visible = []
    for ex in extends:
        for m in modules:
            if m.name == ex.name:
                visible.extend(m.variables)
                break
    return visible

def find_visible_constants(extends, modules):
    visible = {}
    for ex in extends:
        for m in modules:
            if m.name == ex.name:
                visible.update(m.constants)
                break
    return visible

def add_variable(variables, visible_variables, var, type, init, unchanged):
    for v, d in visible_variables:
        if v == var:
            assert d.type == type
            return None

    desc = None
    for v, d in variables:
        if v == var:
            desc = d
            break

    assert desc == None or desc.type == type

    if desc == None:
        variables.append((var, VarDesc(type, init, unchanged)))

def new_variable(variables, visible_variables, type, name = None, init = None, unchanged = False):
    if not name:
        name = mk_name()
    add_variable(
        variables,
        visible_variables,
        name,
        type,
        init = init if init else type.sample(),
        unchanged = unchanged)
    ref = VarRef(name)
    ref.type = type
    ref.kind = Kind.State
    return ref

def build_init(variables, extends, modules):
    inits = []

    for n in extends:
        for m in modules:
            if m.name == n.name:
                if m.variables:
                    inits.append(init_ref(n.name))
                break

    for n,d in variables:
        inits.append(BinOp(BinOpId.Eq, VarRef(n), d.init))

    if inits:
        conjunction = inits[0]
        for i in inits[1:]:
            conjunction = BinOp(BinOpId.And, conjunction, i)
        conjunction.type = bool_t
        conjunction.kind = Kind.State
        return conjunction
    return None

def default_inv(variables, visible_variables):
    x = new_variable(variables, visible_variables, bool_t, 'x')
    y = new_variable(variables, visible_variables, bool_t, 'y')
    return BinOp(BinOpId.Imply, x, y)

def default_prop(variables, visible_variables):
    x = new_variable(variables, visible_variables, bool_t, 'x')
    y = new_variable(variables, visible_variables, bool_t, 'y')
    return BinOp(BinOpId.Imply, Prime(x), Prime(y))

def default_init(variables, extends, modules):
    return build_init(variables, extends, modules)

def default_next(variables, visible_variables):
    x = new_variable(variables, visible_variables, bool_t, 'x')
    y = new_variable(variables, visible_variables, bool_t, 'y')
    return BinOp(BinOpId.And,
                BinOp(BinOpId.Eq, Prime(x), Not(x)),
                BinOp(BinOpId.Eq, Prime(y), x))

def sha1(content):
    encoder = hashlib.sha1()
    encoder.update(content.encode('utf-8'))
    return encoder.hexdigest()

class TestModel:
    def __init__(self, main_module, cfg, modules = [], cmd_options = []):
        self.main_module = main_module
        self.modules = modules
        self.cfg = cfg
        self.cmd_options = cmd_options

        # Consistency checks
        assert self.main_module.name == self.cfg.name, f'{self.main_module.name} == {self.cfg.name}'
        ms = [main_module] + modules
        names = set(m.name for m in ms)
        assert len(names) == len(ms), "Modules must have unique names"

    def cmd_options(self):
        return self.cmd_options

    def render_module(self, path, module_folder, module):
        full_folder_path = os.path.join(path, module_folder)
        os.makedirs(full_folder_path, exist_ok = True)

        name = module.name
        m = module.pretty()
        full_file_path = os.path.join(full_folder_path, name + '.tla')
        with open(full_file_path, 'w') as h:
            h.write(m)

        return {
            'digest' : sha1(m),
            'name' : name,
            'path' : module_folder
        }

    def render_cfg(self, path):
        name = self.cfg.name
        full_path = os.path.join(path, name + '.cfg')
        c = self.cfg.pretty()
        with open(full_path, 'w') as h:
            h.write(c)

        return {
            'digest' : sha1(c),
            'file' : name + '.cfg',
        }

    def render(self, path, **kw):
        modules = []
        search_paths = []
        for module in [self.main_module] + self.modules:
            module_path = module.folder()
            if module_path:
                search_paths.append(module_path)
            else:
                module_path = ''
            modules.append(self.render_module(path, module_path, module))
        cfg = self.render_cfg(path)

        meta = {
            'main_module' : self.main_module.name,
            'search_paths' : search_paths,
            'cmd_options' : self.cmd_options,
            'modules' : modules,
            'cfg' : cfg
        }
        meta.update(kw)

        meta['id'] = sha1(json.dumps(meta, indent = 2))
        return meta

class TlcModel(TestModel):
    def __init__(self,
            extends = [],
            constants = {},
            variables = [],
            globals = [],
            init = None,
            next = None,
            inv = None,
            prop = None,
            view_exclude = [],
            symmetry = None,
            modules = [],
            cmd_options = []):

        self.extends = extends
        self.constants = constants
        self.variables = variables
        self.globals = globals

        if view_exclude:
            view_tuple = Tuple(*[VarRef(i) for i, _ in self.variables if i not in view_exclude])
            view = mk_name()
            self.globals.append(Def0(view, view_tuple))
        else:
            view = None

        visible = find_visible_variables(self.extends, modules)

        self.next = next if next else default_next(self.variables, visible)
        self.inv = inv
        self.prop = prop

        self.init = init if init else default_init(self.variables, self.extends, modules)

        self.name = 'TLC_M0'

        module = module_template(
            name = self.name,
            extends = self.extends,
            constants = self.constants,
            variables = self.variables,
            visible_variables = visible,
            globals = self.globals,
            init = self.init,
            next = self.next,
            inv = self.inv,
            prop = self.prop)

        visible_constants = find_visible_constants(self.extends, modules)
        visible_constants.update(self.constants)

        cfg = Cfg(
            name = self.name,
            check_deadlock = get_check_deadlock(),
            constants = visible_constants,
            invariants = ['Inv'],
            properties = ['Prop'],
            symmetry = symmetry,
            view = view)

        super().__init__(module, cfg, modules=modules, cmd_options = cmd_options)

    def render(self, path):
        # Disable type annotations for TLC
        set_type_annotations(False)
        return super().render(path)

class ApalacheModel(TestModel):
    def __init__(self,
            extends = [],
            constants = {},
            variables = [],
            globals = [],
            init = None,
            next = None,
            inv = None,
            prop = None,
            modules = []):
        self.extends = extends
        self.constants = constants
        self.variables = variables
        self.globals = globals

        visible = find_visible_variables(self.extends, modules)

        self.next = next if next else default_next(self.variables, visible)
        self.inv = inv
        self.prop = prop if prop else default_prop(self.variables, visible)

        self.init = init if init else default_init(self.variables, self.extends, modules)

        self.name = 'Apalache_M0'

        module = module_template(
            name = self.name,
            extends = self.extends,
            constants = self.constants,
            variables = self.variables,
            visible_variables = visible,
            globals = self.globals,
            init = self.init,
            next = self.next,
            inv = self.inv,
            prop = self.prop)

        visible_constants = find_visible_constants(self.extends, modules)
        visible_constants.update(self.constants)

        cfg = Cfg(
            name = self.name,
            check_deadlock = get_check_deadlock(),
            constants = visible_constants,
            invariants = ['Inv', 'Prop'],
            properties = [])

        # Apalache checks for deadlocks by default
        opts = [] if get_check_deadlock() else ['--no-deadlock']
        super().__init__(module, cfg, modules=modules, cmd_options=opts)

    def render_ir(self, path, decls):
        name = self.main_module.name
        full_path = os.path.join(path, name + '.json')

        ir = {
            "name": "ApalacheIR",
            "version": "1.0",
            "description": "https://apalache.informal.systems/docs/adr/005adr-json.html",
            "modules": [
                {
                    "kind": "TlaModule",
                    "name": name,
                    "declarations": decls
                }
            ]
        }
        ir_digest = sha1(json.dumps(ir, indent = 2))
        content = json.dumps(ir, indent = 2)
        with open(full_path, 'w') as h:
            h.write(content)
        return ir_digest

    def render(self, path):
        # Enable type annotations for Apalache
        set_type_annotations(True)
        # Initialize context for IR generation
        ir_context_initialize()
        ir = self.main_module.ir()
        ir_digest = self.render_ir(path, ir)
        tla_meta = super().render(path, ir = ir_digest)
        return tla_meta

def module_template(
        name,
        extends = [],
        constants = {},
        variables = [],
        visible_variables = [],
        globals = [],
        init = None,
        next = None,
        inv = None,
        prop = None):

    fs = []
    if extends:
        fs.append(Extends(*extends))
    if constants:
        fs.append(Constants(constants))

    assert init
    init = Def0('Init', init)

    all_variables = visible_variables + variables
    next = next if next else default_next(variables, visible_variables)
    for v,d in all_variables:
        if d.unchanged:
            ref = VarRef(v)
            # `Unchanged u` comes first: it enables use u' in the expressions
            next = BinOp(BinOpId.And, Unchanged(ref), next)
    next = Def0('Next', next)

    inv = Def0('Inv', inv if inv else default_inv(variables, visible_variables))
    prop = Def0('Prop', prop if prop else Boxed(default_prop(variables, visible_variables), Def0Ref('vars')))

    vars = Tuple(*[VarRef(v) for v, _ in all_variables])
    ann = TupleT(*[d.type for _, d in all_variables])

    if variables:
        fs.append(Variables(variables))
    fs.append(Def0('vars', vars, ann = ann))
    fs.extend(globals)
    fs.extend([
        init,
        next,
        StandardSpec,
        inv,
        prop ])

    return Module(None, name, *fs)

def testmodel_template(*args, **kw):
    return (args, kw)

# Create TLA+ model from pre-existing TLA+ module and provided CFG content
class PlainFileModel(TestModel):
    def __init__(self, name, cfg_content, cmd_options = []):
        module = PlainFileModule(name)
        cfg = RawCfg(name, cfg_content)
        self.name = module.name
        super().__init__(module, cfg, modules = [], cmd_options = cmd_options)

class TestCase:
    def make_path(self, parent_dir):
        path = os.path.join(
            self.desc['case_feature'],
            self.desc['plug_feature'],
            'dl' if self.desc['check_deadlock'] else 'no-dl'
            )
        tlc_path = os.path.join(path, 'tlc')
        ref_path = os.path.join(path, 'ref')
        os.makedirs(os.path.join(parent_dir, tlc_path), exist_ok = True)
        os.makedirs(os.path.join(parent_dir, ref_path), exist_ok = True)
        os.makedirs(os.path.join(parent_dir, path), exist_ok = True)
        return (path, tlc_path, ref_path)

    def render_meta(self, parent_dir, path, tlc_path, ref_path, meta):
        # Digest of meta should not include paths
        meta['id'] = sha1(json.dumps(meta, indent = 2))

        meta['path'] = path
        meta['tlc']['path'] = tlc_path
        meta['ref']['path'] = ref_path

        meta_path = os.path.join(os.path.join(parent_dir, path), 'testcase-' + meta['id'] + '.meta')
        with open(meta_path, 'w') as h:
            h.write(json.dumps(meta, indent = 2))

        return meta

    def render(self, path : str) -> dict:
        pass

class RefApalacheCase(TestCase):
    def __init__(self, tlc, apalache, desc):
        self.tlc = tlc
        self.ref = apalache
        self.desc = desc

    def render(self, parent : str) -> dict:
        path, tlc_path, ref_path = self.make_path(parent)
        meta = {
            'type' : TestCaseType_RefApalache,
            'desc' : self.desc,
            'tlc' : self.tlc.render(os.path.join(parent, tlc_path)),
            'ref' : self.ref.render(os.path.join(parent, ref_path))
        }
        return self.render_meta(parent, path, tlc_path, ref_path, meta)

class RefTlcCase(TestCase):
    def __init__(self, tlc, ref, desc):
        self.tlc = tlc
        self.ref = ref
        self.desc = desc

    def render(self, parent : str) -> dict:
        path, tlc_path, ref_path = self.make_path(parent)
        meta = {
            'type' : TestCaseType_RefTlc,
            'desc' : self.desc,
            'tlc' : self.tlc.render(os.path.join(parent, tlc_path)),
            'ref' : self.ref.render(os.path.join(parent, ref_path))
        }
        return self.render_meta(parent, path, tlc_path, ref_path, meta)

class TlcSymmetryCase(RefTlcCase):
    def __init__(self, tlc, ref, desc):
        super().__init__(tlc, ref, desc)

    def make_path(self, parent_dir):
        inv = ['i'] if self.desc['invariant'] else []
        prop = ['p'] if self.desc['property'] else []
        view = ['v'] if self.desc['view'] else []
        dl = ['dl'] if self.desc['check_deadlock'] else []

        path = '-'.join(['symmetry'] + inv + prop + view + dl)

        tlc_path = os.path.join(path, 'tlc')
        ref_path = os.path.join(path, 'ref')
        os.makedirs(os.path.join(parent_dir, tlc_path), exist_ok = True)
        os.makedirs(os.path.join(parent_dir, ref_path), exist_ok = True)
        os.makedirs(os.path.join(parent_dir, path), exist_ok = True)
        return (path, tlc_path, ref_path)

class AnomalousConditionCase(TestCase):
    def __init__(self, tlc, condition):
        self.tlc = tlc
        self.condition = condition
        self.desc = condition.describe()

    def make_path(self, parent_dir):
        path = os.path.join('anomalous-conditions', self.desc['tag'])
        tlc_path = os.path.join(path, 'tlc')
        os.makedirs(os.path.join(parent_dir, tlc_path), exist_ok = True)
        os.makedirs(os.path.join(parent_dir, path), exist_ok = True)
        return (path, tlc_path)

    def render_meta(self, parent_dir, path, tlc_path, meta):
        # Digest of meta should not include paths
        meta['id'] = sha1(json.dumps(meta, indent = 2))

        meta['path'] = path
        meta['tlc']['path'] = tlc_path

        meta_path = os.path.join(os.path.join(parent_dir, path), 'testcase-' + meta['id'] + '.meta')
        with open(meta_path, 'w') as h:
            h.write(json.dumps(meta, indent = 2))

        return meta

    def render(self, parent : str) -> dict:
        path, tlc_path = self.make_path(parent)
        meta = {
            'type' : TestCaseType_RefAnomalous,
            'desc' : self.desc,
            'tlc' : self.tlc.render(
                os.path.join(parent, tlc_path), anomalous_conditions = self.desc),
        }
        return self.render_meta(parent, path, tlc_path, meta)

class SkipCase(TestCase):
    def __init__(self, reason, desc):
        self.reason = reason
        self.desc = desc

    def render(self, path : str):
        return {
            'id' : sha1(json.dumps(self.desc, indent = 2)),
            'type' : 'skipped',
            'desc' : self.desc,
            'reason' : str(self.reason)
        }
