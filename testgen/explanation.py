# SPDX-FileCopyrightText: Copyright (c) 2022 NVIDIA CORPORATION & AFFILIATES. All rights reserved.

from dataclasses import dataclass
import sys
import yaml
import logging

def yaml_safe_load(yaml_file):
    try:
        with open(yaml_file) as h:
            db = yaml.safe_load(h)
            return db
    except yaml.scanner.ScannerError as es:
        logging.error(f'YAML scan error: {yaml_file}\n  {str(es)}')
        sys.exit()
    except yaml.parser.ParserError as ep:
        logging.error(f'YAML parse error: {yaml_file}\n  {str(ep)}')
        sys.exit()

@dataclass
class Explanation:
    desc : dict
    tlc : str
    ref : str
    explanation : str

def make_key(desc):
    if 'case_feature' not in desc:
        return None
    case = desc['case_feature']
    plug = desc['plug_feature']
    deadlock = desc['check_deadlock']
    return f'{case}-{plug}-{deadlock}'

class ExplanationDB:
    def __init__(self, db_file):
        self.db = {}
        self.db_file = db_file

        if not db_file:
            return

        db = yaml_safe_load(db_file)
        for i in db['explanations']:
            key = make_key(i['desc'])
            if key in self.db:
                logging.error(f'ExplanationDB: {i["desc"]} has duplicates in `{db_file}`')
                exit(1)
            self.db[key] = Explanation(
                desc = i['desc'],
                tlc = i['result']['tlc'],
                ref = i['result']['ref'],
                explanation = i['explanation'])

    def find_explanation(self, desc, tlc, ref):
        key = make_key(desc)
        e = self.db.get(key)
        if e:
            if e.tlc != tlc or e.ref != ref:
                logging.error(f'ExplanationDB: {e.desc} results ({e.tlc}, {e.ref}) are inconsistent with actual results ({tlc}, {ref}) `{self.db_file}`')
                exit(1)
        return e
