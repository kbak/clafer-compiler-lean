"""Actual Choco generation, strict identity extraction, negative candidates and replay."""
import copy
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts/comparison'))
import choco


# [utest->req~compiler-choco-instances~1]
class ChocoTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        tools = os.environ.get('CLAFER_CHOCO_TOOLS')
        if not tools:
            raise RuntimeError('CLAFER_CHOCO_TOOLS required; provision the Choco adapter')
        parent = choco.oracle.external(os.environ.get('CLAFER_ORACLE_EVIDENCE', tempfile.gettempdir()))
        parent.mkdir(parents=True, exist_ok=True)
        cls.output = Path(tempfile.mkdtemp(prefix='choco-', dir=parent))
        print('Choco evidence: '+str(cls.output), flush=True)
        cls.runtime = choco.Runtime(tools, cls.output/'runtime')
        cls.results = choco.demonstration(cls.runtime, cls.output/'demo')
        cls.bag = cls.output/'demo/bag'
        cls.core = json.loads((cls.bag/'core.json').read_text())
        cls.bounds = dict(root=1, Target=1, refs=2)
        cls.raw = (cls.bag/'raw.xml').read_bytes()

    def test_generated_controls_and_counts(self):
        bag, no_set, distinct = [self.results[n] for n in ('bag','set','set-distinct')]
        for value in (bag, distinct):
            self.assertEqual(value['generated'], value['decoded'])
            self.assertEqual(value['generated'], value['checked'])
            self.assertGreaterEqual(value['satisfies'], 1)
            self.assertEqual(value['violates'], 0)
        self.assertEqual([no_set[k] for k in ('generated','decoded','checked')], [0,0,0])
        self.assertEqual(no_set['supplied']['shared']['category'], 'agree_violates')
        candidate = json.loads((self.bag/'instance-0/candidate.json').read_text())
        self.assertEqual(len({pair[0] for _,pair in candidate['references']}), 2)
        self.assertEqual(len({pair[1] for _,pair in candidate['references']}), 1)
        self.assertTrue((self.bag/'explicit.cfr').read_text().startswith('//# OPTIONS --explicit\n'))
        tables = json.loads((self.bag/'instance-0/tables.json').read_text())
        for table in tables.values(): self.assertEqual(set(table), {'root','Target','refs'})
        self.assertEqual(tables['references']['Target'], [])
        for label in ('collapsed','missing_reference'):
            self.assertEqual(bag['supplied'][label], dict(category='agree_violates',complete=True))

    def test_inherited_nested_and_cyclic_identities(self):
        bounds = dict(root=1, Base=1, left=1, right=1, left__leaf=1, right__leaf=1, refs=2, a=1, b=1)
        result = choco.run_case(self.runtime, choco.FIXTURES/'identity.cfr', bounds,
                                self.output/'identity')
        self.assertEqual(result['status'], 'completed', result)
        self.assertGreater(result['satisfies'], 0)
        self.assertEqual(result['violates'], 0)
        candidate = json.loads((self.output/'identity/instance-0/candidate.json').read_text())
        memberships = dict((u, {o for v,o in candidate['members'] if v == u}) for u in bounds)
        self.assertEqual(memberships['Base'], memberships['left'])
        self.assertEqual({u for u,_ in candidate['references']}, {'refs','a','b'})

    def test_strict_export_and_declaration_mapping(self):
        def bad(change):
            tree = ET.fromstring(self.raw)
            change(tree)
            return ET.tostring(tree)
        mutations = [
            lambda t: t.find('declarations')[0].set('uid', 'unknown'),
            lambda t: t.find('declarations').remove(t.find('declarations')[0]),
            lambda t: t.find('declarations')[0].set('cardHigh', '2'),
            lambda t: t.find('declarations')[0].set('scope', '2'),
            lambda t: t.find('search').set('generated', '2'),
            lambda t: t.find('search').set('termination', 'unsat'),
            lambda t: t.find('instance').set('index', '1'),
        ]
        for change in mutations:
            with self.assertRaises(ValueError): choco.envelope(bad(change), self.core, self.bounds)
        for change in (
            lambda t: t.find('instance').append(copy.deepcopy(t.find('instance')[0])),
            lambda t: t.find('instance')[0].set('type','unknown'),
            lambda t: t.find('instance')[0].set('parentId','9'),
            lambda t: t.find('instance')[1][0].set('id','9'),
            lambda t: t.find('instance')[1].append(copy.deepcopy(t.find('instance')[1][0])),
        ):
            instances, _, _ = choco.envelope(bad(change), self.core, self.bounds)
            with self.assertRaises(ValueError):
                choco.decode(instances[0], self.core, self.bounds, self.runtime.comparison.relation)
        with self.assertRaises(ET.ParseError): choco.envelope(self.raw[:-20], self.core, self.bounds)
        with self.assertRaises(ValueError):
            choco.envelope(b'<!DOCTYPE x>'+self.raw, self.core, self.bounds)

    def test_rejected_generated_instance_is_retained(self):
        tree = ET.fromstring(self.raw)
        head = tree.find('instance')[1]
        head.remove(head[0])
        def damaged(runtime, output, timeout, limit):
            (output/'raw.xml').write_bytes(ET.tostring(tree))
        with patch.object(choco, 'solve', damaged):
            result = choco.run_case(self.runtime, choco.FIXTURES/'bag.cfr', self.bounds,
                                    self.output/'damaged-export')
        self.assertEqual(result['status'], 'completed', result)
        self.assertEqual([result[k] for k in ('generated','decoded','checked','violates')], [1,1,1,1])
        self.assertEqual(result['instances'][0]['exact'], 'agree_violates')

    def test_admission_and_operational_failures(self):
        for index, source in enumerate(('A\n[A]\n', '//# OPTIONS --explicit\nA\n',
                                        'A -> integer\n', '[choco| ignored |]\nA\n')):
            path = self.output/('unsupported-'+str(index)+'.cfr')
            path.write_text(source)
            result = choco.run_case(self.runtime, path, dict(root=1,A=1), self.output/('unsupported-'+str(index)))
            self.assertEqual(result['status'], 'unsupported', result)
            self.assertIsNone(result['generated'])
            self.assertEqual(result['checked'], 0)
        home = self.output/'fake-java'
        (home/'bin').mkdir(parents=True)
        java = home/'bin/java'
        for label, text, expected in [('exit', '#!/bin/sh\nexit 7\n', 'error'),
                                       ('stall', '#!/bin/sh\nexec sleep 3\n', 'timeout')]:
            java.write_text(text)
            java.chmod(0o755)
            with patch.dict(self.runtime.tools, java_home=str(home)):
                result = choco.run_case(self.runtime, choco.FIXTURES/'bag.cfr', self.bounds,
                                       self.output/label, timeout=1)
            self.assertEqual(result['status'], expected, result)
            self.assertIsNone(result['generated'])

    def test_exact_replay_and_tampering(self):
        result = choco.replay(self.runtime, self.bag, self.output/'bag-replay')
        self.assertEqual(result['status'], 'completed', result)
        self.assertGreater(result['satisfies'], 0)
        self.assertTrue((self.output/'bag-replay/retained-instance-0/result.json').is_file())
        import shutil
        shutil.copytree(self.bag, self.output/'tampered')
        (self.output/'tampered/instance-0/mapping.json').write_text('[]')
        with self.assertRaisesRegex(ValueError, 'identity changed'):
            choco.replay(self.runtime, self.output/'tampered', self.output/'tampered-replay')


if __name__ == '__main__':
    unittest.main()
