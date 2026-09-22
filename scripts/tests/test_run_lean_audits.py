"""Audit orchestration regressions without downloading or rebuilding dependencies."""
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import run_lean_audits as audits


class AuditRunnerTests(unittest.TestCase):
    def setUp(self):
        # Mocked compiler calls must not print a real-audit success claim in CI.
        self.enterContext(redirect_stdout(io.StringIO()))
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name) / 'repo'
        self.core = Path(self.temporary.name) / 'lean/lib/lean'
        self.core.mkdir(parents=True)
        for name in ['Init', 'Lean', 'Std/Tactic']:
            path = self.core / (name + '.olean')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b'fixture compiler module')
        library = self.root / 'packages/ModularRep'
        library.mkdir(parents=True)
        (library / 'audit-targets.json').write_text(json.dumps({'scripts': [
            'audits/ReusableProviders.lean', 'audits/SporadicAxioms.lean',
            'audits/SporadicDependencies.lean', 'audits/Manuscript.lean']}), encoding='utf-8')
        self.targets = audits.audit_targets(self.root)
        self.imports = [
            ['Init', 'Init', 'ModularRep.Z', 'ModularRep.AxiomGate', 'ModularRep.A'],
            ['Init', 'ModularRep.AxiomGate', 'ModularRep.Z'],
            ['Init', 'ModularRep.AxiomGate'],
            ['Init', 'ModularRep.Manuscript', 'ModularRep.AxiomGate'],
            ['Init', 'Lean', 'Std.Tactic', 'ManuscriptIBAW.Main', 'ModularRep.AxiomGate'],
        ]
        self.payload = {'imports': [{'errors': [], 'result': {'imports': [
            {'module': module} for module in modules]}} for modules in self.imports]}
        self.calls = []

    def compiler(self, command, **kwargs):
        self.calls.append((command, kwargs))
        self.assertEqual(kwargs['cwd'], self.root)
        self.assertTrue(kwargs['check'])
        if command[:2] == ['lean', '--deps-json']:
            self.assertEqual(command[2:], self.targets)
            return subprocess.CompletedProcess(command, 0, json.dumps(self.payload))
        if command == ['lean', '--print-libdir']:
            return subprocess.CompletedProcess(command, 0, str(self.core) + '\n')
        return subprocess.CompletedProcess(command, 0)

    def test_missing_axiom_gate_is_built_before_any_audit(self):
        built = set()
        def execute(command, **kwargs):
            result = self.compiler(command, **kwargs)
            if command[:2] == ['lake', 'build']:
                built.update(command[2:])
            elif command[:3] == ['lake', 'env', 'lean']:
                if '+ModularRep.AxiomGate:olean' not in built:
                    raise subprocess.CalledProcessError(1, command, stderr='Missing AxiomGate.olean')
            return result
        with patch.object(audits.subprocess, 'run', side_effect=execute):
            audits.run_audits(self.root)
        build = self.calls[2][0]
        self.assertEqual(build, ['lake', 'build', '+ManuscriptIBAW.Main:olean',
            '+ModularRep.A:olean', '+ModularRep.AxiomGate:olean',
            '+ModularRep.Manuscript:olean', '+ModularRep.Z:olean'])
        self.assertEqual([c[0][-1] for c in self.calls[3:]], self.targets)
        for command, _ in self.calls[3:]:
            self.assertEqual(command[:-1], ['lake', 'env', 'lean', '--trust=0', '--threads=1'])

    def test_import_order_and_duplicates_do_not_change_build_targets(self):
        with patch.object(audits.subprocess, 'run', side_effect=self.compiler):
            first = audits.dependency_modules(self.root, self.targets)
            for row in self.payload['imports']:
                row['result']['imports'].reverse()
            second = audits.dependency_modules(self.root, self.targets)
        self.assertEqual(first, second)
        self.assertEqual(first, sorted(set(first)))

    def test_zero_exit_header_errors_stop_before_build(self):
        self.payload['imports'][2] = {'errors': ['unexpected end of import'], 'result': None}
        with patch.object(audits.subprocess, 'run', side_effect=self.compiler):
            with self.assertRaisesRegex(ValueError, 'SporadicDependencies'):
                audits.run_audits(self.root)
        self.assertEqual(len(self.calls), 1)

    def test_incomplete_compiler_inventory_is_rejected(self):
        self.payload['imports'].pop()
        with patch.object(audits.subprocess, 'run', side_effect=self.compiler):
            with self.assertRaisesRegex(ValueError, 'incomplete'):
                audits.run_audits(self.root)
        self.assertEqual(len(self.calls), 1)

    def test_invalid_import_is_rejected(self):
        self.payload['imports'][0]['result']['imports'].append({'module': None})
        with patch.object(audits.subprocess, 'run', side_effect=self.compiler):
            with self.assertRaisesRegex(ValueError, 'invalid import'):
                audits.run_audits(self.root)

    def test_dependency_build_failure_prevents_all_audits(self):
        def execute(command, **kwargs):
            result = self.compiler(command, **kwargs)
            if command[:2] == ['lake', 'build']:
                raise subprocess.CalledProcessError(1, command)
            return result
        with patch.object(audits.subprocess, 'run', side_effect=execute):
            with self.assertRaises(subprocess.CalledProcessError):
                audits.run_audits(self.root)
        self.assertFalse(any(c[0][:2] == ['lake', 'env'] for c in self.calls))

    def test_audit_failure_stops_remaining_audits(self):
        def execute(command, **kwargs):
            result = self.compiler(command, **kwargs)
            if command[:2] == ['lake', 'env']:
                raise subprocess.CalledProcessError(1, command)
            return result
        with patch.object(audits.subprocess, 'run', side_effect=execute):
            with self.assertRaises(subprocess.CalledProcessError):
                audits.run_audits(self.root)
        self.assertEqual(sum(c[0][:2] == ['lake', 'env'] for c in self.calls), 1)

    def test_compiler_failure_propagates(self):
        with patch.object(audits.subprocess, 'run', side_effect=subprocess.CalledProcessError(2, ['lean'])):
            with self.assertRaises(subprocess.CalledProcessError):
                audits.run_audits(self.root)

    def test_core_only_imports_need_no_lake_build(self):
        self.payload = {'imports': [{'errors': [], 'result': {'imports': [{'module': 'Init'}]}}
                                   for _ in self.targets]}
        with patch.object(audits.subprocess, 'run', side_effect=self.compiler):
            audits.run_audits(self.root)
        self.assertFalse(any(c[0][:2] == ['lake', 'build'] for c in self.calls))


if __name__ == '__main__':
    unittest.main()
