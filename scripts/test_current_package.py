"""Regression tests for application dependency and inventory validation."""
from copy import deepcopy
from pathlib import Path
import hashlib
import json
import tempfile
import unittest
from unittest.mock import patch

import check_current_package as checker


class CurrentPackageTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.write('manuscript/current/main.tex', b'mathematical source\n')
        source_hash = hashlib.sha256(b'mathematical source\n').hexdigest()
        for name, key in [('audit/current/manuscript.json', 'sha256'),
                          ('audit/current/statement-map.json', 'manuscript_sha256'),
                          ('packages/ModularRep/docs/current-manuscript-map.json', 'manuscript_sha256')]:
            self.write_json(name, {key: source_hash})
        for name, prefix in checker.PACKAGE_PATHS.items():
            prefix = prefix + '/' if prefix else ''
            self.write(prefix + 'lean-toolchain', (checker.TOOLCHAIN + '\n').encode())
            requirements = ('[[require]]\nname = "ModularRep"\npath = "packages/ModularRep"\n'
                            if name == 'ManuscriptIBAW' else
                            '[[require]]\nname = "mathlib"\nscope = "leanprover-community"\nrev = "v4.33.1"\n')
            if name == 'ModularRep':
                requirements += '[[require]]\nname = "formalisation"\npath = "packages/formalisation"\n'
            self.write(prefix + 'lakefile.toml', (f'name = "{name}"\n' + requirements).encode())
            rows = [{'name': dep, 'type': 'git', 'url': url, 'rev': rev,
                     'configFile': 'lakefile.lean' if dep in ('mathlib', 'proofwidgets') else 'lakefile.toml',
                     'manifestFile': 'lake-manifest.json', 'subDir': None}
                    for dep, (url, rev) in checker.DEPENDENCIES.items()]
            rows += [{'name': dep, 'type': 'path', 'dir': directory,
                      'configFile': 'lakefile.toml', 'manifestFile': 'lake-manifest.json'}
                     for dep, directory in checker.LOCAL_DEPENDENCIES[name].items()]
            self.write_json(prefix + 'lake-manifest.json', {
                'name': name, 'packages': rows, 'packagesDir': '.lake/packages', 'lakeDir': '.lake'})

    def write(self, name, raw):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)

    def write_json(self, name, value):
        self.write(name, json.dumps(value).encode())

    def mutate_lock(self, prefix, change):
        name = prefix + 'lake-manifest.json'
        value = json.loads((self.root / name).read_bytes())
        change(value)
        self.write_json(name, value)

    def rejected(self, match):
        return self.assertRaisesRegex(ValueError, match)

    def test_valid_package_without_inventory(self):
        result = checker.check(self.root)
        self.assertEqual(len(result['dependencies']['configuration_sha256']), 9)
        self.assertEqual(set(result['dependencies']['external_revisions']),
                         {'mathlib', 'plausible', 'LeanSearchClient', 'importGraph',
                          'proofwidgets', 'aesop', 'Qq', 'batteries', 'Cli'})
        self.assertIsNone(result['inventory_file_count'])

    def test_inventory_delegates_to_current_release_verifier(self):
        expected = {'status': 'passed_release_checks', 'files': 14}
        with patch('verify_release.check_release', return_value=expected) as verify:
            self.assertEqual(checker.check(self.root, True), expected)
            verify.assert_called_once_with(self.root.resolve())

    def test_each_toolchain_is_checked(self):
        for prefix in checker.PACKAGE_PATHS.values():
            with self.subTest(package=prefix):
                name = (prefix + '/' if prefix else '') + 'lean-toolchain'
                original = (self.root / name).read_bytes()
                self.write(name, b'leanprover/lean4:v4.33.0\n')
                with self.rejected('toolchain'):
                    checker.check(self.root)
                self.write(name, original)

    def test_each_external_pin_is_checked_in_each_package(self):
        for prefix in checker.PACKAGE_PATHS.values():
            prefix = prefix + '/' if prefix else ''
            name = prefix + 'lake-manifest.json'
            original = (self.root / name).read_bytes()
            for dep in checker.DEPENDENCIES:
                with self.subTest(package=prefix, dependency=dep):
                    self.mutate_lock(prefix, lambda v: next(r for r in v['packages'] if r['name'] == dep).update(rev='0' * 40))
                    with self.rejected('dependency pin'):
                        checker.check(self.root)
                    self.write(name, original)

    def test_matching_but_wrong_mathlib_pins_are_rejected(self):
        for prefix in checker.PACKAGE_PATHS.values():
            self.mutate_lock(prefix + '/' if prefix else '',
                             lambda v: next(r for r in v['packages'] if r['name'] == 'mathlib').update(rev='0' * 40))
        with self.rejected('dependency pin'):
            checker.check(self.root)

    def test_changed_repository_is_rejected(self):
        self.mutate_lock('', lambda v: v['packages'][0].update(url='https://example.invalid/mathlib'))
        with self.rejected('dependency pin'):
            checker.check(self.root)

    def test_git_subdirectory_is_checked(self):
        self.mutate_lock('', lambda v: v['packages'][0].update(subDir='other-package'))
        with self.rejected('dependency configuration'):
            checker.check(self.root)

    def test_git_configuration_file_is_checked(self):
        self.mutate_lock('', lambda v: v['packages'][0].update(configFile='other.lean'))
        with self.rejected('dependency configuration'):
            checker.check(self.root)

    def test_dependency_cache_location_is_checked(self):
        self.mutate_lock('', lambda v: v.update(packagesDir='../other-cache'))
        with self.rejected('dependency directories'):
            checker.check(self.root)

    def test_missing_dependency_is_rejected(self):
        self.mutate_lock('', lambda v: v['packages'].pop())
        with self.rejected('dependency names'):
            checker.check(self.root)

    def test_duplicate_dependency_is_rejected(self):
        self.mutate_lock('', lambda v: v['packages'].append(deepcopy(v['packages'][0])))
        with self.rejected('Duplicate dependency'):
            checker.check(self.root)

    def test_extra_dependency_is_rejected(self):
        self.mutate_lock('', lambda v: v['packages'].append({'name': 'unexpected'}))
        with self.rejected('dependency names'):
            checker.check(self.root)

    def test_git_dependency_cannot_be_replaced_by_local_source(self):
        self.mutate_lock('', lambda v: v['packages'][0].update(type='path', dir='elsewhere'))
        with self.rejected('dependency pin'):
            checker.check(self.root)

    def test_local_dependency_location_is_checked(self):
        self.mutate_lock('', lambda v: next(r for r in v['packages'] if r['name'] == 'ModularRep').update(dir='../other'))
        with self.rejected('local dependency'):
            checker.check(self.root)

    def test_lockfile_package_name_is_checked(self):
        self.mutate_lock('', lambda v: v.update(name='unrelated'))
        with self.rejected('lockfile package'):
            checker.check(self.root)

    def test_malformed_dependency_list_is_rejected(self):
        self.mutate_lock('', lambda v: v.update(packages={}))
        with self.rejected('dependency list'):
            checker.check(self.root)

    def test_config_package_name_is_checked(self):
        name = 'lakefile.toml'
        self.write(name, (self.root / name).read_bytes().replace(b'name = "ManuscriptIBAW"', b'name = "other"'))
        with self.rejected('Lake package name'):
            checker.check(self.root)

    def test_direct_local_requirement_is_checked(self):
        name = 'lakefile.toml'
        self.write(name, (self.root / name).read_bytes().replace(b'packages/ModularRep', b'other/ModularRep'))
        with self.rejected('local requirement'):
            checker.check(self.root)

    def test_mathlib_requirement_is_checked(self):
        name = 'packages/ModularRep/lakefile.toml'
        self.write(name, (self.root / name).read_bytes().replace(b'v4.33.1', b'master'))
        with self.rejected('Mathlib requirement'):
            checker.check(self.root)

    def test_missing_config_is_rejected(self):
        (self.root / 'lean-toolchain').unlink()
        with self.rejected('Missing or escaping input'):
            checker.check(self.root)

    def test_manuscript_binding_is_still_checked(self):
        self.write_json('audit/current/manuscript.json', {'sha256': '0' * 64})
        with self.rejected('Manuscript binding'):
            checker.check(self.root)

    def test_inventory_propagates_release_verifier_failure(self):
        with patch('verify_release.check_release', side_effect=ValueError('Release inventory differs')):
            with self.rejected('Release inventory differs'):
                checker.check(self.root, True)

    def test_obsolete_inventory_does_not_replace_manifest(self):
        self.write_json('release-manifest.json', {'files': []})
        with self.rejected('Missing source file: MANIFEST.json'):
            checker.check(self.root, True)


if __name__ == '__main__':
    unittest.main()
