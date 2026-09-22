"""Check manuscript identity and pinned dependency configurations.

The legacy --inventory option delegates to the current MANIFEST.json release
verifier; there is only one authoritative export inventory.
No Lean compilation or mathematical verification is performed.
"""
from pathlib import Path
import argparse, hashlib, json, sys, tomllib
sys.dont_write_bytecode = True

TOOLCHAIN = 'leanprover/lean4:v4.33.1'
DEPENDENCIES = {
    'mathlib': ('https://github.com/leanprover-community/mathlib4', '0df444a360eaa60ab8c11dca51a86af692955474'),
    'plausible': ('https://github.com/leanprover-community/plausible', 'b7eb3304aeae834b12dda98993a37f6a41f6f0bb'),
    'LeanSearchClient': ('https://github.com/leanprover-community/LeanSearchClient', '5f4d51b81cbd3f6b32b156bfad9056621a040404'),
    'importGraph': ('https://github.com/leanprover-community/import-graph', '16f02aa7642864af59f1ff0e384a015994db9118'),
    'proofwidgets': ('https://github.com/leanprover-community/ProofWidgets4', '4be2e3d5087eeb272cf5a8853b8f9dd025ef5957'),
    'aesop': ('https://github.com/leanprover-community/aesop', '3448c0bcc5ce01b2d1546e483ec3620e32df3d0e'),
    'Qq': ('https://github.com/leanprover-community/quote4', '92c15be17b7caf78c2ad767ec40f89052d908d81'),
    'batteries': ('https://github.com/leanprover-community/batteries', '4488d40d070b9700d4d5a6aa342f0d40c31b2a2d'),
    'Cli': ('https://github.com/leanprover/lean4-cli', '6130a47896ce867c6a4a55373441e59e565bad0f'),
}
PACKAGE_PATHS = {
    'ManuscriptIBAW': '',
    'ModularRep': 'packages/ModularRep',
    'formalisation': 'packages/ModularRep/packages/formalisation',
}
LOCAL_DEPENDENCIES = {
    'ManuscriptIBAW': {'ModularRep': 'packages/ModularRep',
                      'formalisation': 'packages/ModularRep/packages/formalisation'},
    'ModularRep': {'formalisation': 'packages/formalisation'},
    'formalisation': {},
}

def named_rows(rows, label):
    if not isinstance(rows, list):
        raise ValueError('Missing dependency list: ' + label)
    result = {}
    for row in rows:
        if not isinstance(row, dict) or not isinstance(row.get('name'), str):
            raise ValueError('Invalid dependency entry: ' + label)
        name = row['name']
        if name in result:
            raise ValueError('Duplicate dependency: ' + label + ': ' + name)
        result[name] = row
    return result

def check_dependencies(read):
    """Validate all three local packages without resolving or downloading dependencies."""
    checked = {}
    for package_name, relative in PACKAGE_PATHS.items():
        prefix = relative + '/' if relative else ''
        def package_read(name):
            path = prefix + name
            raw = read(path)
            checked[path] = digest(raw)
            return raw
        if package_read('lean-toolchain').decode().strip() != TOOLCHAIN:
            raise ValueError('Unexpected Lean toolchain: ' + package_name)
        config = tomllib.loads(package_read('lakefile.toml').decode())
        if config.get('name') != package_name:
            raise ValueError('Unexpected Lake package name: ' + package_name)
        required = named_rows(config.get('require'), prefix + 'lakefile.toml')
        expected_required = ({'ModularRep'} if package_name == 'ManuscriptIBAW'
                             else {'mathlib', 'formalisation'} if package_name == 'ModularRep'
                             else {'mathlib'})
        if set(required) != expected_required:
            raise ValueError('Unexpected direct dependencies: ' + package_name)
        for name, row in required.items():
            if name == 'mathlib':
                if (row.get('rev'), row.get('scope')) != ('v4.33.1', 'leanprover-community') or any(k in row for k in ('path', 'git', 'url')):
                    raise ValueError('Unexpected Mathlib requirement: ' + package_name)
            elif row.get('path') != LOCAL_DEPENDENCIES[package_name][name] or any(k in row for k in ('git', 'url', 'rev')):
                raise ValueError('Unexpected local requirement: ' + package_name + ': ' + name)
        lock = json.loads(package_read('lake-manifest.json'))
        if not isinstance(lock, dict) or lock.get('name') != package_name:
            raise ValueError('Unexpected lockfile package: ' + package_name)
        if lock.get('packagesDir') != '.lake/packages' or lock.get('lakeDir') != '.lake':
            raise ValueError('Unexpected Lake dependency directories: ' + package_name)
        locked = named_rows(lock.get('packages'), prefix + 'lake-manifest.json')
        local = LOCAL_DEPENDENCIES[package_name]
        if set(locked) != set(DEPENDENCIES) | set(local):
            raise ValueError('Unexpected locked dependency names: ' + package_name)
        for name, (url, revision) in DEPENDENCIES.items():
            row = locked[name]
            if (row.get('type'), row.get('url'), row.get('rev')) != ('git', url, revision):
                raise ValueError('Unexpected dependency pin: ' + package_name + ': ' + name)
            config_file = 'lakefile.lean' if name in ('mathlib', 'proofwidgets') else 'lakefile.toml'
            if (row.get('subDir'), row.get('configFile'), row.get('manifestFile')) != (None, config_file, 'lake-manifest.json'):
                raise ValueError('Unexpected dependency configuration: ' + package_name + ': ' + name)
        for name, directory in local.items():
            row = locked[name]
            if (row.get('type'), row.get('dir'), row.get('configFile'), row.get('manifestFile')) != ('path', directory, 'lakefile.toml', 'lake-manifest.json'):
                raise ValueError('Unexpected local dependency: ' + package_name + ': ' + name)
    return {'toolchain': TOOLCHAIN, 'package_names': list(PACKAGE_PATHS),
            'external_revisions': {name: revision for name, (_, revision) in DEPENDENCIES.items()},
            'configuration_sha256': checked,
            'scope': 'Configuration pins only. Dependencies were not downloaded or compiler-resolved.'}

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def check(root, inventory=False):
    root = Path(root).resolve()
    if inventory:
        # Lazy import avoids a module cycle. The release verifier calls this
        # function only with inventory=False through check_repository.
        from verify_release import check_release
        return check_release(root)
    def read(name):
        p = root / name
        if not p.resolve().is_relative_to(root) or not p.is_file():
            raise ValueError('Missing or escaping input: ' + name)
        return p.read_bytes()
    source_hash = digest(read('manuscript/current/main.tex'))
    identifiers = []
    for name, key in [('audit/current/manuscript.json', 'sha256'),
                      ('audit/current/statement-map.json', 'manuscript_sha256'),
                      ('packages/ModularRep/docs/current-manuscript-map.json', 'manuscript_sha256')]:
        record = json.loads(read(name))
        if record.get(key) != source_hash:
            raise ValueError('Manuscript binding differs: ' + name)
        identifiers.append(name)
    dependencies = check_dependencies(read)
    return {'status': 'passed_source_identity_checks', 'manuscript_sha256': source_hash,
            'bindings_checked': identifiers, 'inventory_file_count': None,
            'dependencies': dependencies,
            'scope': 'Manuscript source identity and dependency configurations only. No Lean compilation, theorem verification or release approval.'}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--inventory', action='store_true',
                        help='Verify the pristine export using MANIFEST.json (alias for verify_release.py).')
    args = parser.parse_args()
    try:
        print(json.dumps(check(args.root, args.inventory), indent=2))
    except (ValueError, KeyError, TypeError, OSError) as error:
        parser.exit(1, f'Package check failed: {error}\n')

if __name__ == '__main__':
    main()
