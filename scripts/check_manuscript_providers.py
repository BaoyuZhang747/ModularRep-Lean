"""Read-only checks of both provider collections against the application statement map.

This checks source identities and lexical declaration positions, not Lean name
resolution, mathematical alignment or the truth of external assumptions.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import sys

LIBRARY_SCRIPTS = Path(__file__).resolve().parents[1] / 'packages/ModularRep/scripts'
sys.path.insert(0, str(LIBRARY_SCRIPTS))
from catalogue import code_only, declaration_index
from manuscript_map import (module_from_library_path, relative_source_path,
                            validate_manuscript_map, validate_manuscript_provider)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def application_inventory(root):
    paths = list((root / 'ManuscriptIBAW').rglob('*.lean'))
    if (root / 'ManuscriptIBAW.lean').is_file():
        paths.append(root / 'ManuscriptIBAW.lean')
    return {path.relative_to(root).as_posix() for path in paths}


def check_application_providers(root):
    root = Path(root).resolve()
    read_bytes = {}

    def read(relative):
        path = (root / relative).resolve()
        if not path.is_relative_to(root) or not path.is_file():
            raise ValueError('Missing or escaping source: ' + relative)
        raw = path.read_bytes()
        if path in read_bytes and raw != read_bytes[path]:
            raise ValueError('Input changed during verification: ' + relative)
        read_bytes[path] = raw
        return raw

    projection_raw = read('packages/ModularRep/docs/current-manuscript-map.json')
    projection = validate_manuscript_map(json.loads(projection_raw))
    parent_raw = read('audit/current/statement-map.json')
    parent = json.loads(parent_raw)
    if projection.get('parent_statement_map_sha256') != digest(parent_raw):
        raise ValueError('Projection is not bound to the current parent statement map.')
    for value in (projection, parent):
        manuscript_hash = value.get('manuscript_sha256')
        if not isinstance(manuscript_hash, str) or not re.fullmatch(r'[a-fA-F0-9]{64}', manuscript_hash):
            raise ValueError('Missing or invalid manuscript source hash.')
    if projection['manuscript_sha256'] != parent['manuscript_sha256']:
        raise ValueError('Projection and parent concern different manuscript sources.')
    if not isinstance(parent.get('statements'), list):
        raise ValueError('Parent statement map lacks its statements list.')
    mapped = {}
    for item in parent['statements']:
        key = item.get('label') or item.get('id')
        if not isinstance(key, str) or key in mapped:
            raise ValueError('Missing or duplicate parent statement identifier.')
        mapped[key] = item
    if set(mapped) != {item['label'] for item in projection['labels']}:
        raise ValueError('Projection does not cover the exact parent statement set.')

    inventory = application_inventory(root)
    library = json.loads(read('packages/ModularRep/modules.json'))
    library_rows = library.get('modules') if isinstance(library, dict) else None
    if not isinstance(library_rows, list):
        raise ValueError('Library inventory lacks its modules list.')
    local_lookup = {row['module']: row for row in library_rows}
    if len(local_lookup) != len(library_rows):
        raise ValueError('Duplicate module in the library inventory.')
    counts = {kind: {'lexical': 0, 'pending': 0}
              for kind in ('library', 'application')}
    sources = {}
    for item in projection['labels']:
        declarations = mapped[item['label']].get('declarations')
        if not isinstance(declarations, list):
            raise ValueError('Parent statement lacks declarations: ' + item['label'])
        expected = {'providers': {}, 'application_providers': {}}
        for declaration in declarations:
            relative = relative_source_path(declaration.get('path'))
            if relative in inventory:
                category = 'application_providers'
                module = relative[:-5].replace('/', '.')
            elif relative.startswith('packages/ModularRep/'):
                category = 'providers'
                module = module_from_library_path(relative[len('packages/ModularRep/'):])
            else:
                raise ValueError('Parent declaration has no owning source inventory: ' + relative)
            name = declaration.get('declaration')
            if not isinstance(name, str) or not name:
                raise ValueError('Parent declaration lacks its name: ' + relative)
            identity = (module, name)
            if identity in expected[category]:
                raise ValueError('Duplicate parent declaration: ' + name)
            expected[category][identity] = declaration
        for category in expected:
            actual = {(entry['module'], entry['declaration']): entry for entry in item[category]}
            if set(actual) != set(expected[category]):
                raise ValueError('Projection provider membership differs from parent: '
                                 + item['label'] + ' / ' + category)
            for identity, entry in actual.items():
                original = expected[category][identity]
                relative = original['path']
                if relative not in sources:
                    raw = read(relative)
                    sources[relative] = {'sha256': digest(raw), 'declarations':
                        declaration_index(code_only(raw.decode('utf-8-sig')))}
                source = sources[relative]
                if original.get('source_sha256') != source['sha256']:
                    raise ValueError('Parent declaration source hash differs: ' + relative)
                provider = dict(original)
                provider.setdefault('declaration_presence_check', original.get('declaration_check'))
                status = validate_manuscript_provider(provider, source)
                kind = 'application' if category == 'application_providers' else 'library'
                counts[kind]['pending' if status == 'compiler_name_resolution_pending' else 'lexical'] += 1
                if category == 'providers':
                    local = local_lookup.get(identity[0])
                    if (local is None or local.get('path') != entry['path']
                            or local.get('sha256') != source['sha256']
                            or relative != 'packages/ModularRep/' + entry['path']
                            or entry.get('source_sha256') != source['sha256']):
                        raise ValueError('Local provider disagrees with its source inventory: ' + identity[0])
                    local_status = validate_manuscript_provider(entry, source)
                    if ((local_status == 'compiler_name_resolution_pending')
                            != (status == 'compiler_name_resolution_pending')):
                        raise ValueError('Projection and parent declaration statuses conflict: ' + identity[1])
                    if local_status != 'compiler_name_resolution_pending' and entry.get('line') != original.get('line'):
                        raise ValueError('Projection and parent declaration lines differ: ' + identity[1])
    if application_inventory(root) != inventory:
        raise ValueError('Application source inventory changed during verification.')
    for path, raw in read_bytes.items():
        if path.read_bytes() != raw:
            raise ValueError('Input changed during verification: ' + path.relative_to(root).as_posix())
    return {'status': 'passed_source_checks', 'counts': counts,
            'projection_sha256': digest(projection_raw), 'parent_statement_map_sha256': digest(parent_raw),
            'referenced_source_count': len(sources), 'compiler_name_resolution_performed': False,
            'scope': 'Exact projection membership, source inventory membership and hashes, lexical '
                     'name/line checks, and explicit pending statuses. No Lean or mathematical verification.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    print(json.dumps(check_application_providers(args.root), indent=2))


if __name__ == '__main__':
    main()
