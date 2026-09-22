"""Read the standalone library's manuscript projection without changing files."""
from pathlib import Path, PurePosixPath, PureWindowsPath
import json
import re

MATHEMATICAL_KINDS = {'theorem', 'lemma', 'proposition', 'corollary', 'definition', 'remark'}
MODULE = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z')


def relative_source_path(value):
    """Require a portable source path before resolving it in the owning package."""
    if (not isinstance(value, str) or not value or '\\' in value
            or PureWindowsPath(value).drive or PurePosixPath(value).is_absolute()
            or any(part in ('', '.', '..') for part in value.split('/'))
            or not value.endswith('.lean')):
        raise ValueError('Invalid relative Lean source path: ' + repr(value))
    return value


def module_from_library_path(value):
    relative_source_path(value)
    if value.startswith('packages/formalisation/'):
        value = value[len('packages/formalisation/'):]
    return value[:-5].replace('/', '.')


def validate_manuscript_map(value):
    """Check both collections without claiming that the library supplies the application."""
    if not isinstance(value, dict) or not isinstance(value.get('labels'), list):
        raise ValueError('Manuscript map requires a labels list.')
    expected = value.get('labelled_mathematical_item_count')
    if type(expected) is not int or expected < 0:
        raise ValueError('Manuscript map lacks its mathematical-item count.')
    seen = set()
    for row in value['labels']:
        if not isinstance(row, dict) or not isinstance(row.get('label'), str) or not row['label']:
            raise ValueError('Invalid manuscript label row.')
        if row['label'] in seen:
            raise ValueError('Duplicate manuscript label: ' + row['label'])
        seen.add(row['label'])
        if not isinstance(row.get('kind'), str) or not isinstance(row.get('summary'), str):
            raise ValueError('Manuscript row lacks kind/summary: ' + row['label'])
        if 'number' not in row:
            raise ValueError('Manuscript row lacks number: ' + row['label'])
        for category in ('providers', 'application_providers'):
            if not isinstance(row.get(category), list):
                raise ValueError('Missing or invalid ' + category + ': ' + row['label'])
            identities = set()
            for provider in row[category]:
                if not isinstance(provider, dict) or not all(
                        isinstance(provider.get(key), str) and provider[key].strip()
                        for key in ('module', 'declaration')):
                    raise ValueError('Invalid ' + category + ' entry: ' + row['label'])
                module, declaration = provider['module'], provider['declaration']
                if not MODULE.fullmatch(module) or any(c.isspace() for c in declaration):
                    raise ValueError('Invalid provider module or declaration: ' + row['label'])
                identity = (module, declaration)
                if identity in identities:
                    raise ValueError('Duplicate provider in ' + row['label'] + ': ' + declaration)
                identities.add(identity)
                if category == 'providers':
                    if module.split('.')[0] not in ('ModularRep', 'Formalisation'):
                        raise ValueError('An application provider is not supplied by this library: ' + module)
                    if module_from_library_path(provider.get('path')) != module:
                        raise ValueError('Local provider module/path mismatch: ' + module)
                elif (set(provider) != {'module', 'declaration', 'package',
                                       'provided_by_standalone_library', 'current_compilation'}
                        or module.split('.')[0] != 'ManuscriptIBAW'
                        or not declaration.startswith('ManuscriptIBAW.')
                        or provider.get('package') != 'separate manuscript application'
                        or provider.get('provided_by_standalone_library') is not False
                        or provider.get('current_compilation') != 'not_claimed_by_this_map'):
                    raise ValueError('Invalid separate application classification: ' + module)
    actual = sum(row['kind'] in MATHEMATICAL_KINDS for row in value['labels'])
    if actual != expected:
        raise ValueError('Manuscript mathematical-item count does not match its rows.')
    if not value['labels'] and value.get('status') != 'no_manuscript_association':
        raise ValueError('An empty map is not a completed manuscript projection.')
    return value


def load_manuscript_map(path):
    return validate_manuscript_map(json.loads(Path(path).read_text(encoding='utf-8')))


def validate_manuscript_provider(provider, row):
    """Check an explicit lexical status or preserve pending compiler resolution."""
    def status_kind(value):
        if isinstance(value, str):
            if value in ('source_lexical', 'source_lexical_only'):
                return 'lexical'
            if value == 'compiler_name_resolution_pending':
                return 'pending'
        raise ValueError('Missing or unknown manuscript declaration check: ' + repr(value))

    check = provider.get('declaration_presence_check')
    kind = status_kind(check)
    if 'declaration_check' in provider and status_kind(provider['declaration_check']) != kind:
        raise ValueError('Conflicting manuscript declaration checks: ' + repr(check)
                         + ' and ' + repr(provider['declaration_check']))
    if kind == 'pending':
        return check
    line = provider.get('line')
    if type(line) is not int or line < 1:
        raise ValueError('Invalid manuscript provider line: ' + provider['declaration'])
    matches = [declaration for declaration in row.get('declarations', [])
               if declaration.get('qualified_name_candidate') == provider['declaration']
               and declaration.get('line') == line]
    if not matches:
        raise ValueError('Manuscript provider name/line mismatch: ' + provider['declaration'])
    return check


def validate_local_providers(mapping, lookup):
    """Validate local providers; external references require the application checker."""
    validate_manuscript_map(mapping)
    counts = {'lexical': 0, 'pending': 0, 'external_references': 0}
    for item in mapping['labels']:
        counts['external_references'] += len(item['application_providers'])
        for provider in item['providers']:
            row = lookup.get(provider['module'])
            if row is None or row.get('path') != provider['path']:
                raise ValueError('Manuscript provider module/path missing from catalogue: '
                                 + provider['module'])
            check = validate_manuscript_provider(provider, row)
            counts['pending' if check == 'compiler_name_resolution_pending' else 'lexical'] += 1
    return counts
