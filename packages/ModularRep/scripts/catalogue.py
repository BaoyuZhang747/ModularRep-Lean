#!/usr/bin/env python3
"""Lexical catalogue helpers retained for the public source checker.

Regeneration is disabled in this public copy: the development generator does
not reproduce the distributed catalogue from the supplied inputs. Use
python -B scripts/check_repository.py from the repository root to check sources.
For a pristine release export, use python -B scripts/verify_release.py instead.
Historical compiler receipt inputs are not distributed in the public package.
"""
from pathlib import Path
import sys
sys.dont_write_bytecode = True
import hashlib
import json
import re
import os
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    """Replace JSON atomically after flushing a complete same-directory temporary."""
    path = Path(path)
    payload = json.dumps(value, indent=2, ensure_ascii=False) + '\n'
    descriptor, temporary = tempfile.mkstemp(prefix='.atomic-json-', suffix='.tmp', dir=path.parent)
    try:
        with os.fdopen(descriptor, 'w', encoding='utf-8') as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        for attempt in range(6):
            try:
                os.replace(temporary, path)
                break
            except PermissionError:
                if attempt == 5:
                    raise
                time.sleep(0.02 * (attempt + 1))
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def code_only(text):
    """Blank nested comments and string literals, preserving line positions."""
    out = list(text)
    i, depth, quoted = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2
            elif text.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if text[i] != '\n': out[i] = ' '
                i += 1
        elif quoted:
            if text[i] == '\\':
                out[i] = ' '; i += 1
                if i < len(text): out[i] = ' '; i += 1
            elif text[i] == '"':
                out[i] = ' '; quoted = False; i += 1
            else:
                if text[i] != '\n': out[i] = ' '
                i += 1
        elif text.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0: end = len(text)
            out[i:end] = ' ' * (end-i); i = end
        elif text[i] == '"':
            out[i] = ' '; quoted = True; i += 1
        else:
            i += 1
    return ''.join(out)


def public_files():
    paths = []
    for directory, directories, filenames in os.walk(ROOT):
        directories[:] = [name for name in directories if name not in
                           {'.lake', '.git', '__pycache__', 'verification-output'}]
        paths.extend(Path(directory)/name for name in filenames
                     if not (name.startswith('.atomic-json-') and name.endswith('.tmp')))
    return sorted(paths)


def source_paths():
    for path in public_files():
        if path.suffix != '.lean': continue
        rel = path.relative_to(ROOT)
        if rel.parts[0] == 'audits': continue
        yield path


def declaration_index(clean):
    """Lexical declared names, with explicit scope; generated declarations omitted."""
    result, scopes = [], []
    pattern = re.compile(r'^\s*(?P<mods>(?:(?:noncomputable|protected|private|unsafe|partial)\s+)*)'
                         r'(?:@\[[^\n]*\]\s*)?'
                         r'(?P<kind>theorem|lemma|def|abbrev|opaque|structure|class|inductive|axiom)'
                         r'\s+(?P<name>[^\s:(\[\{]+)')
    for number, line in enumerate(clean.splitlines(), 1):
        namespace = re.match(r'^\s*namespace\s+(\S+)', line)
        section = re.match(r'^\s*(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$', line)
        ending = re.match(r'^\s*end(?:\s+(\S+))?\s*$', line)
        if namespace:
            scopes.append(('namespace', namespace.group(1)))
        elif section:
            scopes.append(('section', section.group(1)))
        elif ending and scopes:
            scopes.pop()
        found = pattern.match(line)
        if found:
            name = found['name'].removesuffix('.')
            prefix = '.'.join(value for kind, value in scopes if kind == 'namespace')
            full = name.removeprefix('_root_.') if name.startswith('_root_.') else '.'.join(x for x in [prefix, name] if x)
            result.append({'kind': found['kind'], 'declared_name': name,
                           'qualified_name_candidate': full, 'line': number,
                           'visibility': 'private' if 'private' in found['mods'].split() else 'public'})
    return result


def module_name(path):
    relative = path.relative_to(ROOT)
    if relative.parts[:2] == ('packages', 'formalisation'):
        relative = Path(*relative.parts[2:])
    return relative.with_suffix('').as_posix().replace('/', '.')


def role(name):
    if name in {'ModularRep', 'ModularRep.PaperProofs', 'Formalisation'}:
        return 'compatibility-umbrella'
    if name in {'ModularRep.Library', 'ModularRep.Manuscript'}:
        return 'entry-point'
    if 'Dependenc' in name or name.endswith('ReductionLogic'):
        return 'dependency-ledger-no-mathematical-credit'
    if name.startswith('Formalisation.'):
        return 'retained-formalisation-library'
    if '.PaperProofs.' in name:
        return 'manuscript-and-general-source-extension'
    return 'general-library-and-source-interface'


def catalogue():
    rows = []
    for path in source_paths():
        clean = code_only(path.read_text(encoding='utf-8-sig'))
        name = module_name(path)
        rows.append({'module': name, 'path': path.relative_to(ROOT).as_posix(),
                     'sha256': sha256(path), 'role': role(name),
                     'imports': re.findall(r'^\s*(?:public\s+)?import\s+(\S+)', clean, re.M),
                     'declarations': declaration_index(clean),
                     'verification_status': 'see-verification-status.json'})
    return rows


def closure(rows, roots):
    lookup = {row['module']: row for row in rows}
    visited, visiting, ordered = set(), set(), []

    def visit(name):
        if name in visited or name not in lookup: return
        if name in visiting: raise ValueError('Import cycle: '+name)
        visiting.add(name)
        for dependency in lookup[name]['imports']: visit(dependency)
        visiting.remove(name); visited.add(name); ordered.append(name)

    for name in roots: visit(name)
    return ordered


def main():
    raise SystemExit(
        'Catalogue regeneration is disabled in this public source bundle. '
        'The public inputs do not reproduce the distributed catalogue. Run python -B scripts/check_repository.py from the repository root, or python -B scripts/verify_release.py for a pristine export.'
    )


if __name__ == '__main__':
    main()
