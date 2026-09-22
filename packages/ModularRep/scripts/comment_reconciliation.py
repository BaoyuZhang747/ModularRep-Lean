"""Authenticate a restricted comment edit; this is not a Lean compilation.

The historical receipt inputs are not distributed in the public package.
This optional validation branch is used only when those inputs are supplied.

Historical receipts remain immutable. No string literal, code, import, command,
identifier, or existing non-comment byte is permitted to change. Interior edits
in files containing interpolation syntax require another validation route.
"""
from pathlib import Path
import hashlib
import json
import re
import tomllib

MODE = 'comment-only-reconciled-historical-compilation'
FRESH_MODE = 'fresh-selected-source-replay-after-comment-reconciliation'
REPLAY_ANCHOR = 'ModularRep/CurrentManuscriptReduction.lean'


def fail(message):
    raise ValueError('Comment reconciliation: ' + message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def contained_file(root, relative):
    root = Path(root).resolve()
    p = root / relative
    if Path(relative).is_absolute() or not p.resolve().is_relative_to(root):
        fail('path escapes distribution: ' + relative)
    if not p.is_file() or p.is_symlink():
        fail('missing or linked evidence: ' + relative)
    return p


def ordinary_footer(data):
    # Precisely one ordinary block comment, separated from old EOF by newline.
    if not re.fullmatch(rb'(?:\r?\n)+/-(?![-!])(?:(?!/-|-/)[\s\S])*-/(?:\r?\n)*', data):
        fail('footer is not one closed ordinary comment')


def comments(data):
    """Return outer block-comment spans; strings and quoted names are retained.

    Fail closed on interpolated strings and character literals instead of
    approximating their grammar. Apostrophes inside ordinary identifiers do
    not matter, but a quoted scalar or a character escape requires another
    validation route. The check is deliberately conservative even in comments.
    This restriction only applies when existing comment interiors are edited.
    """
    if re.search(rb'\b[A-Za-z_][A-Za-z0-9_]*!\s*"', data):
        fail('interpolation requires separate inspection for interior edits')
    decoded = data.decode('utf-8')
    if re.search(r"'[^'\\\r\n]'", decoded) or re.search(r"'\\", decoded):
        fail('character literals require separate inspection for interior edits')
    spans = []
    i = 0
    while i < len(data):
        if data.startswith(b'--', i):
            e = data.find(b'\n', i)
            i = len(data) if e < 0 else e
        elif data.startswith(b'/-', i):
            start = i
            i += 2
            depth = 1
            while i < len(data) and depth:
                if data.startswith(b'/-', i): depth += 1; i += 2
                elif data.startswith(b'-/', i): depth -= 1; i += 2
                else: i += 1
            if depth: fail('unterminated historical block comment')
            spans.append((start, i))
        elif data.startswith('«'.encode(), i):
            e = data.find('»'.encode(), i + 2)
            if e < 0: fail('unterminated quoted identifier')
            i = e + 2
        elif data[i:i+1] == b'r' and (i == 0 or not re.match(rb'[A-Za-z0-9_]', data[i-1:i])):
            m = re.match(rb'r(#{0,})"', data[i:])
            if not m: i += 1; continue
            end = b'"' + m[1]
            e = data.find(end, i + len(m[0]))
            if e < 0: fail('unterminated raw string')
            i = e + len(end)
        elif data[i:i+1] == b'"':
            if i and data[i-1:i] == b'!':
                fail('interpolation requires separate inspection for interior edits')
            i += 1
            while i < len(data):
                if data[i:i+1] == b'\\': i += 2
                elif data[i:i+1] == b'"': i += 1; break
                else: i += 1
            else: fail('unterminated string')
        else:
            i += 1
    return spans


def masked_lines(data, spans):
    b = bytearray(data)
    for start, end in spans:
        for i in range(start, end):
            if b[i] not in (10, 13): b[i] = 32
    return [line.rstrip(b' ') for line in bytes(b).splitlines(keepends=False)]


def reconstruct_original(current, record):
    if sha(current) != record['current_source_sha256']:
        fail('current source hash mismatch: ' + record['path'])
    footer = record.get('footer', '').encode('utf-8')
    if footer:
        ordinary_footer(footer)
        if not current.endswith(footer): fail('footer suffix mismatch')
        body = current[:-len(footer)]
    else:
        body = current
    edits = record.get('edits', [])
    previous_end = -1
    delta = 0
    locations = []
    for edit in edits:
        start = edit['old_start_byte']
        before, after = edit['before'].encode('utf-8'), edit['after'].encode('utf-8')
        if type(start) is not int or start < 0 or start < previous_end or not before:
            fail('invalid or overlapping edit spans')
        if any(marker in value for value in (before, after) for marker in (b'/-', b'-/')):
            fail('interior edits may not alter comment delimiters')
        locations.append((start, start + delta, before, after))
        previous_end = start + len(before)
        delta += len(after) - len(before)
    old = body
    for start, new_start, before, after in reversed(locations):
        if new_start < 0 or old[new_start:new_start+len(after)] != after:
            fail('replacement bytes do not match')
        old = old[:new_start] + before + old[new_start+len(after):]
    if sha(old) != record['compiled_source_sha256']:
        fail('reconstructed compiled bytes do not match authenticated hash')
    if edits:
        spans = comments(old)
        for start, _, before, _ in locations:
            if not any(a + (3 if old[a:a+3] in (b'/--', b'/-!') else 2) <= start and start+len(before) <= b-2 for a,b in spans):
                fail('edit is outside an existing block-comment interior')
        if masked_lines(old, spans) != masked_lines(body, comments(body)):
            fail('non-comment bytes or code line/column positions changed')
    return old


def load_manifest(root, receipt):
    spec = receipt['comment_reconciliation']
    path = contained_file(root, spec['path'])
    if sha(path.read_bytes()) != spec['sha256']: fail('manifest hash mismatch')
    manifest = json.loads(path.read_text(encoding='utf-8'))
    if manifest.get('schema_version') != 1 or manifest.get('mode') != MODE:
        fail('unsupported manifest schema/mode')
    rows = manifest['files']
    if len({r['path'] for r in rows}) != len(rows): fail('duplicate manifest source')
    return {r['path']: r for r in rows}


def validate_receipt(root, receipt):
    """Validate every inherited row against its immutable exact old receipt."""
    if receipt.get('mode') != MODE:
        fail('unsupported receipt mode')
    spec = receipt['compiled_baseline_receipt']
    if not spec['path'].startswith('validation/comment-baseline/'):
        fail('baseline must be explicitly historical')
    data = contained_file(root, spec['path']).read_bytes()
    if sha(data) != spec['sha256']: fail('baseline receipt hash mismatch')
    baseline = json.loads(data)
    if baseline.get('status') != 'passed': fail('baseline did not pass')
    if baseline.get('mode') == MODE: fail('chained comment reconciliation is not supported')
    if receipt.get('config_sha256', {}) != baseline.get('config_sha256', {}):
        fail('configuration differs from compiled baseline')
    previous = {(r['module'], r['path']): r for r in baseline['checked']}
    now = {(r['module'], r['path']): r for r in receipt['checked']}
    if len(previous) != len(baseline['checked']) or len(now) != len(receipt['checked']) or previous.keys() != now.keys():
        fail('module/path selection changed')
    manifest = load_manifest(root, receipt)
    mutable = {'source_sha256', 'validation_origin'}
    for key, row in now.items():
        old = previous[key]
        if old.get('exit_code') != 0: fail('unsuccessful baseline compilation')
        for k, v in old.items():
            if k not in mutable and row.get(k) != v: fail('altered historical evidence: ' + k)
        if row.get('validation_origin') != MODE: fail('row lacks explicit comment-only origin')
        if 'validation_origin' in old and row.get('compiled_validation_origin') != old['validation_origin']:
            fail('historical validation origin was not preserved')
        if row.get('compiled_source_sha256') != old['source_sha256']:
            fail('compiled source hash differs from baseline')
        record = manifest.get(row['path'])
        if record is None: fail('missing exact source transformation')
        if record['compiled_source_sha256'] != old['source_sha256'] or record['current_source_sha256'] != row['source_sha256']:
            fail('transformation/source receipt mismatch')
        reconstruct_original(contained_file(root,row['path']).read_bytes(), record)
    return baseline


def validate_all_transforms(root, receipt, expected_paths):
    manifest = load_manifest(root, receipt)
    if set(manifest) != set(expected_paths):
        fail('transformation manifest does not cover the exact owned Lean file set')
    for path, row in manifest.items():
        reconstruct_original(contained_file(root, path).read_bytes(), row)


def fresh_selection(root, source_receipt, audit_targets):
    manifest = load_manifest(root, source_receipt)
    interior = sorted(path for path, row in manifest.items() if row.get('edits') and path not in audit_targets)
    if REPLAY_ANCHOR not in manifest:
        fail('missing integrated reduction replay anchor')
    return list(audit_targets) + interior + ([] if REPLAY_ANCHOR in interior else [REPLAY_ANCHOR])


def replay_command(root, relative):
    config = ('packages/formalisation/lakefile.toml' if relative.startswith('packages/formalisation/') else 'lakefile.toml')
    options = tomllib.loads(contained_file(root, config).read_text(encoding='utf-8'))['leanOptions']
    result = ['lean', '--trust=0', '--threads=1', '-M8192']
    def flatten(prefix, value):
        if isinstance(value, dict):
            for key, child in value.items(): flatten(prefix+[key], child)
        else:
            literal = str(value).lower() if isinstance(value, bool) else str(value)
            result.append('-D'+'.'.join(prefix)+'='+literal)
    flatten([], options)
    return result + ['--root=.', relative]


def validate_fresh_checks(root, fresh, source_receipt, audit_targets):
    """Bind fresh source replays separately from retained compilation objects."""
    if fresh.get('mode') != FRESH_MODE or fresh.get('status') != 'passed':
        fail('fresh selected source replays did not pass in the explicit mode')
    if fresh.get('source_object_fingerprint_sha256') != source_receipt.get('source_object_fingerprint_sha256'):
        fail('fresh replay fingerprint does not match the current source/object set')
    if fresh.get('historical_source_receipt_sha256') != source_receipt['compiled_baseline_receipt']['sha256']:
        fail('fresh replay historical source receipt binding differs')
    if fresh.get('config_sha256') != source_receipt.get('config_sha256'):
        fail('fresh replay configuration binding differs')
    if [row['path'] for row in fresh['checked']] != fresh_selection(root, source_receipt, audit_targets):
        fail('fresh replay selection is not the exact approved selection')
    for row in fresh['checked']:
        if row.get('exit_code') != 0 or row.get('source_unchanged') is not True:
            fail('unsuccessful or mutated fresh replay source')
        if sha(contained_file(root, row['path']).read_bytes()) != row['source_sha256']:
            fail('fresh replay source bytes differ')
        if row.get('command') != replay_command(root, row['path']):
            fail('fresh replay command differs from required options')
        if not re.fullmatch(r'[0-9a-f]{64}', row.get('log_sha256', '')):
            fail('fresh replay log digest is invalid')


def declarations_from_baseline(root, source_receipt, baseline_spec):
    validate_receipt(root, source_receipt)
    if not baseline_spec['path'].startswith('validation/comment-baseline/'):
        fail('declaration baseline must be explicitly historical')
    raw = contained_file(root, baseline_spec['path']).read_bytes()
    if sha(raw) != baseline_spec['sha256']: fail('declaration baseline hash mismatch')
    old = json.loads(raw)
    if old.get('mode') == MODE: fail('chained declaration reconciliation is not supported')
    manifest = load_manifest(root, source_receipt)
    rows = []
    seen = set()
    for row in old['modules']:
        if row['module'] in seen: fail('duplicate historical declaration module')
        seen.add(row['module'])
        record = manifest.get(row['path'])
        if record is None or row['source_sha256'] != record['compiled_source_sha256']:
            fail('compiler declaration source does not match compiled baseline')
        reconstruct_original(contained_file(root,row['path']).read_bytes(), record)
        rows.append({**row, 'source_sha256':record['current_source_sha256'],
                     'compiled_source_sha256':row['source_sha256'], 'validation_origin':MODE})
    return {'schema_version':1, 'mode':MODE,
            'method':'Preserved compiler-resolved names and ranges from the authenticated earlier compilation. Exact restricted comment reconciliation preserves code line/column positions. This is not new ILean compilation or source-assumption authentication.',
            'compiled_baseline_declarations':baseline_spec,
            'comment_source_receipt':source_receipt['declaration_source_receipt_binding'],
            'modules':rows}


def validate_declarations(root, data):
    if data.get('mode') != MODE: fail('unsupported declaration reconciliation mode')
    spec = data['comment_source_receipt']
    raw = contained_file(root, spec['path']).read_bytes()
    if sha(raw) != spec['sha256']: fail('declaration/source receipt binding mismatch')
    receipt = json.loads(raw)
    # This binding is supplied for deterministic declaration reconstruction,
    # rather than embedded in the source receipt and causing a self-hash cycle.
    receipt['declaration_source_receipt_binding'] = spec
    expected = declarations_from_baseline(root, receipt, data['compiled_baseline_declarations'])
    if data != expected: fail('declaration inventory differs from authenticated preserved ranges')
