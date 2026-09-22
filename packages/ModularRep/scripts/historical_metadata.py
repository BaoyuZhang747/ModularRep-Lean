"""Validate the identity, not the mathematics, of retained compiler metadata.

The historical receipt inputs are not distributed in the public package.
This optional validation branch is used only when those inputs are supplied.
"""
import hashlib
import json
from pathlib import Path

MODE = 'partial-retained-metadata-current-source-identities'


def validate_retained_declarations(root, data):
    root = Path(root).resolve()
    binding = data.get('historical_declarations', {})
    path = (root / binding.get('path', '')).resolve()
    if not path.is_relative_to(root) or not path.is_file():
        raise ValueError('Missing in-package historical declaration record.')
    if hashlib.sha256(path.read_bytes()).hexdigest() != binding.get('sha256'):
        raise ValueError('Historical declaration record changed.')
    original = json.loads(path.read_text(encoding='utf-8'))
    old = {row['module']: row for row in original['modules']}
    seen = set()
    for row in data.get('modules', []):
        name = row['module']
        if name in seen or row != old.get(name):
            raise ValueError('Retained declaration metadata is not an unchanged record: ' + name)
        seen.add(name)
        source = (root / row['path']).resolve()
        if not source.is_relative_to(root) or not source.is_file():
            raise ValueError('Invalid retained declaration source: ' + name)
        if hashlib.sha256(source.read_bytes()).hexdigest() != row['source_sha256']:
            raise ValueError('Retained declaration source changed: ' + name)
    pending = data.get('pending_modules', [])
    if not isinstance(pending, list) or set(pending) & seen:
        raise ValueError('Invalid pending declaration metadata list.')
    return data


def historical_validation_files(root):
    """Authenticate withdrawn receipts without treating them as current checks."""
    root = Path(root).resolve()
    index = root / 'validation/applicability.json'
    if not index.exists():
        return set()
    value = json.loads(index.read_text(encoding='utf-8'))
    if value.get('status') != 'historical-receipts-not-applicable-to-current-sources':
        raise ValueError('Unknown validation receipt applicability status.')
    result = set()
    for entry in value.get('receipts', []):
        p = (root / entry['path']).resolve()
        if not p.is_relative_to(root / 'validation') or not p.is_file():
            raise ValueError('Invalid historical validation path.')
        if hashlib.sha256(p.read_bytes()).hexdigest() != entry['sha256']:
            raise ValueError('Preserved historical receipt changed: ' + entry['path'])
        result.add(p)
    return result
