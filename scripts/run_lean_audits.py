"""Build the configured audits' imports, then elaborate the audit source files."""
from pathlib import Path
import json
import subprocess


def audit_targets(root):
    library = root / 'packages' / 'ModularRep'
    record = json.loads((library / 'audit-targets.json').read_text(encoding='utf-8'))
    targets = [library / p for p in record['scripts']]
    targets.append(root / 'ManuscriptIBAW' / 'MainAudit.lean')
    return [path.relative_to(root).as_posix() for path in targets]


def dependency_modules(root, targets):
    # --deps-json uses the pinned compiler's header parser without loading the
    # imports. It handles comments and import modifiers, and works before the
    # missing audit dependencies have been compiled. Lake uses this same parser.
    parsed = subprocess.run(['lean', '--deps-json', *targets], cwd=root,
                            check=True, capture_output=True, text=True, encoding='utf-8')
    payload = json.loads(parsed.stdout)
    rows = payload.get('imports') if isinstance(payload, dict) else None
    if not isinstance(rows, list) or len(rows) != len(targets):
        raise ValueError('Lean returned an incomplete audit import inventory.')
    modules = set()
    for target, row in zip(targets, rows):
        if not isinstance(row, dict) or row.get('errors') != []:
            raise ValueError(f'Cannot read imports of {target}: {row!r}')
        result = row.get('result')
        imports = result.get('imports') if isinstance(result, dict) else None
        if not isinstance(imports, list):
            raise ValueError(f'Lean returned no import list for {target}.')
        for item in imports:
            module = item.get('module') if isinstance(item, dict) else None
            if not isinstance(module, str) or not module:
                raise ValueError(f'Lean returned an invalid import for {target}.')
            modules.add(module)
    library = subprocess.run(['lean', '--print-libdir'], cwd=root, check=True,
                             capture_output=True, text=True, encoding='utf-8')
    core = Path(library.stdout.strip())
    if not core.is_absolute() or not core.is_dir():
        raise ValueError('Lean returned an invalid standard-library directory.')
    # Init is implicit unless a header uses `prelude`; explicit imports of Lean
    # or Std are also already provided by this toolchain, rather than Lake targets.
    return sorted(module for module in modules
                  if not core.joinpath(*module.split('.')).with_suffix('.olean').is_file())


def run_audits(root):
    root = Path(root).resolve()
    targets = audit_targets(root)
    modules = dependency_modules(root, targets)
    if modules:
        print(f'Building {len(modules)} audit dependency modules and their imports', flush=True)
        # A root `lake build` need not reach these modules. The explicit module
        # facet also avoids ambiguity with a library or executable of the same name.
        subprocess.run(['lake', 'build', *('+' + name + ':olean' for name in modules)],
                       cwd=root, check=True)
    for relative in targets:
        print('Checking ' + relative, flush=True)
        subprocess.run(['lake', 'env', 'lean', '--trust=0', '--threads=1', relative],
                       cwd=root, check=True)
    print('Configured library and main application audits passed. '
          'The additional exhaustive declaration audit is not reproduced.')


def main():
    run_audits(Path(__file__).resolve().parents[1])


if __name__ == '__main__':
    main()
