"""Offline source/inventory checks; not a Lean kernel or Comparator substitute."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def imports(text):
    return re.findall(r"(?m)^(?:public )?import ([\w.]+)\s*$", text)

def graph():
    return {str(p.relative_to(ROOT)).removesuffix('.lean').replace('/', '.').replace('\\', '.'):
            imports(p.read_text(encoding='utf-8')) for p in sorted(ROOT.glob('HamParity/*.lean'))}

def closure(deps, name):
    seen = set()
    def visit(n):
        if n in seen:
            return
        seen.add(n)
        for child in deps.get(n, []):
            visit(child)
    visit(name)
    return seen

def main():
    manifest = json.loads((ROOT/'verification/VERIFIED-SOURCE-MANIFEST.json').read_text())
    failures = []
    for item in manifest['files']:
        p = ROOT/item['path']
        if not p.is_file() or sha(p) != item['sha256'] or p.stat().st_size != item['bytes']:
            failures.append('verified inventory mismatch: '+item['path'])
    actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*.lean') if '.lake' not in p.parts}
    expected = {x['path'] for x in manifest['files'] if x['path'].endswith('.lean')}
    if actual != expected:
        failures.append('Lean inventory membership mismatch')
    deps = graph()
    solution = closure(deps, 'HamParity.RegistrySolution')
    if 'HamParity.RegistryChallenge' in solution:
        failures.append('circular Challenge import')
    for module, children in deps.items():
        p = ROOT/(module.replace('.', '/')+'.lean')
        text = p.read_text(encoding='utf-8')
        if not text.startswith('module\n') or len(text.splitlines()) > 10000:
            failures.append('module header/line gate: '+module)
        for child in children:
            if child.startswith('HamParity.') and child not in deps:
                failures.append('missing local dependency: '+child)
        if module in solution:
            # Supplementary lexical gate; the retained axiom audit is stronger.
            if re.search(r'\b(sorry|admit|axiom|native_decide|sorryAx)\b|Lean\.ofReduceBool', text):
                failures.append('review forbidden-token hit: '+module)
    challenge = ROOT/'HamParity/RegistryChallenge.lean'
    if len(challenge.read_text(encoding='utf-8').splitlines()) > 1000 or challenge.stat().st_size > 100*1024:
        failures.append('Challenge size gate')
    if any(x.startswith('HamParity') for x in deps['HamParity.RegistryChallenge']):
        failures.append('Challenge is not core/Std standalone')
    cfg = json.loads((ROOT/'comparator-finite-oracle.json').read_text())
    if cfg['definition_names'] != ['HamiltonicityOracle.query']:
        failures.append('definition hole mismatch')
    if set(cfg['permitted_axioms']) != {'propext','Quot.sound','Classical.choice'}:
        failures.append('axiom configuration mismatch')
    if len(cfg['theorem_names']) != 4:
        failures.append('target count mismatch')
    if (ROOT/'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.35.0-rc3':
        failures.append('toolchain mismatch')
    if json.loads((ROOT/'lake-manifest.json').read_text())['packages'] != []:
        failures.append('unexpected package dependency')
    result = {'kind':'offline packaging check, not proof verification', 'passed':not failures,
              'verified_files':len(manifest['files']), 'lean_files':len(actual),
              'solution_local_modules':len([x for x in solution if x in deps]),
              'dependency_graph':deps, 'failures':failures}
    out = ROOT/'.verification'
    out.mkdir(exist_ok=True)
    (out/'source-check.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k!='dependency_graph'},indent=2))
    return 0 if not failures else 1

if __name__ == '__main__':
    raise SystemExit(main())
