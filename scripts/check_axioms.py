#!/usr/bin/env python3
"""Fail if a public declaration has a nonstandard axiom dependency."""
import re
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[1]
certificate = root / 'TransparencyLean' / 'Certificate.lean'
expected = set(re.findall(r'^#print axioms (\S+)', certificate.read_text(), re.MULTILINE))
log = Path(sys.argv[1]).read_text()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
found = {}
for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
    found[match.group(1)] = {x.strip() for x in match.group(2).split(',') if x.strip()}
for match in re.finditer(r"'([^']+)' does not depend on any axioms", log):
    found[match.group(1)] = set()

if set(found) != expected:
    raise SystemExit(f'Audit coverage mismatch: missing={expected-set(found)}, extra={set(found)-expected}')
for name, axioms in found.items():
    if not axioms <= allowed:
        raise SystemExit(f'Unexpected axioms for {name}: {axioms-allowed}')

for path in [root / 'TransparencyLean.lean', *sorted((root / 'TransparencyLean').rglob('*.lean'))]:
    code = re.sub(r'/\-.*?\-/|--[^\n]*', '', path.read_text(), flags=re.DOTALL)
    if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|skipKernelTC)\b', code):
        raise SystemExit(f'Forbidden proof escape or placeholder token: {path.relative_to(root)}')

print(f'PASS: {len(expected)} public declarations audited; only standard Lean axioms; no proof placeholders.')
