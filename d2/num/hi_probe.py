"""Probe the RANK/HIGH payload: source_mass semantics + window per component."""
import os
import json
from pathlib import Path

BASE = Path(os.environ.get("PG182_D1_DATA", Path(__file__).resolve().parents[2] / "d1/frozen/extracted")) / "prime-gaps-external-182/snapshot/prime_gaps_20260903"
cands = list(BASE.rglob("fine_coarse_inner_sources_n393216.json"))
print("found:", cands)
p = cands[0]
d = json.loads(p.read_text())
print("root keys:", list(d))
for k, v in d.items():
    if isinstance(v, list):
        print(f"  {k}: list[{len(v)}]")
    elif isinstance(v, dict):
        print(f"  {k}: dict[{len(v)}] {list(v)[:12]}")
    else:
        print(f"  {k}: {repr(v)[:120]}")
comps = d.get("components") or d.get("results") or d.get("rows")
print("=== first component ===")
c0 = comps[0]
for k, v in c0.items():
    print(f"  {k}: {json.dumps(v)[:220] if isinstance(v,(dict,list)) else repr(v)[:200]}")
