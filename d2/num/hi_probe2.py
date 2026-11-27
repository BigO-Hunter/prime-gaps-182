import os
import json
from pathlib import Path

p = Path(os.environ.get("PG182_D1_DATA", Path(__file__).resolve().parents[2] / "d1/frozen/extracted")) / "prime-gaps-external-182/snapshot/prime_gaps_20260903/experiments/analytic_support/fine_coarse_inner_sources_n393216.json"
d = json.loads(p.read_text())
g = d["groups"][0]
print("group keys:", list(g))
for k, v in g.items():
    if isinstance(v, list):
        print(f"  {k}: list[{len(v)}]")
    elif isinstance(v, dict):
        print(f"  {k}: dict[{len(v)}] {list(v)[:12]}")
    else:
        print(f"  {k}: {repr(v)[:160]}")
comp = (g.get("components") or g.get("results") or [])[0]
print("=== comp0 ===")
for k, v in comp.items():
    print(f"  {k}: {json.dumps(v)[:260] if isinstance(v,(dict,list)) else repr(v)[:200]}")
print("=== kinds ===")
print(json.dumps(d["kinds"], indent=1)[:900])
