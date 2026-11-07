"""Reconcile 94 slope!=0 covers vs 64 inner-low: where do the other 30 live?"""
import json
from pathlib import Path

BASE = Path.home() / "bigo-campaign/pg182-d1/frozen/extracted/prime-gaps-external-182/snapshot/prime_gaps_20260903/experiments"
# outer low stages mentioned by D1: G1/G2 low
cands = sorted(BASE.rglob("*outer*low*.json")) + sorted(BASE.rglob("*low*outer*.json"))
seen = set()
for p in cands:
    if p in seen:
        continue
    seen.add(p)
    try:
        d = json.loads(p.read_text())
    except Exception as e:
        print(p.name, "UNPARSED", e)
        continue
    keys = list(d)[:8]
    n = 0
    kinds = {}
    slopes = set()
    for key in ("results", "components", "groups", "stages"):
        v = d.get(key)
        if isinstance(v, list):
            n = max(n, len(v))
            for it in v:
                if isinstance(it, dict):
                    k = it.get("kind") or (it.get("group") or {}).get("role") or "?"
                    kinds[k] = kinds.get(k, 0) + 1
                    par = it.get("parameters") or {}
                    s = par.get("slope")
                    if s is not None:
                        slopes.add(str(s))
    print(f"{p.parent.name}/{p.name}: keys={keys[:6]} n={n} kinds={kinds} slopes={sorted(slopes)[:4]}")
