"""Dump one low result entry + group shape (the radial window)."""
import json
from pathlib import Path

BASE = Path.home() / "bigo-campaign/pg182-d1/frozen/extracted/prime-gaps-external-182/snapshot/prime_gaps_20260903/experiments"
FILES = {
    "g3g5g6": BASE / "variational_routes/fine_coarse_inner_low_v3_g3g5g6_n393216_b48.json",
    "g4": BASE / "tuple_geometry/fine393216_G4_low_v3.json",
    "c": BASE / "analytic_support/fine_C_low_v3_n393216.json",
}

for tag, p in FILES.items():
    d = json.loads(p.read_text())
    print("=" * 78)
    print(tag, "results:", len(d["results"]))
    r0 = d["results"][0]
    print("result[0] keys:", list(r0))
    for k, v in r0.items():
        if isinstance(v, (dict, list)):
            print(f"  {k}: {type(v).__name__}[{len(v)}] {json.dumps(v)[:300]}")
        else:
            print(f"  {k}: {repr(v)[:160]}")
    if "group" in d:
        print("-- group --")
        print(json.dumps(d["group"], indent=1)[:2000])
    if "original_group" in d:
        print("-- original_group --")
        print(json.dumps(d["original_group"], indent=1)[:1200])
    print("-- limitations --")
    print(json.dumps(d.get("limitations"), indent=1)[:1200])
