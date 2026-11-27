"""Deeper probe: the low payload components + radial window shape."""
import os
import json
from pathlib import Path

BASE = Path(os.environ.get("PG182_D1_DATA", Path(__file__).resolve().parents[2] / "d1/frozen/extracted")) / "prime-gaps-external-182/snapshot/prime_gaps_20260903/experiments"
FILES = {
    "g3g5g6": BASE / "variational_routes/fine_coarse_inner_low_v3_g3g5g6_n393216_b48.json",
    "g4": BASE / "tuple_geometry/fine393216_G4_low_v3.json",
    "c": BASE / "analytic_support/fine_C_low_v3_n393216.json",
}

for tag, p in FILES.items():
    d = json.loads(p.read_text())
    print("=" * 78)
    print(tag, "| keys:", list(d))
    for k, v in d.items():
        if isinstance(v, list):
            print(f"  {k}: list[{len(v)}]")
        elif isinstance(v, dict):
            print(f"  {k}: dict[{len(v)}] {list(v)[:10]}")
        else:
            print(f"  {k}: {repr(v)[:100]}")
