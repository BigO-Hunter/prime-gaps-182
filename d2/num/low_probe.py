"""Probe the LOW row payload structure (D2b). Binary discipline: JSON parse only, print shape."""
import os
import json
import sys
from pathlib import Path

BASE = Path(os.environ.get("PG182_D1_DATA", Path(__file__).resolve().parents[2] / "d1/frozen/extracted")) / "prime-gaps-external-182/snapshot/prime_gaps_20260903/experiments"
FILES = {
    "g3g5g6": BASE / "variational_routes/fine_coarse_inner_low_v3_g3g5g6_n393216_b48.json",
    "g4": BASE / "tuple_geometry/fine393216_G4_low_v3.json",
    "c": BASE / "analytic_support/fine_C_low_v3_n393216.json",
}


def shape(o, depth=0, name="root"):
    pad = "  " * depth
    if isinstance(o, dict):
        print(f"{pad}{name}: dict[{len(o)}] keys={list(o)[:14]}")
        if depth < 2:
            for k, v in list(o.items())[:6]:
                shape(v, depth + 1, str(k))
    elif isinstance(o, list):
        print(f"{pad}{name}: list[{len(o)}]")
        if o and depth < 2:
            shape(o[0], depth + 1, "[0]")
    else:
        s = repr(o)
        print(f"{pad}{name}: {type(o).__name__} {s[:90]}")


for tag, p in FILES.items():
    print("=" * 70)
    print(tag, p.name, p.stat().st_size)
    d = json.loads(p.read_text())
    shape(d)
