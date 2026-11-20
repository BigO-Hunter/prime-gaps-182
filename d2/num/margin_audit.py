#!/usr/bin/env python3
"""margin_audit.py — measure which inner rows the frozen table can close.

The composition's Layer-I split is

    innerMass j  <=  envSup j * (cell mass)        (hrow)
    envSup j * hq <= faceUpper j                  (hmargin)

`hq = zeta/393216` is the proved uniform cell mass.  `hmargin` is pure rational
arithmetic *once an envelope value is known*, so the question this script answers
is: **which recorded table value can serve as `envSup`?**

Candidate: the cover's `witnessUpper` (the retained-maximum affine-prefix witness,
the D3 / audit-item-3 datum).  Verdict: it satisfies the margin on the 73
`rankTwo`/`high` rows and on none of the 64 `.low` rows, where it misses by
19-27 orders of magnitude -- so no rounding, convention, or chunking can recover
those rows: their envelope is simply not a recorded table value.

Exit code 0 iff the partition is exactly (all non-low rows hold) and (no low row
holds), which is the invariant `num/emit_table.py` asserts before emitting.

Usage: python3 num/margin_audit.py
"""
import os
import math
import re
import sys
from fractions import Fraction as Q
from pathlib import Path

SRC = (Path(os.environ.get("PG182_D1_DATA", Path(__file__).resolve().parents[2] / "d1/frozen/extracted"))
       / "prime-gaps-external-182/target/SourceData182.lean")
ZETA = Q(1379373467, 1312494500)
HQ = ZETA / 393216


def parse_q(text: str) -> Q:
    m = re.fullmatch(r"\(?(-?\d+)(?: / (\d+))?\)?", text.strip())
    if not m:
        raise ValueError(text)
    return Q(int(m.group(1)), int(m.group(2) or 1))


def main() -> int:
    text = SRC.read_text()
    i = text.index("def trialInnerCertificates")
    blk = text[i:blk_end] if (blk_end := text.find("\nend ", i)) > 0 else text[i:]

    def vals(name: str) -> list[Q]:
        return [parse_q(m) for m in re.findall(name + r" := \(?([^,}\)]+)", blk)]

    face, wit = vals("faceUpper"), vals("witnessUpper")
    kind = re.findall(r"kind := \.(\w+)", blk)
    assert len(face) == len(wit) == len(kind) == 137

    hold = [j for j in range(137) if wit[j] * HQ <= face[j]]
    low = [j for j in range(137) if kind[j] == "low"]
    nonlow = [j for j in range(137) if kind[j] != "low"]

    print(f"witnessUpper * hq <= faceUpper holds on {len(hold)}/137 rows")
    print(f"  rankTwo/high rows: {len(nonlow)}, of which hold: {len([j for j in hold if j in nonlow])}")
    print(f"  low rows:          {len(low)}, of which hold: {len([j for j in hold if j in low])}")

    short = [(face[j] / (wit[j] * HQ), j) for j in low]
    worst, worst_j = min(short)
    best, best_j = max(short)
    print(f"  low-row shortfall (certificate/required): worst 10^{math.log10(float(worst)):.1f}"
          f" (row {worst_j}), best 10^{math.log10(float(best)):.1f} (row {best_j})")
    print(f"    i.e. the frozen witness overshoots the low certificates by "
          f"{float(1/best):.0f}x .. {float(1/worst):.0f}x -- not a rounding gap")

    ok = (len(hold) == len(nonlow)) and all(j in hold for j in nonlow)
    print(f"\npartition invariant {'HOLDS' if ok else 'BROKEN'}: "
          "the margin is a table fact exactly on the rankTwo/high rows")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
