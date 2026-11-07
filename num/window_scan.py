"""D2b: authoritative window scan from the certificate source (line-based, no backtracking)."""
import re
from fractions import Fraction as Q
from pathlib import Path

SRC = Path.home() / "bigo-campaign/pg182-d1/frozen/extracted/prime-gaps-external-182/target/SourceData182.lean"
ZETA = Q(1379373467, 1312494500)
HQ = ZETA / 393216

kind_re = re.compile(r"kind := \.(\w+)")
slope_re = re.compile(r"slope := (\d+)")
piece_re = re.compile(r"⟨(\d+), (\d+),")
head_re = re.compile(r"^def (trialOuterCertificates|trialInnerCertificates)")

block = None
rows = {60: [], 137: []}
n = {60: 0, 137: 0}
for line in SRC.read_text().splitlines():
    m = head_re.match(line)
    if m:
        block = 60 if "Outer" in m.group(1) else 137
        continue
    if block is None:
        continue
    k = kind_re.search(line)
    if not k:
        continue
    s = slope_re.search(line)
    ps = [(int(a), int(b)) for a, b in piece_re.findall(line)]
    if not ps:
        continue
    n[block] += 1
    rows[block].append((k.group(1), int(s.group(1)) if s else None,
                        min(a for a, _ in ps), max(b for _, b in ps)))

for b in (60, 137):
    print(f"Fin {b}: {n[b]} records with pieces + kind")
    agg = {}
    for kind, slope, lo, hi in rows[b]:
        a = agg.setdefault(kind, dict(n=0, lo=[], hi=[], sl=set()))
        a["n"] += 1
        a["lo"].append(lo * HQ)
        a["hi"].append(hi * HQ)
        a["sl"].add(slope)
    for kind, a in sorted(agg.items()):
        print(f"  {kind:8s} n={a['n']:3d}  window=[{float(min(a['lo'])):.4e},{float(max(a['hi'])):.4e}]"
              f"  all_hi<=zeta={all(h <= ZETA for h in a['hi'])}"
              f"  slope range {min(x for x in a['sl'] if x is not None)}..{max(x for x in a['sl'] if x is not None)}"
              f"  slope0={sum(1 for x in a['sl'] if x == 0)}")

topsl = [hi * HQ for kind, slope, lo, hi in rows[137] if kind == "low"]
topsr = [hi * HQ for kind, slope, lo, hi in rows[137] if kind in ("rankTwo", "high")]
print(f"\ninner .low  n={len(topsl)} max window top={float(max(topsl)):.6f} "
      f"= {float(max(topsl)/ZETA):.4f}*zeta  headroom {float(ZETA/max(topsl)):.3f}x")
print(f"inner rank/high n={len(topsr)} max window top={float(max(topsr)):.6f} "
      f"= {float(max(topsr)/ZETA):.4f}*zeta  headroom {float(ZETA/max(topsr)):.3f}x")
print(f"zeta={float(ZETA):.6f}  hq={float(HQ):.6e}")
print(f"top low window exact: {max(topsl)}")
