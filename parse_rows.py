import re, json
from fractions import Fraction

src = open('/Users/dmitri.arkhipov/bigo-campaign/pg182-r2/prime-gaps-lean/formal/SourceData182.lean').read()
start = src.index('def trialInnerCertificates')
arr = src[start:]
i = arr.index('![')+2
depth = 0; recs = []; cur = ''
for c in arr[i:]:
    if c == '{':
        depth += 1
        if depth == 1: cur = ''; continue
    elif c == '}':
        depth -= 1
        if depth == 0: recs.append(cur); cur = ''; continue
    elif c == ']' and depth == 0:
        break
    if depth >= 1: cur += c
print('inner records:', len(recs))
def field(rec, name):
    m = re.search(re.escape(name) + r' := ', rec)
    if not m: return None
    s = rec[m.end():]
    out = ''; d = 0
    for c in s:
        if c in '[{(': d += 1
        elif c in ']})': d -= 1
        if c == ',' and d == 0: break
        out += c
    return out.strip()
rows = []
for idx, r in enumerate(recs):
    cover = field(r, 'cover')
    kind = field(cover, 'kind').strip()
    pieces = field(cover, 'pieces') or ''
    npieces = len(re.findall(r'⟨[^⟨⟩]*⟩', pieces))
    fam = field(cover, 'family')
    fu = Fraction(field(r,"faceUpper").strip("() ").replace(" ",""))
    rows.append(dict(idx=idx, kind=kind, family=fam, npieces=npieces,
                     faceUpper=f"{fu.numerator}/{fu.denominator}"))
r2 = [r for r in rows if r['kind']=='.rankTwo']
print('rankTwo inner rows:', len(r2))
r2s = sorted(r2, key=lambda r: (r['npieces'], int(r['family'])))
for r in r2s[:15]: print(r['idx'], 'family', r['family'], 'pieces', r['npieces'])
json.dump(rows, open('inner_rows.json','w'), indent=1)
