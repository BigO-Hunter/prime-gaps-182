#!/usr/bin/env python3
"""Walk the Lean import closure of a target module and report `sorry`/`admit` occurrence sites.

Read-only. Used as corroborating evidence before the decisive `#print axioms` run.
"""
import os
import re
import sys
from pathlib import Path

WEIL = Path(os.environ.get("WEIL_VERIFY", str(Path(__file__).resolve().parent / "Weil")))
ROOTS = [WEIL / "Weil", WEIL / ".lake/packages/Stacks", WEIL / ".lake/packages/mathlib"]

IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_.']+)", re.M)
# A `sorry` token that is *code* rather than prose: it terminates a term or stands alone.
# Prose mentions ("a `sorry` definition", "sorry-free") are excluded by requiring the token to
# follow a term-introducing keyword or to be the whole line.
SORRY_RE = re.compile(
    r"(?:^|:=\s*by|:=|exact|apply|refine|·|;)\s*sorry\s*$"
    r"|^\s*sorry\s*$",
    re.M,
)


def module_file(mod: str) -> Path | None:
    rel = mod.replace(".", "/") + ".lean"
    for root in ROOTS:
        p = root / rel
        if p.is_file():
            return p
    return None


def closure(target: str) -> set[Path]:
    seen_mods: set[str] = set()
    files: set[Path] = set()
    stack = [target]
    while stack:
        mod = stack.pop()
        if mod in seen_mods:
            continue
        seen_mods.add(mod)
        f = module_file(mod)
        if f is None:
            continue
        files.add(f)
        try:
            text = f.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        stack.extend(IMPORT_RE.findall(text))
    return files


def main() -> int:
    targets = sys.argv[1:]
    if not targets:
        print("usage: closure_sorry_scan.py <Module.Name> [more...]")
        return 2
    for target in targets:
        files = closure(target)
        hits = []
        for f in sorted(files):
            text = f.read_text(encoding="utf-8", errors="replace")
            for m in SORRY_RE.finditer(text):
                line = text.count("\n", 0, m.start()) + 1
                ctx = text.splitlines()[line - 1].strip()
                hits.append((f, line, ctx))
        print(f"== {target}: {len(files)} modules in import closure, {len(hits)} sorry/admit tokens")
        for f, line, ctx in hits:
            print(f"   {f.relative_to(WEIL)}:{line}: {ctx[:120]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
