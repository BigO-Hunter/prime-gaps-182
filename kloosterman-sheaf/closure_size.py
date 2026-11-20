#!/usr/bin/env python3
"""Measure the import closure of a Lean target: size, package split, and built/unbuilt counts."""
import os
import re
import sys
from pathlib import Path

WEIL = Path(os.environ.get("WEIL_VERIFY", str(Path(__file__).resolve().parent / "Weil")))
PKGS = WEIL / ".lake/packages"
ROOTS = [(WEIL / "Weil", "Weil")] + [(p / "Stacks", "Stacks") for p in [PKGS]] + [
    (WEIL / "Weil", "Weil")
]
# package roots in priority order
SEARCH = [("Weil", WEIL)] + [
    (p.name, p) for p in sorted(PKGS.iterdir()) if (p / ".lake").is_dir() or p.is_dir()
]

IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_.']+)", re.M)


def resolve(mod: str):
    rel = mod.replace(".", "/") + ".lean"
    for name, root in SEARCH:
        p = root / rel
        if p.is_file():
            return name, p
    return None, None


def olean_of(src: Path, pkg: str) -> Path:
    # Weil's own modules build into Weil/.lake/..., packages build into <pkg>/.lake/...
    root = WEIL if pkg == "Weil" else (PKGS / pkg)
    rel = src.relative_to(root if pkg == "Weil" else root)
    return root / ".lake/build/lib/lean" / rel.with_suffix(".olean")


def main() -> int:
    target = sys.argv[1]
    seen: set[str] = set()
    files: dict[str, tuple[str, Path]] = {}
    stack = [target]
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        pkg, f = resolve(mod)
        if f is None:
            continue
        files[mod] = (pkg, f)
        stack.extend(IMPORT_RE.findall(f.read_text(encoding="utf-8", errors="replace")))
    per_pkg: dict[str, int] = {}
    unbuilt: dict[str, int] = {}
    for mod, (pkg, f) in files.items():
        per_pkg[pkg] = per_pkg.get(pkg, 0) + 1
        if not olean_of(f, pkg).is_file():
            unbuilt[pkg] = unbuilt.get(pkg, 0) + 1
    print(f"target={target} closure={len(files)}")
    for pkg in sorted(per_pkg):
        print(f"  {pkg:12s} files={per_pkg[pkg]:6d} unbuilt={unbuilt.get(pkg, 0):5d}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
