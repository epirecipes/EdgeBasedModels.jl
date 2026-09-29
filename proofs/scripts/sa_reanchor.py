#!/usr/bin/env python3
"""Re-anchor claim source lines after a source edit (SA-PASS_SKILL.md §7, step 1).

For every claim in Alignment/claims/<Group>.yaml whose text no longer occurs verbatim
(whitespace-normalised, fragments split on `[...]`) in its cited `source.lines`, search the
source file for the minimal line windows that contain each fragment and rewrite `lines`:

* one window per fragment; among several candidates the one nearest the old start line wins;
* the old format is kept: a comma-separated field gets one entry per fragment, a range field
  gets the single range spanning all fragments.

Claims whose text is no longer found anywhere in the file are listed and left unchanged: their
text changed (step 2 of §7: update `text` here and in the `sa_claim`, then re-shadow blind).
Only the `lines:` line of a claim is rewritten; comments and formatting are preserved.

    python scripts/sa_reanchor.py            # dry run: report what would change
    python scripts/sa_reanchor.py --write    # rewrite the fragments in place
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import sa_claims_lib as L  # noqa: E402

MAX_WINDOW = 120  # lines


def parse_lines(rng: str) -> list[tuple[int, int]]:
    out = []
    for part in str(rng or "").split(","):
        part = part.strip()
        m = re.match(r"^(\d+)(?:\s*-\s*(\d+))?$", part)
        if m:
            a = int(m.group(1))
            out.append((a, int(m.group(2) or a)))
    return out


def windows(norm_lines: list[str], frag: str) -> list[tuple[int, int]]:
    """All minimal 1-based line windows [a, b] whose normalised text contains `frag`."""
    n = len(norm_lines)
    found = []
    for a in range(n):
        acc = ""
        for b in range(a, min(n, a + MAX_WINDOW)):
            acc = (acc + " " + norm_lines[b]).strip() if acc else norm_lines[b]
            if frag in acc:
                # minimal on the left as well?
                inner = " ".join(x for x in norm_lines[a + 1:b + 1] if x)
                if a == b or frag not in L.norm_text(inner):
                    found.append((a + 1, b + 1))
                break
    return found


def fmt(ws: list[tuple[int, int]], comma: bool) -> str:
    if comma:
        return ",".join(f"{a}" if a == b else f"{a}-{b}" for a, b in ws)
    a = min(w[0] for w in ws)
    b = max(w[1] for w in ws)
    return f"{a}-{b}"


def reanchor(c: dict, root: pathlib.Path) -> tuple[str | None, str | None]:
    """(new lines field or None, problem or None)."""
    if L.source_problem(c, root) is None:
        return None, None
    src = c.get("source") or {}
    path = root / str(src.get("file"))
    if not path.exists():
        return None, f"source file {src.get('file')} not found"
    norm_lines = [L.norm_text(x) for x in path.read_text(encoding="utf-8").splitlines()]
    old = parse_lines(src.get("lines", ""))
    old_a = old[0][0] if old else 1
    comma = "," in str(src.get("lines", ""))
    chosen = []
    for frag in L.fragments(c.get("text")):
        ws = windows(norm_lines, frag)
        if not ws:
            return None, "text fragment no longer in the file (text changed): " + repr(frag[:70])
        ref = chosen[-1][1] if chosen else old_a
        ws.sort(key=lambda w: (abs(w[0] - ref), w[0]))
        chosen.append(ws[0])
    new = fmt(chosen, comma)
    trial = dict(c)
    trial["source"] = dict(src, lines=new)
    if L.source_problem(trial, root) is not None:
        return None, f"re-anchoring to {new} does not verify"
    return new, None


def rewrite(path: pathlib.Path, updates: dict[str, str]) -> int:
    lines = path.read_text(encoding="utf-8").splitlines(keepends=True)
    cur = None
    n = 0
    for i, line in enumerate(lines):
        m = re.match(r"^- id: (.+?)\s*$", line)
        if m:
            cur = m.group(1).strip().strip("'\"")
            continue
        if cur in updates and re.match(r"^    lines:", line):
            val = updates[cur]
            val = f"'{val}'" if "," in val else val
            lines[i] = f"    lines: {val}\n"
            n += 1
            cur = None
    path.write_text("".join(lines), encoding="utf-8")
    return n


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=str(pathlib.Path(__file__).resolve().parent.parent))
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()
    root = pathlib.Path(args.root)
    total = 0
    problems = []
    for frag_file in sorted((root / "Alignment" / "claims").glob("*.yaml")):
        updates = {}
        for c in L.load_claims_file(frag_file):
            new, prob = reanchor(c, root)
            if prob:
                problems.append(f"{c['id']}: {prob}")
            elif new is not None:
                updates[str(c["id"])] = new
                print(f"{c['id']}: lines {c['source'].get('lines')} -> {new}")
        if updates and args.write:
            n = rewrite(frag_file, updates)
            if n != len(updates):
                print(f"WARNING: {frag_file.name}: rewrote {n} of {len(updates)} lines fields")
        total += len(updates)
    print(f"{total} claim(s) re-anchored{'' if args.write else ' (dry run)'}")
    if problems:
        print(f"{len(problems)} claim(s) need attention:")
        for p in problems:
            print("  - " + p)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
