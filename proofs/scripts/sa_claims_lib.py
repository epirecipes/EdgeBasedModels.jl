"""Shared helpers for the SA-PASS claim registry (Alignment/claims*.yaml).

A registry file may be a list of claim mappings, a mapping with a `claims` list, or a mapping
from claim id to claim mapping. Every function here is read-only on the fragments.
"""

from __future__ import annotations

import pathlib
import re
from typing import Any

import yaml

ID_RE = re.compile(r"^[A-Za-z0-9._-]+$")
EXAMPLE_PREFIXES = ("SELFTEST.", "EXAMPLE.")
KINDS = {
    "algebraic-identity", "inequality", "equivalence", "existence", "structural",
    "dynamical", "categorical", "limit", "other",
}
STATUSES = {"implemented", "axiomatized", "missing", "informal"}
FIELDS = ["id", "group", "source", "text", "kind", "impl", "supporting", "impl_note",
          "required", "status", "notes"]


def is_example_id(cid: str) -> bool:
    return any(cid.startswith(p) for p in EXAMPLE_PREFIXES)


def norm_text(s: Any) -> str:
    """Whitespace-normalised text (the comparison form of a verbatim quote)."""
    return " ".join(str(s or "").split())


def fragments(text: Any) -> list[str]:
    """Split a claim text into its verbatim fragments (separator: a `[...]` token)."""
    parts = re.split(r"\s*\[\.\.\.\]\s*", norm_text(text))
    return [p for p in parts if p]


def load_claims_file(path: pathlib.Path) -> list[dict]:
    with open(path, encoding="utf-8") as fh:
        data = yaml.safe_load(fh)
    if data is None:
        return []
    if isinstance(data, dict) and "claims" in data:
        data = data["claims"]
    if isinstance(data, dict):
        out = []
        for k, v in data.items():
            v = dict(v or {})
            v.setdefault("id", k)
            out.append(v)
        data = out
    if not isinstance(data, list):
        raise ValueError(f"{path}: expected a list of claims")
    claims = []
    for c in data:
        if not isinstance(c, dict):
            raise ValueError(f"{path}: claim entry is not a mapping: {c!r}")
        c = dict(c)
        c["_file"] = str(path)
        claims.append(c)
    return claims


def as_list(x: Any) -> list:
    if x is None:
        return []
    if isinstance(x, (list, tuple)):
        return list(x)
    return [x]


def validate_claim(c: dict) -> list[str]:
    """Registry-level problems of one claim entry (independent of Lean)."""
    probs = []
    cid = str(c.get("id", ""))
    if not ID_RE.match(cid):
        probs.append("invalid_id")
    for f in ("id", "group", "source", "text", "status"):
        if c.get(f) in (None, ""):
            probs.append(f"missing field `{f}`")
    status = c.get("status")
    if status is not None and status not in STATUSES:
        probs.append(f"unknown status `{status}`")
    kind = c.get("kind")
    if kind is not None and kind not in KINDS:
        probs.append(f"unknown kind `{kind}`")
    req = bool(c.get("required", False))
    if req != (status == "implemented"):
        probs.append("required_mismatch (required must be true iff status is implemented)")
    if status == "implemented" and not as_list(c.get("impl")):
        probs.append("gap (status implemented but impl is empty)")
    return probs


def source_problem(c: dict, root: pathlib.Path) -> str | None:
    """Check that every fragment of `text` occurs verbatim (whitespace-normalised) in the cited
    source lines. Returns a description of the problem, or None."""
    src = c.get("source") or {}
    if not isinstance(src, dict):
        return "source is not a mapping"
    f = src.get("file")
    if not f:
        return "source.file missing"
    path = root / str(f)
    if not path.exists():
        return f"source file {f} not found"
    lines = path.read_text(encoding="utf-8").splitlines()
    rng = str(src.get("lines", "")).strip()
    chunks = []
    if rng:
        for part in rng.split(","):
            part = part.strip()
            m = re.match(r"^(\d+)(?:\s*-\s*(\d+))?$", part)
            if not m:
                return f"cannot parse source.lines `{rng}`"
            a = int(m.group(1))
            b = int(m.group(2) or a)
            chunks.append("\n".join(lines[a - 1:b]))
        hay = norm_text(" ".join(chunks))
    else:
        hay = norm_text("\n".join(lines))
    missing = [fr for fr in fragments(c.get("text")) if fr not in hay]
    if missing:
        return "text fragment not found verbatim in the cited lines: " + repr(missing[0][:80])
    return None


def str_presenter(dumper, data):
    if "\n" in data:
        return dumper.represent_scalar("tag:yaml.org,2002:str", data, style="|")
    return dumper.represent_scalar("tag:yaml.org,2002:str", data)


class BlockDumper(yaml.SafeDumper):
    pass


BlockDumper.add_representer(str, str_presenter)


def dump_yaml(obj: Any, path: pathlib.Path, header: str) -> None:
    text = yaml.dump(obj, Dumper=BlockDumper, sort_keys=False, allow_unicode=True, width=100)
    path.write_text(header + text, encoding="utf-8")
