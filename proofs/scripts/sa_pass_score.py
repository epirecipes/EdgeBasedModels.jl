#!/usr/bin/env python3
"""SA-PASS scorer: combine the Lean audit (Alignment/report/sa_pass_audit.json, written by
`#sa_pass_report`) with the claim registry, compute the scores and render the report.

Registration consistency (a claim scores 0 on any of these):
  Lean side (from the audit): invalid_id, duplicate, gap, impl_untrusted, impl_unsound,
                              shadow_mismatch, incomplete, module_mismatch, audit_error,
                              shadow_trusted_free, shadow_tautology, hypothesis_refuted,
                              witness_invalid
  Registry side (here):       unlisted, impl_mismatch, text_mismatch, group_mismatch,
                              required_mismatch, duplicate, invalid_id, gap
Hints (reported, never scored): witness_missing, backward_unused_shadows, identical_to_impl.
Scores: SA-PASS = 1 iff consistent, n >= 1, every forward check and the backward check pass;
SA-PASS_soft = 0.5 * (forward passes) / n + 0.5 * [backward passes] (0 if inconsistent).

Modes: `report` (excludes SELFTEST.* / EXAMPLE.* ids) and `selftest` (only those ids; compares
the result with the expectations file and exits non-zero on any mismatch).
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import pathlib
import sys
from collections import Counter, defaultdict

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import sa_claims_lib as L  # noqa: E402

import yaml  # noqa: E402

# every flag zeroes the claim's score; listed here for documentation
SCORE_FLAGS = ["unlisted", "invalid_id", "duplicate", "gap", "impl_untrusted", "impl_unsound",
               "impl_mismatch", "text_mismatch", "group_mismatch", "required_mismatch",
               "shadow_mismatch", "incomplete", "module_mismatch", "audit_error",
               "shadow_trusted_free", "shadow_tautology", "hypothesis_refuted", "witness_invalid"]
HINTS = ["witness_missing", "backward_unused_shadows"]
STATUSES = ["pass", "fail", "vacuous", "audit_violation", "sorry", "missing"]


def load_registry(paths: list[str]) -> list[dict]:
    claims = []
    for p in paths:
        path = pathlib.Path(p)
        if path.exists():
            claims.extend(L.load_claims_file(path))
    return claims


def score_claims(audit: dict, registry: list[dict], select, root: pathlib.Path,
                 check_sources: bool) -> dict:
    lean = [c for c in audit.get("claims", []) if select(c["id"])]
    reg = [c for c in registry if select(str(c.get("id", "")))]
    reg_by_id: dict[str, list[dict]] = defaultdict(list)
    for c in reg:
        reg_by_id[str(c.get("id"))].append(c)
    results = []
    for c in lean:
        cid = c["id"]
        flags: dict[str, list[str]] = defaultdict(list)
        for f in c.get("lean_flags", []):
            flags[f["flag"]].append(f["detail"])
        entries = reg_by_id.get(cid, [])
        y = entries[0] if entries else None
        if y is None:
            flags["unlisted"].append("not in the claims registry")
        else:
            if len(entries) > 1:
                flags["duplicate"].append(f"{len(entries)} registry entries")
            if not L.ID_RE.match(cid):
                flags["invalid_id"].append("registry id does not match [A-Za-z0-9._-]+")
            if L.norm_text(y.get("text")) != L.norm_text(c.get("text")):
                flags["text_mismatch"].append("sa_claim text differs from the registry text")
            if str(y.get("group")) != c.get("group"):
                flags["group_mismatch"].append(f"registry `{y.get('group')}` vs Lean `{c.get('group')}`")
            yreq = bool(y.get("required", False))
            if yreq != bool(c.get("required")):
                flags["required_mismatch"].append(f"registry required={yreq} vs Lean {c.get('required')}")
            elif yreq != (y.get("status") == "implemented"):
                flags["required_mismatch"].append("registry required is not (status == implemented)")
            yimpl = sorted(str(x) for x in L.as_list(y.get("impl")))
            if yimpl != sorted(c.get("impl", [])):
                flags["impl_mismatch"].append(f"registry {yimpl} vs Lean {sorted(c.get('impl', []))}")
            if y.get("status") == "implemented" and not yimpl:
                flags["gap"].append("registry status implemented with empty impl")
        warnings = []
        if y is not None and check_sources:
            sp = L.source_problem(y, root)
            if sp:
                warnings.append("source_mismatch: " + sp)
        fwd = c.get("forward", [])
        bwd = c.get("backward", {})
        n = c.get("n_shadows", 0)
        npass = sum(1 for f in fwd if f["status"] == "pass")
        bpass = bwd.get("status") == "pass"
        consistent = not flags
        sa_pass = int(consistent and n > 0 and npass == n and bpass)
        soft = (0.5 * npass / n + 0.5 * (1 if bpass else 0)) if (consistent and n > 0) else 0.0
        group = str(y.get("group")) if y is not None else c.get("group")
        required = bool(y.get("required")) if y is not None else bool(c.get("required"))
        results.append({
            "id": cid, "group": group, "required": required,
            "status": (y or {}).get("status"), "n": n,
            "forward": [f["status"] for f in fwd], "backward": bwd.get("status", "missing"),
            "forward_detail": fwd, "backward_detail": bwd,
            "flags": {k: v for k, v in flags.items()}, "warnings": warnings,
            "sa_pass": sa_pass, "soft": round(soft, 4),
            "identical_to_impl": c.get("identical_to_impl", []),
            "hints": [h["hint"] for h in c.get("hints", [])],
            "hint_details": c.get("hints", []),
            "trusted_free_shadows": c.get("trusted_free_shadows", []),
            "tautological_shadows": c.get("tautological_shadows", []),
            "refutations": c.get("refutations", []),
            "witnesses": c.get("witnesses", []),
            "impl": c.get("impl", []), "impl_info": c.get("impl_info", []),
            "shadow_question": [f["idx"] for f in fwd if f.get("shadow_question")] +
                               (["backward"] if bwd.get("shadow_question") else []),
        })
    lean_ids = {c["id"] for c in lean}
    unregistered = []
    for cid, entries in reg_by_id.items():
        if cid not in lean_ids:
            y = entries[0]
            unregistered.append({"id": cid, "group": str(y.get("group")),
                                 "required": bool(y.get("required", False)),
                                 "status": y.get("status"), "impl": L.as_list(y.get("impl")),
                                 "problems": L.validate_claim(y)})
    return {"claims": results, "unregistered": unregistered, "registry_size": len(reg)}


def summarise(scored: dict, audit: dict, select) -> dict:
    claims = scored["claims"]
    unreg = scored["unregistered"]
    groups: dict[str, dict] = defaultdict(lambda: {
        "registry": 0, "registered": 0, "required": 0, "sa_pass": 0, "soft_sum": 0.0,
        "fwd_pass": 0, "fwd_total": 0, "bwd_pass": 0, "bwd_total": 0, "required_failures": 0,
        "status_counts": Counter()})
    for c in claims:
        g = groups[c["group"]]
        g["registered"] += 1
        g["registry"] += 0 if "unlisted" in c["flags"] else 1
        g["required"] += int(c["required"])
        g["sa_pass"] += c["sa_pass"]
        g["soft_sum"] += c["soft"]
        g["fwd_pass"] += sum(1 for s in c["forward"] if s == "pass")
        g["fwd_total"] += len(c["forward"])
        g["bwd_pass"] += int(c["backward"] == "pass")
        g["bwd_total"] += 1
        g["required_failures"] += int(c["required"] and not c["sa_pass"])
        for s in c["forward"] + [c["backward"]]:
            g["status_counts"][s] += 1
    for u in unreg:
        g = groups[u["group"]]
        g["registry"] += 1
        g["required"] += int(u["required"])
        g["required_failures"] += int(u["required"])
    group_rows = []
    for name in sorted(groups):
        g = groups[name]
        group_rows.append({
            "group": name, "registry": g["registry"], "registered": g["registered"],
            "required": g["required"], "sa_pass": g["sa_pass"],
            "mean_soft": round(g["soft_sum"] / g["registered"], 4) if g["registered"] else 0.0,
            "fwd_pass": g["fwd_pass"], "fwd_total": g["fwd_total"], "bwd_pass": g["bwd_pass"],
            "bwd_total": g["bwd_total"], "required_failures": g["required_failures"],
            "status_counts": dict(g["status_counts"])})
    required_failures = []
    for c in claims:
        if c["required"] and not c["sa_pass"]:
            reasons = [f"{k}: {'; '.join(v)}" for k, v in c["flags"].items()]
            reasons += [f"forward {i + 1}: {s}" for i, s in enumerate(c["forward"]) if s != "pass"]
            if c["backward"] != "pass":
                reasons.append(f"backward: {c['backward']}")
            if c["n"] == 0:
                reasons.append("no shadows")
            required_failures.append({"id": c["id"], "reasons": reasons})
    for u in unreg:
        if u["required"]:
            required_failures.append({"id": u["id"], "reasons": ["not registered in Lean (no sa_claim)"]})
    offenders: dict[str, dict] = {}
    for c in claims:
        checks = [(f"forward {f['idx']}", f) for f in c["forward_detail"]] + [("backward", c["backward_detail"])]
        for label, d in checks:
            for o in d.get("offenders", []) or []:
                e = offenders.setdefault(o, {"offender": o, "count": 0, "checks": []})
                e["count"] += 1
                e["checks"].append(f"{c['id']} {label}")
    bridges = [b for b in audit.get("bridges", []) if any(select(x) for x in b.get("claims", []))]
    bridge_counts = Counter(b["status"] for b in bridges)
    n_reg = len(claims)
    hint_counts = Counter(h for c in claims for h in c["hints"])
    trusted_free = [{"claim": c["id"], **t} for c in claims for t in c["trusted_free_shadows"]]
    tautological = [{"claim": c["id"], **t} for c in claims for t in c["tautological_shadows"]]
    refuted = [{"claim": c["id"], "sa_pass_without_flag": int(
        set(c["flags"]) == {"hypothesis_refuted"} and c["n"] > 0 and
        all(s == "pass" for s in c["forward"]) and c["backward"] == "pass"),
        "refutations": c["refutations"]} for c in claims if c["refutations"]]
    summary = {
        "registry_claims": scored["registry_size"],
        "registered_claims": n_reg,
        "unregistered_claims": len(unreg),
        "required_claims": sum(int(c["required"]) for c in claims) + sum(int(u["required"]) for u in unreg),
        "sa_pass": sum(c["sa_pass"] for c in claims),
        "sa_pass_required": sum(c["sa_pass"] for c in claims if c["required"]),
        "mean_soft": round(sum(c["soft"] for c in claims) / n_reg, 4) if n_reg else 0.0,
        "required_failures": len(required_failures),
        "check_status_counts": dict(Counter(s for c in claims for s in c["forward"] + [c["backward"]])),
        "bridges": dict(bridge_counts),
        "hints": dict(hint_counts),
        "trusted_free_shadows": dict(Counter(t["review"] for t in trusted_free)),
        "tautological_shadows": dict(Counter(t["review"] for t in tautological)),
        "claims_with_refuted_hypotheses": len(refuted),
    }
    fails = [f for f in audit.get("fail_records", []) if select(f["claim"])]
    orphans = [o for o in audit.get("orphan_registrations", []) if select(o["claim"])]
    bridge_claims = {b["decl"]: b.get("claims", []) for b in audit.get("bridges", [])}
    ignored = [r for r in audit.get("reviews", []) if not r.get("counted")
               and (not bridge_claims.get(r["decl"]) or any(select(x) for x in bridge_claims[r["decl"]]))]
    refuters = [r for r in audit.get("refuters", [])
                if r.get("origin") == "trusted" or select_refuter(r, select)]
    return {"summary": summary, "groups": group_rows, "required_failures": required_failures,
            "offenders": sorted(offenders.values(), key=lambda e: (-e["count"], e["offender"])),
            "bridges": bridges, "fail_records": fails, "orphans": orphans,
            "ignored_reviews": ignored, "trusted_free": trusted_free,
            "tautological": tautological, "refuted": refuted,
            "refuters": refuters}


def select_refuter(r: dict, select) -> bool:
    """Alignment-library refuters declared by the self-test belong to the self-test report."""
    selftest = str(r.get("module", "")).startswith("Alignment.Example")
    return selftest == bool(select("SELFTEST.x"))


def example_sanity(audit: dict) -> str:
    """One line: do the worked-example claims pass every check (Lean side only)?"""
    ex = [c for c in audit.get("claims", []) if c["id"].startswith("EXAMPLE.")]
    ok = [c for c in ex if not c.get("lean_flags") and c.get("n_shadows", 0) > 0
          and all(f["status"] == "pass" for f in c.get("forward", []))
          and c.get("backward", {}).get("status") == "pass"]
    return (f"Tool sanity: {len(ok)}/{len(ex)} worked-example claims (`EXAMPLE.*`) pass every check "
            f"(run `bash scripts/sa_pass.sh --self-test` for the full self-test).")


def md_escape(s: str) -> str:
    return str(s).replace("|", "\\|").replace("\n", " ")


def render_md(scored: dict, summ: dict, audit: dict, mode: str, sources: list[str]) -> str:
    s = summ["summary"]
    now = _dt.datetime.now().strftime("%Y-%m-%d %H:%M")
    out = [f"# SA-PASS report ({'self-test' if mode == 'selftest' else 'EBCMCategory'})", "",
           f"Generated {now} from `Alignment/report/sa_pass_audit.json` "
           f"(Lean {audit.get('lean_version')}) and {', '.join('`' + x + '`' for x in sources)}.",
           "", "Trusted modules loaded by the audit: " +
           ", ".join(f"`{m}`" for m in audit.get("trusted_modules", [])) +
           ("" if audit.get("trusted_by_import") else
            " (**root file not read: trust by module prefix**)"), "",
           example_sanity(audit), "",
           "## Summary", "", "| quantity | value |", "|---|---|",
           f"| claims in registry | {s['registry_claims']} |",
           f"| claims registered in Lean | {s['registered_claims']} |",
           f"| registry claims not registered in Lean | {s['unregistered_claims']} |",
           f"| required claims (status implemented) | {s['required_claims']} |",
           f"| SA-PASS = 1 (all / required) | {s['sa_pass']} / {s['sa_pass_required']} |",
           f"| mean SA-PASS_soft (registered claims) | {s['mean_soft']} |",
           f"| required failures | {s['required_failures']} |",
           "| check statuses | " + ", ".join(f"{k}: {v}" for k, v in sorted(s["check_status_counts"].items())) + " |",
           "| bridges | " + ", ".join(f"{k}: {v}" for k, v in sorted(s["bridges"].items())) + " |",
           "| hints (not scored) | " + (", ".join(f"{k}: {v}" for k, v in sorted(s["hints"].items())) or "none") + " |",
           "| trusted-free shadows (by review status) | " +
           (", ".join(f"{k}: {v}" for k, v in sorted(s["trusted_free_shadows"].items())) or "none") + " |",
           "| tautological shadows (by review status) | " +
           (", ".join(f"{k}: {v}" for k, v in sorted(s.get("tautological_shadows", {}).items())) or "none") + " |",
           f"| claims with a refuted implementation hypothesis | {s['claims_with_refuted_hypotheses']} |",
           "", "## Per group", "",
           "| group | registry | registered | required | SA-PASS=1 | mean soft | forward pass | backward pass | required failures |",
           "|---|---|---|---|---|---|---|---|---|"]
    for g in summ["groups"]:
        out.append(f"| {g['group']} | {g['registry']} | {g['registered']} | {g['required']} | {g['sa_pass']} | "
                   f"{g['mean_soft']} | {g['fwd_pass']}/{g['fwd_total']} | {g['bwd_pass']}/{g['bwd_total']} | "
                   f"{g['required_failures']} |")
    out += ["", "## Claims", "",
            "| id | req | n | forward | backward | SA-PASS | soft | flags |", "|---|---|---|---|---|---|---|---|"]
    for c in sorted(scored["claims"], key=lambda c: (c["group"], c["id"])):
        fl = ", ".join(sorted(c["flags"])) or ""
        ident = f" (identical to impl: {c['identical_to_impl']})" if c["identical_to_impl"] else ""
        if c["hints"]:
            ident += f" (hints: {', '.join(sorted(set(c['hints'])))})"
        out.append(f"| `{md_escape(c['id'])}` | {'yes' if c['required'] else 'no'} | {c['n']} | "
                   f"{' '.join(c['forward']) or '-'} | {c['backward']} | {c['sa_pass']} | {c['soft']} | "
                   f"{md_escape(fl)}{md_escape(ident)} |")
    if scored["unregistered"]:
        out += ["", "## Registry claims without a Lean registration", "",
                "| id | group | required | status | impl | registry problems |", "|---|---|---|---|---|---|"]
        for u in sorted(scored["unregistered"], key=lambda u: (u["group"], u["id"])):
            out.append(f"| `{md_escape(u['id'])}` | {u['group']} | {'yes' if u['required'] else 'no'} | "
                       f"{u['status']} | {md_escape(', '.join(u['impl']))} | {md_escape('; '.join(u['problems']))} |")
    out += ["", "## Required failures", ""]
    if not summ["required_failures"]:
        out.append("None.")
    for r in summ["required_failures"]:
        out.append(f"* `{r['id']}`: " + md_escape("; ".join(r["reasons"])))
    out += ["", "## Bridges", "", "| bridge | claims | status | hash | statement | notes |",
            "|---|---|---|---|---|---|"]
    for b in sorted(summ["bridges"], key=lambda b: (b["status"], b["decl"])):
        notes = "; ".join(b.get("reasons", []) + ([b["review_reason"]] if b.get("review_reason") else []))
        out.append(f"| `{b['decl']}` | {md_escape(', '.join(b['claims']))} | {b['status']} | `{b['hash']}` | "
                   f"`{md_escape(b['statement'])}` | {md_escape(notes)} |")
    out += ["", "## Refuted implementation hypotheses (`hypothesis_refuted`)", "",
            "The implementation theorem assumes a hypothesis that a sound theorem refutes, so it is "
            "vacuously true (and so is every shadow that shares the hypothesis). The refutation is "
            "kernel-checked.", ""]
    if not summ["refuted"]:
        out.append("None.")
    for r in summ["refuted"]:
        note = " (all checks pass: this pass is withdrawn by the flag)" if r["sa_pass_without_flag"] else ""
        out.append(f"* `{r['claim']}`{note}: " + md_escape("; ".join(r["refutations"])))
    out += ["", "## Trusted-free shadows (`shadow_trusted_free`)", "",
            "These shadows mention no trusted-library constant after inlining alignment helpers, so "
            "they are closed statements of logic or arithmetic. The flag zeroes the claim until an "
            "independent reviewer confirms that the source text is itself such a statement, with "
            "`sa_shadow_reviewed <shadow> \"<hash>\" \"<reason>\"` in `Alignment/ReviewedBridges.lean`.", "",
            "| claim | shadow | content hash | review |", "|---|---|---|---|"]
    for t in sorted(summ["trusted_free"], key=lambda t: (t["review"], t["claim"], t["idx"])):
        out.append(f"| `{md_escape(t['claim'])}` | S{t['idx']} `{t['decl']}` | `{t['hash']}` | {t['review']} |")
    out += ["", "## Tautological shadows (`shadow_tautology`)", "",
            "These shadows hold by reflexivity or by assumption at reducible transparency after "
            "inlining alignment helpers, so they say nothing whatever constants they mention. The "
            "flag is lifted by the same hash-pinned `sa_shadow_reviewed` record.", "",
            "| claim | shadow | content hash | review |", "|---|---|---|---|"]
    if not summ["tautological"]:
        out.append("| none | | | |")
    for t in sorted(summ["tautological"], key=lambda t: (t["review"], t["claim"], t["idx"])):
        out.append(f"| `{md_escape(t['claim'])}` | S{t['idx']} `{t['decl']}` | `{t['hash']}` | {t['review']} |")
    hinted = [c for c in scored["claims"] if c["hint_details"]]
    out += ["", "## Hints (not scored)", "",
            "`witness_missing`: an implementation hypothesis headed by a trusted predicate is shared "
            "by every shadow, and no `@[sa_witness]` certificate shows it can hold. "
            "`backward_unused_shadows`: the backward checker does not use some shadows (they may be "
            "redundant).", ""]
    if not hinted:
        out.append("None.")
    for c in sorted(hinted, key=lambda c: c["id"]):
        for h in c["hint_details"]:
            out.append(f"* `{c['id']}` {h['hint']}: {md_escape(h['detail'])}")
    out += ["", "## Refuters", "",
            "Theorems used to refute implementation hypotheses: sound trusted-library theorems "
            "`∀ ys, P₁ → … → Pₘ → False` (or `→ ¬ P`, `→ a ≠ b`) and alignment-library "
            "`@[sa_refutation]` theorems.", "",
            "| refuter | origin | status | premise heads | notes |", "|---|---|---|---|---|"]
    for r in sorted(summ["refuters"], key=lambda r: (r.get("origin", ""), r.get("status", ""), r["decl"])):
        out.append(f"| `{r['decl']}` | {r.get('origin')} | {r.get('status')} | "
                   f"{md_escape(', '.join(r.get('heads', [])))} | {md_escape('; '.join(r.get('reasons', [])))} |")
    out += ["", "## Offending constants", "", "| constant [reason] | checks | examples |", "|---|---|---|"]
    for e in summ["offenders"][:300]:
        out.append(f"| `{md_escape(e['offender'])}` | {e['count']} | {md_escape(', '.join(e['checks'][:4]))} |")
    out += ["", "## Recorded failures (`sa_fail_*`)", "", "| claim | target | reason | SHADOW? |", "|---|---|---|---|"]
    for f in summ["fail_records"]:
        out.append(f"| `{f['claim']}` | {f['target']} | {md_escape(f['reason'])} | "
                   f"{'yes' if f.get('shadow_question') else ''} |")
    if summ["orphans"] or summ["ignored_reviews"]:
        out += ["", "## Warnings", ""]
        for o in summ["orphans"]:
            out.append(f"* orphan registration `{o['kind']}` of `{o['decl']}` for unknown claim `{o['claim']}`")
        for r in summ["ignored_reviews"]:
            out.append(f"* review record for `{r['decl']}` in `{r['module']}` ignored (only "
                       f"`Alignment.ReviewedBridges` counts)")
    warn = [(c["id"], w) for c in scored["claims"] for w in c["warnings"]]
    if warn:
        out += ["", "## Source anchoring warnings", ""]
        out += [f"* `{cid}`: {md_escape(w)}" for cid, w in warn]
    out += ["", "Check statuses: `pass` (exact statement, structural, not vacuous), `fail` (wrong statement or "
            "recorded failure), `vacuous`, `audit_violation` (offenders listed), `sorry`, `missing`. "
            "Passes whose shadows were written after seeing the implementation are weak passes.", ""]
    return "\n".join(out)


def run_selftest(scored: dict, summ: dict, expected_path: pathlib.Path) -> list[str]:
    exp = yaml.safe_load(expected_path.read_text(encoding="utf-8")) or {}
    errors = []
    by_id = {c["id"]: c for c in scored["claims"]}
    exp_claims = exp.get("claims", {}) or {}
    for cid in by_id:
        if cid not in exp_claims:
            errors.append(f"{cid}: no expectation (add it to {expected_path.name})")
    for cid, e in exp_claims.items():
        c = by_id.get(cid)
        if c is None:
            errors.append(f"{cid}: expected in the audit but not registered")
            continue
        got_flags = sorted(c["flags"])
        if sorted(e.get("flags", []) or []) != got_flags:
            errors.append(f"{cid}: flags {got_flags} != expected {sorted(e.get('flags', []) or [])}")
        if "forward" in e and list(e["forward"]) != c["forward"]:
            errors.append(f"{cid}: forward {c['forward']} != expected {e['forward']}")
        if "backward" in e and e["backward"] != c["backward"]:
            errors.append(f"{cid}: backward {c['backward']} != expected {e['backward']}")
        if "sa_pass" in e and int(e["sa_pass"]) != c["sa_pass"]:
            errors.append(f"{cid}: sa_pass {c['sa_pass']} != expected {e['sa_pass']}")
        if "soft" in e and abs(float(e["soft"]) - c["soft"]) > 1e-9:
            errors.append(f"{cid}: soft {c['soft']} != expected {e['soft']}")
        if "shadow_question" in e and list(e["shadow_question"]) != c["shadow_question"]:
            errors.append(f"{cid}: shadow_question {c['shadow_question']} != expected {e['shadow_question']}")
        if "hints" in e and sorted(set(e["hints"] or [])) != sorted(set(c["hints"])):
            errors.append(f"{cid}: hints {sorted(set(c['hints']))} != expected {sorted(set(e['hints'] or []))}")
        for flag, subs in (e.get("flag_details_include") or {}).items():
            det = " ".join(c["flags"].get(flag, []))
            for sub in subs:
                if sub not in det:
                    errors.append(f"{cid}: {flag} details do not mention `{sub}`: {det[:300]}")
        for flag, subs in (e.get("flag_details_exclude") or {}).items():
            det = " ".join(c["flags"].get(flag, []))
            for sub in subs:
                if sub in det:
                    errors.append(f"{cid}: {flag} details must not mention `{sub}`: {det[:300]}")
        if "trusted_free" in e:
            got = {int(t["idx"]): t["review"] for t in c["trusted_free_shadows"]}
            want = {int(k): v for k, v in (e["trusted_free"] or {}).items()}
            if got != want:
                errors.append(f"{cid}: trusted-free shadows {got} != expected {want}")
        if "tautological" in e:
            got = {int(t["idx"]): t["review"] for t in c["tautological_shadows"]}
            want = {int(k): v for k, v in (e["tautological"] or {}).items()}
            if got != want:
                errors.append(f"{cid}: tautological shadows {got} != expected {want}")
        if "unused_shadows" in e:
            got = c["backward_detail"].get("unused_shadows", [])
            if list(e["unused_shadows"]) != list(got):
                errors.append(f"{cid}: backward unused shadows {got} != expected {e['unused_shadows']}")
        for label, subs in (e.get("offenders_include") or {}).items():
            if label == "backward":
                offs = c["backward_detail"].get("offenders", [])
            else:
                idx = int(str(label).replace("forward", "").strip() or 1)
                offs = next((f.get("offenders", []) for f in c["forward_detail"] if f["idx"] == idx), [])
            for sub in subs:
                if not any(sub in o for o in offs):
                    errors.append(f"{cid}: {label} offenders {offs} do not mention `{sub}`")
    refuters = {r["decl"]: r for r in summ["refuters"]}
    for decl, st in (exp.get("refuters", {}) or {}).items():
        r = refuters.get(decl)
        if r is None:
            errors.append(f"refuter {decl}: not found")
        elif r.get("status") != st:
            errors.append(f"refuter {decl}: status {r.get('status')} != expected {st} ({r.get('reasons')})")
    bridges = {b["decl"]: b for b in summ["bridges"]}
    for decl, st in (exp.get("bridges", {}) or {}).items():
        b = bridges.get(decl)
        if b is None:
            errors.append(f"bridge {decl}: not found")
        elif b["status"] != st:
            errors.append(f"bridge {decl}: status {b['status']} != expected {st} ({b.get('reasons')})")
    return errors


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=str(pathlib.Path(__file__).resolve().parent.parent))
    ap.add_argument("--audit", default="Alignment/report/sa_pass_audit.json")
    ap.add_argument("--claims", action="append", default=None)
    ap.add_argument("--mode", choices=["report", "selftest"], default="report")
    ap.add_argument("--expected", default="Alignment/Example/selftest_expected.yaml")
    ap.add_argument("--out-json", default=None)
    ap.add_argument("--out-md", default=None)
    ap.add_argument("--strict", action="store_true")
    ap.add_argument("--check-sources", action="store_true")
    args = ap.parse_args()
    root = pathlib.Path(args.root)
    audit = json.loads((root / args.audit).read_text(encoding="utf-8"))
    if args.mode == "selftest":
        claim_files = args.claims or ["Alignment/Example/claims_example.yaml",
                                      "Alignment/Example/claims_selftest.yaml"]
        select = L.is_example_id
        out_json = args.out_json or "Alignment/report/sa_selftest_report.json"
        out_md = args.out_md or "Alignment/report/sa_selftest_report.md"
    else:
        claim_files = args.claims or ["Alignment/claims.yaml"]
        select = lambda cid: not L.is_example_id(cid)  # noqa: E731
        out_json = args.out_json or "Alignment/report/sa_pass_report.json"
        out_md = args.out_md or "Alignment/report/sa_pass_report.md"
    registry = load_registry([str(root / p) for p in claim_files])
    scored = score_claims(audit, registry, select, root, args.check_sources)
    summ = summarise(scored, audit, select)
    report = {"mode": args.mode, "lean_version": audit.get("lean_version"),
              "trusted_modules": audit.get("trusted_modules"), **summ,
              "claims": scored["claims"], "unregistered": scored["unregistered"]}
    (root / out_json).write_text(json.dumps(report, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    (root / out_md).write_text(render_md(scored, summ, audit, args.mode, claim_files), encoding="utf-8")
    s = summ["summary"]
    print(f"SA-PASS ({args.mode}): {s['registered_claims']} registered claim(s), SA-PASS=1: {s['sa_pass']}, "
          f"mean soft {s['mean_soft']}, required failures {s['required_failures']} "
          f"-> {out_md}")
    if args.mode == "selftest":
        errors = run_selftest(scored, summ, root / args.expected)
        n_exp = len((yaml.safe_load((root / args.expected).read_text(encoding='utf-8')) or {}).get("claims", {}))
        if errors:
            print(f"SELF-TEST FAILED ({len(errors)} mismatch(es)):")
            for e in errors:
                print("  - " + e)
            return 1
        exp_all = yaml.safe_load((root / args.expected).read_text(encoding='utf-8')) or {}
        print(f"SELF-TEST PASSED: {n_exp} claim expectation(s), "
              f"{len(exp_all.get('bridges', {}) or {})} bridge expectation(s) and "
              f"{len(exp_all.get('refuters', {}) or {})} refuter expectation(s) met")
        return 0
    if args.strict and s["required_failures"]:
        print(f"STRICT: {s['required_failures']} required claim(s) without SA-PASS = 1")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
