"""Reproduce the conditional certificate checks, without certifying external mathematics."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

from snippets import ROOT, code, input_document, target_block

EXPECTED_FIELDS = {
    "intersection": "HeightOneIntersection", "dimension": "FiniteLocalDimension",
    "normalization": "NormalizationPieces", "boundary": "AffineBoundaryDivisors",
    "etaleDivisors": "EtalePullbackDivisors", "etaleNormal": "EtalePreservesNormal",
    "abhyankar": "AbhyankarLocalIrreducibility", "divisorImage": "FiniteDivisorImage",
    "divisorEquations": "PolynomialPrimeDivisorEquation", "affineRegular": "AffineSpaceRegular",
    "normalOpen": "NormalLocusOpen", "domainComponents": "DomainPointUniqueComponent",
    "regularOpen": "RegularOpenImmersion",
}
TOOLCHAIN = "leanprover/lean4:v4.28.0"
MATHLIB_REV = "8f9d9cff6bd728b17a24e163c9402775d9e6a365"
CONDITIONAL_MARKER = "CONDITIONAL_NL_VERIFIED: exact Library → NL target and standard axioms checked"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manifest(root: Path = ROOT) -> None:
    manifest = json.loads((root / "manifest.json").read_text(encoding="utf-8"))
    actual_lean = {p.relative_to(root).as_posix() for p in (root / "NormalLocus").glob("*.lean")}
    expected_lean = {p for p in manifest["files"] if p.startswith("NormalLocus/") and p.endswith(".lean")}
    if actual_lean != expected_lean:
        raise ValueError("Lean source file set differs from the reviewed manifest")
    for relative, expected in manifest["files"].items():
        path = root / relative
        if not path.is_file() or sha256(path) != expected:
            raise ValueError(f"Reviewed file changed: {relative}")


def check_documentation() -> None:
    if (ROOT / "docs/inputs.md").read_text(encoding="utf-8") != input_document():
        raise ValueError("Displayed input declarations differ from Lean source")
    expected_target = (
        "# 结果和全部核心定义\n\n"
        "以下是实际源文件中的声明片段，由验证程序逐字比对。完整上下文见对应 Lean 文件。\n\n"
        + target_block() + "\n\n## 完整组合证明\n\n"
        + code("NormalLocus/ConditionalNL.lean", "normal_locus_finite_etale_conditional") + "\n"
    )
    if (ROOT / "docs/target.md").read_text(encoding="utf-8") != expected_target:
        raise ValueError("Displayed target or proof differs from Lean source")
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    for path, name in [
        ("NormalLocus/Statement.lean", "NormalLocusConclusion"),
        ("NormalLocus/Statement.lean", "NormalLocusTheorem"),
        ("NormalLocus/ExternalGeometry.lean", "CoreGeometry"),
        ("NormalLocus/ExternalGeometry.lean", "Library"),
    ]:
        if code(path, name) not in readme:
            raise ValueError(f"README does not display the exact declaration {name}")
    source = (ROOT / "NormalLocus/ExternalGeometry.lean").read_text(encoding="utf-8")
    fields = {}
    for structure in ["CoreGeometry", "Library"]:
        match = re.search(rf"structure {structure}\b[^\n]*where\n((?:  \w+ : \w+\n)+)", source)
        if not match:
            raise ValueError(f"Cannot inspect {structure}")
        fields.update(re.findall(r"^  (\w+) : (\w+)$", match[1], re.MULTILINE))
    registered = json.loads((ROOT / "external_inputs.json").read_text(encoding="utf-8"))["inputs"]
    if len(registered) != 13 or {x["field"]: x["statement"] for x in registered} != EXPECTED_FIELDS:
        raise ValueError("External register differs from the thirteen reviewed inputs")
    if fields != EXPECTED_FIELDS:
        raise ValueError("External Library fields differ from the reviewed inputs")
    tex = (ROOT / "provenance/Normal_Loci_Keller_Maps_v1.tex").read_text(encoding="utf-8")
    labels = set(re.findall(r"\\label\{([^}]+)\}", tex))
    for item in registered:
        if not set(item["tex_labels"]) <= labels:
            raise ValueError(f"Unknown TeX anchor for {item['field']}")


def check_source_policy() -> None:
    # This is a supplementary source check, not a substitute for axiom audit or replay.
    forbidden = r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b|skipKernelTC|ofReduceBool|trustCompiler"
    for path in sorted((ROOT / "NormalLocus").glob("*.lean")):
        source = path.read_text(encoding="utf-8")
        source = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
        source = re.sub(r"--[^\n]*", "", source)
        if re.search(forbidden, source):
            raise ValueError(f"Forbidden proof-source construct: {path.name}")


def run(lake: str, arguments: list[str], log_name: str, source: str | None = None) -> str:
    print(f"RUN: {log_name}", flush=True)
    result = subprocess.run([lake, *arguments], cwd=ROOT, input=source,
                            capture_output=True, text=True, encoding="utf-8", errors="replace")
    output = result.stdout + result.stderr
    (ROOT / "verification" / log_name).write_text(output, encoding="utf-8", newline="\n")
    if result.returncode or "PANIC at " in output or "uncaught exception:" in output:
        raise RuntimeError(f"{log_name} failed ({result.returncode}):\n{output[-5000:]}")
    print(f"PASS: {log_name}", flush=True)
    return output


def negative_checks(lake: str, header: str) -> list[str]:
    header = header.replace("`NormalLocus.normal_locus_finite_etale_conditional",
                            "`NormalLocus.TestCertificate")
    cases = {
        "wrong-target": ("theorem NormalLocus.TestCertificate : True := True.intro\n", "exact Library → NL type"),
        "extra-axiom": (
            "axiom unprovedInput : NormalLocus.NormalLocusTheorem\n"
            "theorem NormalLocus.TestCertificate (_ : NormalLocus.External.Library) : "
            "NormalLocus.NormalLocusTheorem := unprovedInput\n", "nonstandard axioms"),
        "sorry": (
            "theorem NormalLocus.TestCertificate : NormalLocus.External.Library → "
            "NormalLocus.NormalLocusTheorem := by sorry\n", "nonstandard axioms"),
        "extra-premise": (
            "theorem NormalLocus.TestCertificate (h : NormalLocus.NormalLocusTheorem) "
            "(_ : NormalLocus.External.Library) : NormalLocus.NormalLocusTheorem := h\n",
            "exact Library → NL type"),
    }
    passed = []
    for name, (fixture, expected) in cases.items():
        result = subprocess.run([lake, "env", "lean", "--stdin"], cwd=ROOT,
                                input=header + "\n" + fixture + "#audit_conditional_nl\n",
                                capture_output=True, text=True, encoding="utf-8", errors="replace")
        output = result.stdout + result.stderr
        (ROOT / f"verification/negative-{name}.log").write_text(output, encoding="utf-8", newline="\n")
        if result.returncode == 0 or expected not in output:
            raise RuntimeError(f"Negative test was not correctly rejected: {name}\n{output[-2000:]}")
        passed.append(name)
        print(f"REJECTED_AS_EXPECTED: {name}", flush=True)
    return passed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=os.environ.get("NL_LAKE") or shutil.which("lake") or "lake")
    parser.add_argument("--check-docs", action="store_true")
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()
    if args.check_docs and args.require_complete:
        parser.error("--check-docs does not perform the full-certificate check")
    started = time.monotonic()
    report = {"status": "RUNNING", "unconditional_nl": "INCOMPLETE",
              "external_inputs_proved": 0, "external_inputs_total": 13,
              "translation_fidelity": "MANUAL_REVIEW",
              "logic_and_implementation_soundness": "TRUST_ASSUMPTION",
              "independent_checker": "NOT_RUN"}
    destination = ROOT / "verification/results.json"
    try:
        check_manifest()
        initial_manifest = sha256(ROOT / "manifest.json")
        check_documentation()
        check_source_policy()
        if (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip() != TOOLCHAIN:
            raise ValueError("Unexpected Lean toolchain")
        packages = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))["packages"]
        if next(p["rev"] for p in packages if p["name"] == "mathlib") != MATHLIB_REV:
            raise ValueError("Unexpected mathlib revision")
        print("PASS: frozen sources, displayed declarations, thirteen inputs, proof-source policy", flush=True)
        if args.check_docs:
            print("STATIC_ONLY_NOT_PROOF_CHECK")
            return 0
        destination.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        version = run(args.lake, ["env", "lean", "--version"], "toolchain.log").strip()
        if "version 4.28.0" not in version:
            raise ValueError(f"Actual Lean executable is not the pinned version: {version}")
        run(args.lake, ["build"], "build.log")
        audit = (ROOT / "Audit.lean").read_text(encoding="utf-8")
        output = run(args.lake, ["env", "lean", "--stdin"], "audit.log",
                     audit + "\n#audit_conditional_nl\n#audit_full_nl\n")
        if CONDITIONAL_MARKER not in output or "EXTERNAL_INTERFACE_CHECKED:" not in output:
            raise ValueError("Conditional certificate audit did not report success")
        declared_count = len(re.findall(r"^#audit_axioms ", audit, re.MULTILINE))
        if output.count("standard axioms only:") != declared_count:
            raise ValueError("Not every registered theorem completed its axiom audit")
        header = audit.split("\n#audit_axioms NormalLocus.", 1)[0]
        negative = negative_checks(args.lake, header)
        run(args.lake, ["env", "lean", "--run", "scripts/ReplayTest.lean"], "replay-self-test.log")
        run(args.lake, ["env", "lean", "-c", ".lake/build/certificate-replay.c",
                        "scripts/Replay.lean"], "replay-compile.log")
        binary = ".lake/build/certificate-replay" + (".exe" if sys.platform == "win32" else "")
        run(args.lake, ["env", "leanc", "-o", binary,
                        ".lake/build/certificate-replay.c", "-lLeanChecker"], "replay-link.log")
        run(args.lake, ["env", binary], "replay.log")
        replay = json.loads((ROOT / "verification/replay.json").read_text(encoding="utf-8"))
        if replay["status"] != "PASS" or replay["trust_level"] != 0:
            raise ValueError("Fresh kernel replay did not pass")
        check_manifest()
        check_documentation()
        if sha256(ROOT / "manifest.json") != initial_manifest:
            raise ValueError("Reviewed manifest changed during verification")
        complete = "FULL_NL_VERIFIED: exact target and standard axioms checked" in output
        report.update(status="CONDITIONAL_VERIFIED", toolchain=version,
                      mathlib_revision=MATHLIB_REV, manifest_sha256=sha256(ROOT / "manifest.json"),
                      audited_theorems=declared_count, negative_tests=negative,
                      kernel_replay=replay, unconditional_nl="VERIFIED" if complete else "INCOMPLETE",
                      checked_at=datetime.now(timezone.utc).isoformat(),
                      elapsed_seconds=round(time.monotonic() - started, 2))
        destination.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print("CONDITIONAL_VERIFIED: all executable checks passed; external inputs and trust assumptions remain")
        return 2 if args.require_complete and not complete else 0
    except Exception as error:
        if not args.check_docs:
            report.update(status="FAIL", error=str(error))
            destination.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
