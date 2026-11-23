"""Rebuild the unconditional Casimir proof using the pinned MIT proof export."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

from fetch_pins import INPUTS, fetch
from replay_windows import FORMALIZATION, LEAN_COMMIT, MATHLIB_COMMIT, digest


UPSTREAM = FORMALIZATION / "upstream"
TOOLS = UPSTREAM / "export"
EXPORT_URL = "https://math.mit.edu/~drew/grh/solution.ndjson.zst"
EXPORT_COMPRESSED = "61a8938ad5f5e57397c1c0e3b954916af546d9004ade01c3555744a681b05381"
EXPORT_RAW = "5ea74b912147c5c93cc2b6d70cc727cf908df2f62ac6a20480a3fa02f6be244e"
CLOSURE = "c5f05616fe0a4f72dcdf7c183f66548e0dee951dab8d3c9318a2e52be46514f7"
WINDOW_SOURCE = "d19cab6578ddf9225ac2d9787f2761a4d311dfd834ab691b102788071a10beb9"
BASE_IMPORTS = "Mathlib,PublishedWindowArithmetic"
THEOREM = "RH01.casimirRiemannHypothesis"
AXIOMS = ["Classical.choice", "Quot.sound", "propext"]


def run(*command, cwd=None, env=None, log=None):
    if log is None:
        subprocess.run(command, cwd=cwd, env=env, check=True)
        return
    with log.open("wb") as output:
        subprocess.run(command, cwd=cwd, env=env, stdout=output, stderr=subprocess.STDOUT, check=True)


def require_digest(path, expected):
    if digest(path) != expected:
        raise ValueError(f"SHA-256 mismatch: {path}")


def prepare_export(directory, raw):
    if raw is not None:
        require_digest(raw, EXPORT_RAW)
        return raw
    archive = directory / "solution.ndjson.zst"
    raw = directory / "solution.ndjson"
    if not archive.exists():
        partial = archive.with_suffix(".zst.part")
        run("curl", "--fail", "--location", "--retry", "3", "--continue-at", "-",
            "--output", partial, EXPORT_URL)
        require_digest(partial, EXPORT_COMPRESSED)
        partial.replace(archive)
    require_digest(archive, EXPORT_COMPRESSED)
    if not raw.exists():
        partial = raw.with_suffix(".ndjson.part")
        run("zstd", "-df", "--long=30", archive, "-o", partial)
        require_digest(partial, EXPORT_RAW)
        partial.replace(raw)
    require_digest(raw, EXPORT_RAW)
    return raw


def prepare_batches(proof, raw, selector, packer, lean, jobs, env):
    base_names = proof / "base-names.ndjson"
    run(lean, "--run", "ExportBaseNames.lean", base_names, *BASE_IMPORTS.split(","),
        cwd=TOOLS / "packer", env=env)
    roots = (TOOLS / "window-inputs.txt").read_text(encoding="utf-8").splitlines()
    index = proof / "index"
    run(*selector, raw, index, base_names, *roots)
    closure = proof / "selected.declarations.u64"
    run(*selector, "closure", raw, index, closure)
    require_digest(closure, CLOSURE)
    ranges = subprocess.check_output(
        [sys.executable, TOOLS / "export_batch_ranges.py", closure, "2000000000"], text=True,
    ).splitlines()
    if len(ranges) != 31:
        raise ValueError(f"Unexpected batch partition with {len(ranges)} ranges")
    batches = []
    parent = BASE_IMPORTS
    for position, bounds in enumerate(ranges, 1):
        module = f"PackedPublishedBatch{position:03d}"
        start, end = map(int, bounds.split())
        batches.append({"module": module, "parent": parent, "source_start": start, "source_end": end})
        parent = module

    def pack(batch):
        module = batch["module"]
        staged = proof / f"{module}.ndjson"
        log = proof / f"{module}.selection.log"
        run(*selector, "batch-select", raw, index, staged, closure,
            str(batch["source_start"]), str(batch["source_end"]), log=log)
        candidate = proof / f"{module}.olean"
        run(packer, staged, candidate, module, batch["parent"], base_names,
            log=proof / f"{module}.pack.log")
        staged.unlink()
        return dict(batch, sha256=digest(candidate))

    with ThreadPoolExecutor(jobs) as pool:
        return list(pool.map(pack, batches))


def use_existing_batches(candidate_dir, ledger):
    batches = [json.loads(row) for row in ledger.read_text(encoding="utf-8").splitlines()]
    expected = [f"PackedPublishedBatch{i:03d}" for i in range(1, 32)]
    if [batch["module"] for batch in batches] != expected:
        raise ValueError("The candidate ledger must list all 31 expected modules in order")
    for batch, parent in zip(batches, [BASE_IMPORTS, *expected[:-1]]):
        if batch["parent"] != parent:
            raise ValueError(f"Unexpected parent of {batch['module']}")
        require_digest(candidate_dir / f"{batch['module']}.olean", batch["sha256"])
    return batches


def replay_batches(batches, candidate_dir, proof, checker, env, jobs):
    def replay(batch):
        module = batch["module"]
        candidate = candidate_dir / f"{module}.olean"
        require_digest(candidate, batch["sha256"])
        log = proof / f"{module}.kernel.log"
        run(checker, "-v", module, cwd=proof, env=env, log=log)
        if f"replaying {module}" not in log.read_text(encoding="utf-8").splitlines():
            raise ValueError(f"Missing kernel replay for {module}")
        require_digest(candidate, batch["sha256"])
        print(f"Kernel accepted {module}", flush=True)

    with ThreadPoolExecutor(jobs) as pool:
        list(pool.map(replay, reversed(batches)))


def replay_final_modules(proof, modules, checker, env):
    kernel_log = proof / "kernel-replay.log"
    with kernel_log.open("wb") as combined:
        for module in modules:
            log = proof / f"{module}.kernel.log"
            run(checker, "-v", module, cwd=proof, env=env, log=log)
            output = log.read_bytes()
            if f"replaying {module}".encode() not in output.splitlines():
                raise ValueError(f"Missing final kernel replay for {module}")
            combined.write(output)
            combined.flush()


def finish(proof, batch_tail, lean, checker, env):
    window = UPSTREAM / "PublishedWindows.lean"
    require_digest(window, WINDOW_SOURCE)
    original = window.read_bytes()
    adapter_body = original[original.index(b"import PublishedWindowArithmetic"):]
    proof_sources = {
        "RecoveredPublishedInputs": f"prelude\nimport {batch_tail}\n".encode(),
        "RecoveredPublishedNamespaces": (
            "import RecoveredPublishedInputs\n"
            + "".join(f"namespace {name}\nend {name}\n" for name in (
                "GlobalTheory.EX", "GlobalTheory.Fc", "UpperTheory.Top", "UpperTheory.LiteratureTheorems",
            ))
        ).encode(),
        "PublishedWindows": b"import RecoveredPublishedNamespaces\n" + adapter_body,
        "PublishedCasimir": (UPSTREAM / "PublishedCasimir.lean").read_bytes(),
        "EndToEndAudit": (UPSTREAM / "EndToEndAudit.lean").read_bytes(),
    }
    for module, content in proof_sources.items():
        source = proof / f"{module}.lean"
        source.write_bytes(content)
        run(lean, "--tstack=400000", "-DmaxHeartbeats=4000000", "-DautoImplicit=false",
            source.name, "-o", f"{module}.olean", cwd=proof, env=env, log=proof / f"{module}.log")

    audit = (proof / "EndToEndAudit.log").read_text(encoding="utf-8")
    for theorem in (THEOREM, "RH01.continuedHeat_residue_at_casimir"):
        axiom_line = re.search(rf"'{re.escape(theorem)}' depends on axioms: \[([^\]]+)\]", audit)
        if not axiom_line or sorted(axiom_line[1].split(", ")) != AXIOMS:
            raise ValueError(f"Axiom audit did not pass for {theorem}")
        if f"{theorem} uses the expected proof route" not in audit:
            raise ValueError(f"Proof dependency audit did not pass for {theorem}")
    checked = ["RH01.HeatBoundary", "RH01.SignedTransforms", "PublishedWindowArithmetic",
               "PublishedMellin", *proof_sources]
    replay_final_modules(proof, checked, checker, env)
    return checked


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("work", type=Path)
    parser.add_argument("--lean", required=True, type=Path, help="Path to the real pinned Lean executable")
    parser.add_argument("--raw-export", type=Path, help="Reuse the pinned, unpacked MIT export")
    parser.add_argument("--pins-dir", type=Path, help="Location of the pinned source archive and import index")
    parser.add_argument("--indexer", type=Path, help="Use an already built ExportIndex executable")
    parser.add_argument("--batch-dir", type=Path, help="Replay already packed batches from an earlier run")
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    lean = args.lean.resolve()
    if LEAN_COMMIT not in subprocess.check_output([lean, "--version"], text=True):
        parser.error("Expected Lean 4.33.1 at the pinned commit")
    lake = lean.with_name("lake" + lean.suffix)
    checker = lean.with_name("leanchecker" + lean.suffix)
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=True)
    # A new output directory prevents a stale success receipt after a failed rerun.
    proof = work / "proof"
    proof.mkdir()
    inputs = (args.pins_dir or work / "inputs").resolve()
    inputs.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, PATH=str(lean.parent) + os.pathsep + os.environ["PATH"])
    env.pop("LEAN_PATH", None)
    run(lake, "exe", "cache", "get", cwd=FORMALIZATION, env=env, log=work / "mathlib-cache.log")
    for name, url, checksum in INPUTS:
        fetch(inputs / name, url, checksum)
    base = work / "base"
    run(sys.executable, UPSTREAM / "replay_windows.py", "--slice", "conditional",
        "--archive", inputs / INPUTS[0][0], "--index", inputs / INPUTS[1][0],
        "--work", base, "--lean", lean, "--jobs", str(args.jobs), env=env, log=work / "base.log")
    if not (base / "verified-conditional.json").is_file():
        raise ValueError("The fresh arithmetic and local base replay did not pass")
    packages = FORMALIZATION / ".lake/packages"
    candidate_dir = args.batch_dir.resolve() if args.batch_dir else proof
    env["LEAN_PATH"] = os.pathsep.join(map(str, dict.fromkeys((
        proof, base / "objects", FORMALIZATION / ".lake/build/lib/lean",
        *sorted(packages.glob("*/.lake/build/lib/lean")), candidate_dir,
    ))))

    if args.batch_dir:
        batches = use_existing_batches(candidate_dir, candidate_dir / "replayed-batches.jsonl")
    else:
        raw = prepare_export(inputs, args.raw_export.resolve() if args.raw_export else None)
        if args.indexer:
            selector = [args.indexer.resolve()]
        else:
            run("dotnet", "build", TOOLS / "ExportIndex/ExportIndex.csproj", "-c", "Release",
                "-o", work / "indexer", log=work / "indexer-build.log")
            selector = ["dotnet", work / "indexer/ExportIndex.dll"]
        packer_project = work / "packer"
        shutil.copytree(TOOLS / "packer", packer_project)
        packer_env = dict(env)
        packer_env.pop("LEAN_PATH")
        run(lake, "build", cwd=packer_project, env=packer_env, log=work / "packer-build.log")
        packer = packer_project / ".lake/build/bin" / ("pack-published-terms" + lean.suffix)
        batches = prepare_batches(proof, raw, selector, packer, lean, args.jobs, env)
    replay_batches(batches, candidate_dir, proof, checker, env, args.jobs)
    checked = finish(proof, batches[-1]["module"], lean, checker, env)
    ledger = proof / "replayed-batches.jsonl"
    ledger.write_text("".join(json.dumps(batch) + "\n" for batch in batches), encoding="utf-8")
    receipt = {
        "theorem": THEOREM, "statement": "_root_.RiemannHypothesis", "axioms": AXIOMS,
        "lean_commit": LEAN_COMMIT, "mathlib_commit": MATHLIB_COMMIT,
        "arithmetic_input": "packed objects" if args.batch_dir else "pinned MIT export",
        "export_sha256": None if args.batch_dir else EXPORT_RAW,
        "closure_declarations_sha256": None if args.batch_dir else CLOSURE,
        "batches_kernel_checked": len(batches), "modules_kernel_checked": checked,
        "sha256": {name: digest(proof / name) for name in (
            "PublishedWindows.lean", "PublishedCasimir.lean", "EndToEndAudit.lean",
            "EndToEndAudit.log", "kernel-replay.log", ledger.name,
        )},
    }
    (proof / "verified-publication.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(f"Verified {THEOREM} through {len(batches)} arithmetic batches", flush=True)


if __name__ == "__main__":
    main()
