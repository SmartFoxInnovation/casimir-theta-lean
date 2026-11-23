"""Replay the pinned Alpöge imports and the RH01 adapters using stock Lean.

The source index supplies the build order and SHA-256 for each original file.
Each Lean invocation uses the upstream Lake options without writing a full
transitive Lake setup manifest. Build output stays in the supplied workspace.
"""

import argparse
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, FIRST_COMPLETED, wait
import gzip
import hashlib
import heapq
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile
import time


SOURCE_COMMIT = "371a1a26d5e17f604428e3a8ce6ce341cf517434"
ARCHIVE_SHA256 = "c0506dfc6a8172a1f06bf4021c874aa0f81709db95fc5ab488981cd049caf492"
INDEX_COMMIT = "3dfad138a23fc00951ee3a20d388cb6bd92924f7"
INDEX_SHA256 = "c4e2032331f0da7fafe9dc6046ca9430e899041f77c1985167c92f5b0ee7ea74"
LEAN_COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
MATHLIB_COMMIT = "0df444a360eaa60ab8c11dca51a86af692955474"
FORMALIZATION = Path(__file__).resolve().parents[1]
VWIN = "Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow"
TOP_MAIN = VWIN.rsplit(".", 1)[0] + ".TopMainZj"
ARITHMETIC = (
    "Development.AutomorphicArithmetic.PrimitiveCosets.GzEq",
    "Development.AutomorphicArithmetic.PrimitiveCosets.LevelGmLeOnFamilyScales",
)
OPTIONS = {
    "autoImplicit": False,
    "relaxedAutoImplicit": False,
    "maxSynthPendingDepth": 3,
    "pp.unicode.fun": True,
    "maxHeartbeats": 4_000_000,
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    with path.open("rb") as file:
        return hashlib.file_digest(file, "sha256").hexdigest()


def module_path(module, suffix):
    return Path(*module.split(".")).with_suffix(suffix)


def import_names(source):
    # The pinned archive uses one name per import line, including primed names.
    return re.findall(r"^(?:(?:public|meta|private)[ \t]+)?import[ \t]+(\S+)", source, re.M)


def load_index(index):
    with gzip.open(index, "rt", encoding="utf-8") as file:
        by_id = {row["id"]: row for line in file if (row := json.loads(line))}
    by_name = {row["module"]: row for row in by_id.values()}
    return by_id, by_name


def select_closure(by_id, by_name, roots):
    pending = list(roots)
    closure = {}
    while pending:
        name = pending.pop()
        if name not in closure:
            row = by_name[name]
            dependencies = [by_id[ref]["module"] for ref in row["imports"]]
            closure[name] = (row["source_sha256"], dependencies, row["depth"])
            pending.extend(dependencies)
    return closure


def critical_distances(closure):
    distances = dict.fromkeys(closure, 0)
    for name in sorted(closure, key=lambda name: closure[name][2], reverse=True):
        distance = distances[name] + 1
        for dep in closure[name][1]:
            distances[dep] = max(distances[dep], distance)
    return distances


def prepare_sources(archive, src, closure, by_name):
    prefix = f"riemann-hypothesis-{SOURCE_COMMIT}/src/"
    needed = {prefix + module_path(name, ".lean").as_posix(): name for name in closure}
    project_names = set(by_name)
    with tarfile.open(archive, "r|gz") as tree:
        for member in tree:
            if not member.isfile() or member.name not in needed:
                continue
            name = needed.pop(member.name)
            data = tree.extractfile(member).read()
            expected, dependencies, _ = closure[name]
            if hashlib.sha256(data).hexdigest() != expected:
                raise ValueError(f"Source hash differs for {name}")
            imports = set(import_names(data.decode("utf-8-sig")))
            if imports & project_names != set(dependencies):
                raise ValueError(f"Import index disagrees with source for {name}")
            path = src / module_path(name, ".lean")
            path.parent.mkdir(parents=True, exist_ok=True)
            if not path.is_file() or digest(path) != expected:
                path.write_bytes(data)
            verified = len(closure) - len(needed)
            if verified % 5000 == 0:
                print(f"Verified {verified:,}/{len(closure):,} upstream sources", flush=True)
            if not needed:
                break
    if needed:
        raise ValueError(f"Sources missing from the archive: {list(needed)[:5]}")


def run_lean(lean, cwd, env, output, log, *args, timeout=14400):
    start = time.monotonic()
    with log.open("wb") as stream:
        result = subprocess.run(
            [str(lean), *map(str, args)], cwd=cwd, env=env,
            stdout=stream, stderr=subprocess.STDOUT, timeout=timeout,
        )
    if result.returncode or not output.is_file():
        raise RuntimeError(f"Lean failed ({result.returncode}): {log}")
    return round(time.monotonic() - start, 3)


def compile_module(name, source_digest, src, objects, scratch, lean, env):
    source = module_path(name, ".lean")
    if digest(src / source) != source_digest:
        raise ValueError(f"The staged source no longer matches the pin: {name}")
    output = objects / module_path(name, ".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    token = hashlib.sha256(name.encode()).hexdigest()
    setup = scratch / f"{token}.json"
    log = scratch / f"{token}.log"
    temporary = scratch / f"{token}.olean"
    options = dict(OPTIONS)
    if name.startswith(("GroundTheory.LocalFields.", "GroundTheory.GlobalFields.")):
        options["synthInstance.maxHeartbeats"] = 400_000
    setup.write_text(json.dumps({
        "plugins": [], "package": "tree", "options": options, "name": name,
        "isModule": False, "importArts": {}, "dynlibs": [],
    }), encoding="utf-8")
    seconds = run_lean(
        lean, src, env, temporary, log,
        "--tstack=400000", "-j", 1, source, "-o", temporary, "--setup", setup,
    )
    temporary.replace(output)
    setup.unlink()
    if not log.stat().st_size:
        log.unlink()
    return {"module": name, "sha256": digest(output), "seconds": seconds}


def build_closure(closure, priority, src, objects, scratch, lean, env, journal, jobs, limit, pause):
    completed = set()
    ledgers = (journal, journal.with_name("frontier-built.jsonl"))
    for ledger in ledgers:
        if not ledger.is_file():
            continue
        for line in ledger.read_text(encoding="utf-8").splitlines():
            record = json.loads(line)
            name = record["module"]
            path = objects / module_path(name, ".olean")
            if name in closure and path.is_file() and digest(path) == record["sha256"]:
                completed.add(name)
    downstream = defaultdict(list)
    unresolved = {}
    distances = critical_distances(closure)
    ready = []
    for name, (_, deps, _) in closure.items():
        if name in completed:
            continue
        outstanding = set(deps) - completed
        unresolved[name] = len(outstanding)
        for dep in outstanding:
            downstream[dep].append(name)
        if not outstanding:
            heapq.heappush(ready, (name not in priority, -distances[name], name))
    print(f"Resuming with {len(completed):,}/{len(closure):,} verified objects", flush=True)
    built = 0
    issued = 0
    running = {}
    with ThreadPoolExecutor(max_workers=jobs) as pool, journal.open("a", encoding="utf-8") as log:
        while running or ready:
            while ready and len(running) < jobs and (limit is None or issued < limit) and not pause.exists():
                _, _, name = heapq.heappop(ready)
                future = pool.submit(
                    compile_module, name, closure[name][0], src, objects, scratch, lean, env,
                )
                running[future] = name
                issued += 1
            if not running:
                break
            finished, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in finished:
                name = running.pop(future)
                try:
                    record = future.result()
                except Exception as exc:
                    raise RuntimeError(f"Failed while building {name}") from exc
                log.write(json.dumps(record) + "\n")
                log.flush()
                built += 1
                completed.add(name)
                for consumer in downstream[name]:
                    unresolved[consumer] -= 1
                    if not unresolved[consumer]:
                        heapq.heappush(ready, (consumer not in priority, -distances[consumer], consumer))
                if built % 25 == 0 or len(completed) == len(closure):
                    print(f"{len(completed):,}/{len(closure):,} checked; last {name}", flush=True)
    print(f"Finished this invocation: {built:,} new, {len(completed):,}/{len(closure):,} total", flush=True)
    if pause.exists():
        print(f"Paused after recording finished modules. Remove {pause} to resume.", flush=True)
    elif len(completed) != len(closure) and limit is None:
        raise RuntimeError("Build graph stopped with unresolved modules")
    return len(completed) == len(closure)


def replay_adapters(lean, env, objects, work, identity, upstream_count, full):
    adapter_root = FORMALIZATION / "upstream"
    if full:
        targets = ("PublishedWindowArithmetic", "PublishedWindows", "PublishedMellin", "PublishedCasimir")
        theorem = "RH01.casimirRiemannHypothesis"
        checked = (TOP_MAIN, VWIN, *targets)
        label = "publication"
    else:
        targets = ("PublishedWindowArithmetic", "PublishedMellin", "CasimirFamilyAudit")
        theorem = "RH01.casimir_of_conductor_one_family_windows"
        checked = ("RH01.HeatBoundary", *targets)
        label = "conditional"
    eligible = work / f"verified-{label}.json"
    sources = [
        FORMALIZATION / name
        for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml", "RH01.lean")
    ]
    sources.extend(sorted((FORMALIZATION / "RH01").glob("*.lean")))
    sources.extend(adapter_root / (target + ".lean") for target in targets)
    source_hashes = {source.relative_to(FORMALIZATION).as_posix(): digest(source) for source in sources}
    lake = lean.with_name("lake" + lean.suffix)
    build_env = dict(env, PATH=str(lean.parent) + os.pathsep + env.get("PATH", ""))
    with (work / f"{label}-local-build.log").open("wb") as log:
        subprocess.run(
            [str(lake), "build", "+RH01", "+RH01.PublicationAudit"], cwd=FORMALIZATION,
            env=build_env, stdout=log, stderr=subprocess.STDOUT, check=True,
        )
    adapter_hashes = {}
    for target in targets:
        source = adapter_root / (target + ".lean")
        log = work / (target + ".log")
        output = objects / (target + ".olean")
        source_hash = digest(source)
        run_lean(lean, adapter_root, env, output, log, "--tstack=400000",
                 "-DmaxHeartbeats=4000000", "-DautoImplicit=false", source, "-o", output)
        if digest(source) != source_hash:
            raise RuntimeError(f"The source changed during the replay of {target}")
        adapter_hashes[target] = {"source_sha256": source_hash, "olean_sha256": digest(output)}
        print(log.read_text(encoding="utf-8"), end="", flush=True)
    audit = (work / (targets[-1] + ".log")).read_text(encoding="utf-8")
    match = re.search(rf"'{re.escape(theorem)}' depends on axioms: \[([^\]]*)\]", audit)
    if not match or set(match[1].split(", ")) != ALLOWED_AXIOMS:
        raise RuntimeError("The final theorem's axiom audit differs from the expected three")
    if f"{theorem} uses the expected proof route" not in audit:
        raise RuntimeError("The proof dependency audit is missing")
    checker = lean.with_name("leanchecker" + lean.suffix)
    kernel_log = work / ("kernel-replay.log" if full else "conditional-kernel-replay.log")
    with kernel_log.open("wb") as log:
        for target in checked:
            subprocess.run(
                [str(checker), "-v", target], cwd=adapter_root, env=env,
                stdout=log, stderr=subprocess.STDOUT, check=True,
            )
    if any(digest(FORMALIZATION / path) != expected for path, expected in source_hashes.items()):
        raise RuntimeError("A local proof source changed during the publication replay")
    receipt = {
        "theorem": theorem,
        "statement": "RiemannHypothesis" if full else "Conductor-one family-window estimate implies RiemannHypothesis",
        "axioms": sorted(ALLOWED_AXIOMS),
        "lean_commit": LEAN_COMMIT,
        "mathlib_commit": MATHLIB_COMMIT,
        "upstream_commit": SOURCE_COMMIT,
        "upstream_objects": upstream_count,
        "source_identity": identity,
        "adapters": adapter_hashes,
        "local_source_sha256": source_hashes,
        "kernel_checked": list(checked),
        "kernel_log_sha256": digest(kernel_log),
    }
    if full:
        receipt["window_objects"] = {
            name: digest(objects / module_path(name, ".olean")) for name in (TOP_MAIN, VWIN)
        }
    temporary = eligible.with_suffix(".tmp")
    temporary.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    temporary.replace(eligible)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--index", type=Path, required=True)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--slice", choices=("arithmetic", "conditional", "top", "window"), default="window")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--prepare-only", action="store_true")
    args = parser.parse_args()
    if args.jobs < 1 or (args.limit is not None and args.limit < 1):
        parser.error("jobs and limit must be positive")
    if digest(args.archive) != ARCHIVE_SHA256:
        raise SystemExit("The source archive does not match the pinned digest.")
    if digest(args.index) != INDEX_SHA256:
        raise SystemExit("The dependency index does not match the pinned digest.")
    lean = args.lean.resolve()
    version = subprocess.check_output([str(lean), "--version"], text=True).strip()
    if LEAN_COMMIT not in version:
        raise SystemExit(f"Unexpected Lean toolchain: {version}")
    packages = FORMALIZATION / ".lake" / "packages"
    mathlib = packages / "mathlib"
    revision = subprocess.check_output(["git", "-C", str(mathlib), "rev-parse", "HEAD"], text=True).strip()
    if revision != MATHLIB_COMMIT:
        raise SystemExit(f"Unexpected Mathlib commit: {revision}")
    workspace = args.work.resolve()
    workspace.mkdir(parents=True, exist_ok=True)
    src, objects, scratch = (workspace / name for name in ("src", "objects", "attempts"))
    for folder in (src, objects, scratch):
        folder.mkdir(exist_ok=True)
    package_roots = sorted(packages.glob("*/.lake/build/lib/lean"))
    mathlib_root = mathlib / ".lake" / "build" / "lib" / "lean"
    package_roots.remove(mathlib_root)
    local_root = FORMALIZATION / ".lake" / "build" / "lib" / "lean"
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, (
        objects, mathlib_root, *package_roots, local_root,
    ))))
    roots = list(ARITHMETIC)
    if args.slice in ("conditional", "window"):
        adapters = ["PublishedWindowArithmetic.lean"]
        if args.slice == "window":
            adapters.append("PublishedWindows.lean")
        adapters.append("PublishedMellin.lean")
        for path in adapters:
            roots.extend(import_names((FORMALIZATION / "upstream" / path).read_text(encoding="utf-8")))
        roots = list(dict.fromkeys(name for name in roots if not name.startswith(("RH01.", "Published"))))
        if args.slice == "window" and VWIN not in roots:
            raise RuntimeError("The adapter no longer imports the pinned VwinOfRow module")
    elif args.slice == "top":
        roots = [TOP_MAIN]
    by_id, by_name = load_index(args.index)
    closure = select_closure(by_id, by_name, roots)
    priority = select_closure(by_id, by_name, [TOP_MAIN]) if args.slice == "window" else closure
    print(version, flush=True)
    print(f"{args.slice} closure: {len(closure):,} modules; source pin {SOURCE_COMMIT}", flush=True)
    stamp = workspace / (f"prepared-{args.slice}.json")
    identity = {"archive": ARCHIVE_SHA256, "index": INDEX_SHA256, "roots": roots}
    if not stamp.is_file() or json.loads(stamp.read_text(encoding="utf-8")) != identity:
        prepare_sources(args.archive, src, closure, by_name)
        stamp.write_text(json.dumps(identity, indent=2) + "\n", encoding="utf-8")
    if args.prepare_only:
        print(f"Verified and staged {len(closure):,} pinned source files", flush=True)
        return
    finished = build_closure(closure, priority, src, objects, scratch, lean, env,
                             workspace / "built.jsonl", args.jobs, args.limit, workspace / "pause")
    if finished and args.slice == "arithmetic":
        run_lean(lean, FORMALIZATION / "upstream", env,
                 objects / "PublishedWindowArithmetic.olean", workspace / "PublishedWindowArithmetic.log",
                 "--tstack=400000", "-DmaxHeartbeats=4000000", "-DautoImplicit=false",
                 "PublishedWindowArithmetic.lean", "-o", objects / "PublishedWindowArithmetic.olean")
        print((workspace / "PublishedWindowArithmetic.log").read_text(encoding="utf-8"), end="")
    if finished and args.slice in ("conditional", "window"):
        full = args.slice == "window"
        replay_adapters(lean, env, objects, workspace, identity, len(closure), full)
        print(f"The {args.slice} target passed the axiom audit and kernel replay.", flush=True)
    return 0 if finished or args.limit is not None else 2


if __name__ == "__main__":
    raise SystemExit(main())
