# The Line Between the Waves

**A Casimir-inspired route to the Riemann Hypothesis in Lean**  
21 November 2026

[Paper (PDF)](docs/casimir-theta.pdf) · [Final Lean verification](verification/README.md) · [v1.0.0 release notes](RELEASE_NOTES.md)

The Lean kernel accepted [`RH01.casimirRiemannHypothesis`](formalization/upstream/PublishedCasimir.lean) with conclusion `_root_.RiemannHypothesis` and exactly three axioms: `propext`, `Classical.choice`, and `Quot.sound`.

The proof uses the published Alpöge–Claude conductor-one window estimate and a centered-ramp Mellin identity. The local theta argument turns a hypothetical zero to the right of the critical line into a residue whose growth violates the window bound. Mathlib's functional equation gives the other half. The [dependency audit](formalization/upstream/EndToEndAudit.lean) checks that the local proof uses these arithmetic inputs and excludes the upstream headline theorem and its zero-exclusion step. [Published arithmetic proof and export](https://math.mit.edu/~drew/grh/)

The Casimir calculation motivates subtracting the matched background before estimating the remainder. Lean checks `ζ(-1) = -1/12` and the corresponding signed heat residue in separate theorems. [Heat calculation](formalization/RH01/HeatBoundary.lean)

## Build the local Lean library

Install Elan and Git. The toolchain file selects Lean 4.33.1. Run these commands from the repository root.

```sh
cd formalization
lake exe cache get
lake build +RH01 +RH01.PublicationAudit
```

This builds the local analytic argument and audit. The full theorem also needs the published arithmetic proof terms recovered by the replay below.

## Replay the full theorem

Use Linux with Elan, Git, Python 3.11 or later, .NET SDK 10, curl, and Zstandard. Allow at least 150 GB of free space for the export, index, and compiled objects. The pinned export is 7.7 GB compressed and 61.6 GB unpacked. Reduce `--jobs` if memory is limited.

Run from the repository root.

```sh
sha256sum -c SHA256SUMS
elan toolchain install "$(cat formalization/lean-toolchain)"
lean="$(cd formalization && elan which lean)"
python3 formalization/upstream/replay_export.py .replay-export --lean "$lean" --jobs 4
```

The runner verifies the input hashes, rebuilds the 407-module arithmetic base, and selects the required declarations into 31 batches. Lean's kernel replays each batch and the final modules. A successful run writes `.replay-export/proof/verified-publication.json`. Use `--raw-export FILE` to supply an existing unpacked export. [Replay options and source map](formalization/README.md)

## Checked release

The end-to-end replay rebuilt all 31 batches and checked each one against a fresh arithmetic base. The final release check verified their hashes, compiled the exact-statement audit again, and replayed all nine final modules. [End-to-end receipt](verification/end-to-end.json) · [Final replay receipt](verification/final-kernel-check.json)

OpenAI's GPT-6.2 Astra and Sol models assisted with research, Lean formalization, and manuscript preparation. OpenAI's ImageGen produced the cover. The bundled lean4export parser retains its Apache-2.0 license. [Parser license](formalization/upstream/export/packer/LICENSE)
