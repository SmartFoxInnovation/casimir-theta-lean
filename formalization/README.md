# Lean source map

[Repository README](../README.md) · [Paper](../docs/casimir-theta.pdf) · [Final Lean verification](../verification/README.md)

| Source | Role |
| --- | --- |
| [RH01/Casimir.lean](RH01/Casimir.lean) | Defines the centered ramp and window bound. Proves the contradiction and the reflection step. |
| [RH01/Detector.lean](RH01/Detector.lean) | Constructs the signed theta detector, including domination, the nonzero residue, and the off-window bound. |
| [upstream/PublishedWindowArithmetic.lean](upstream/PublishedWindowArithmetic.lean) | Converts the conductor-one family estimate into the local window bound. |
| [upstream/PublishedWindows.lean](upstream/PublishedWindows.lean) | Proves the window bound using the published arithmetic construction. |
| [upstream/PublishedMellin.lean](upstream/PublishedMellin.lean) | Identifies the Mellin transform of the same centered ramp. |
| [upstream/PublishedCasimir.lean](upstream/PublishedCasimir.lean) | States the unconditional theorem. |
| [upstream/EndToEndAudit.lean](upstream/EndToEndAudit.lean) | Checks the explicit zero statement, proof dependencies, and the three axioms. |
| [RH01/HeatBoundary.lean](RH01/HeatBoundary.lean) and [RH01/SignedTransforms.lean](RH01/SignedTransforms.lean) | Prove the separate Casimir value and signed heat residue. |

The [toolchain](lean-toolchain) pins Lean 4.33.1 and the [Lake manifest](lake-manifest.json) pins Mathlib and its dependencies. The [export replay](upstream/replay_export.py) verifies the published source archive, import index, and MIT proof export against pinned SHA-256 digests. From the repository root, run `python3 formalization/upstream/replay_export.py --help` for input and replay options.

The [source-module runner](upstream/replay_windows.py) also supports the original source closure. Use `--slice conditional` for the 407-module arithmetic base and local implication, or `--slice window` for the much larger original-source build. The [main README](../README.md#replay-the-full-theorem) gives the export command used for the checked release.
