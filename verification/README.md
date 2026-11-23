# Final Lean verification

Lean 4.33.1 checked `RH01.casimirRiemannHypothesis` against Mathlib’s `RiemannHypothesis`. The final audit reports the three standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

- [Final audit](final-audit.log) and [final kernel replay](final-kernel-replay.log) record the accepted theorem and the nine modules replayed.
- [Final replay receipt](final-kernel-check.json) records the toolchain, Mathlib pin, module list, and hashes. Its `EndToEndAudit.log` and `kernel-replay.log` entries correspond to the two final logs above.
- [End-to-end receipt](end-to-end.json) records the fresh build and all 31 verified arithmetic batches. It preserves the original run inventory. The [batch ledger](reconstructed-batches.jsonl) records the batch hashes.

The full replay commands and input requirements are in the [repository README](../README.md#replay-the-full-theorem).
