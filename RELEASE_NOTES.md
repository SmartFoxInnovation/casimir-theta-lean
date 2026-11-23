# v1.0.0 · The Line Between the Waves

This release contains the paper, Lean sources, and replay tools for `RH01.casimirRiemannHypothesis`. Lean 4.33.1 accepted Mathlib's unconditional Riemann Hypothesis statement using exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Published inputs

The Alpöge–Claude formalization supplies the conductor-one family-window estimate and the Mellin identity for the centered prime ramp. The replay rebuilds the required proof terms from the pinned source and proof export. [Published proof export and verification](https://math.mit.edu/~drew/grh/)

## Our proof path

The local adapter turns the published family estimate into a one-sided bound on arbitrarily late windows. The theta argument combines that bound with signed cancellation to control the full detector integral. A zero at distance $b>0$ to the right of the critical line produces a residue term of order $Y^{5b/4}$, while the detector integral is bounded by order $Y^{3b/4}$. The rates contradict each other on sufficiently late windows. Mathlib's functional equation handles the left half. [Theta detector](formalization/RH01/Detector.lean) · [Dependency audit](formalization/upstream/EndToEndAudit.lean)

The Casimir calculation motivates subtracting a matching background before estimating the remainder. Lean checks $\zeta(-1)=-1/12$ and the signed heat residue in a separate calculation. [Heat boundary](formalization/RH01/HeatBoundary.lean)

## Verification

The end-to-end run rebuilt the 407-module arithmetic base and replayed all 31 recovered proof batches. The final run checked their hashes, compiled the exact-statement audit again, and replayed all nine final modules. [End-to-end receipt](verification/end-to-end.json) · [Final replay receipt](verification/final-kernel-check.json) · [Replay instructions](README.md#replay-the-full-theorem) · [Paper (PDF)](docs/casimir-theta.pdf)
