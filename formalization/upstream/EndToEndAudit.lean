import PublishedCasimir
import RH01.SignedTransforms

namespace RH01

-- Spell out the Mathlib target so a change in the statement cannot silently pass.
example (s : ℂ) (hz : riemannZeta s = 0)
    (hn : ¬ ∃ n : ℕ, s = -2 * (n + 1)) (h₁ : s ≠ 1) : s.re = 1 / 2 :=
  casimirRiemannHypothesis s hz hn h₁

example : riemannZeta (-1) = (-1 : ℂ) / 12 :=
  casimirValue

#print axioms casimirRiemannHypothesis
#print axioms continuedHeat_residue_at_casimir

set_option maxHeartbeats 0 in
run_cmd do
  PublicationAudit.checkStandardAxioms `RH01.casimirRiemannHypothesis
  PublicationAudit.checkDependencies `RH01.casimirRiemannHypothesis
    [`UpperTheory.One.vwin_of_row,
      `UpperTheory.Comparison₂.level_gm_le_on_family_scales,
      `Deduction.mellin_Gchi_modOne, `RH01.publishedPrimeWindowBound, `RH01.primeRamp_mellin,
      `RH01.bilateralLaplace_thetaWeight_eq_completedXi, `RH01.thetaWeight_pos,
      `RH01.zeta_factor_at_zero, `RH01.exists_theta_probe, `RH01.signedRamp_divided_pole_of_factor,
      `RH01.ramp_convolution_eq_normalized_mellinInv, `RH01.mellinInv_signedRamp_shift,
      `RH01.mellinInv_dividedRamp_shift_of_decomp,
      `RH01.eventually_thetaWindowTail_le_one, `RH01.noThetaCertificate_of_primeWindowBound,
      `RH01.riemannHypothesis_of_no_right_zero, `completedRiemannZeta_one_sub]
    [`riemannHypothesis, `UpperTheory.Comparison₂.formB,
      `UpperTheory.FinalTheorems.everyCharacter, `RH01.casimirValue]
  PublicationAudit.checkStandardAxioms `RH01.continuedHeat_residue_at_casimir
  PublicationAudit.checkDependencies `RH01.continuedHeat_residue_at_casimir
    [`RH01.signedThetaHeat_residue_at_casimir, `RH01.casimirValue] []

end RH01
