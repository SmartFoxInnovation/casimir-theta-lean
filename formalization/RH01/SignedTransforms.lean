import RH01.HeatBoundary
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Holomorphic signed transforms

Write ζ₀(w) = ζ(w) - 1/(w-1), continued with value γ at 1. Using ζ₀ and its
divided difference makes the signed ramp response holomorphic across the pole
at 1 as well as across zeta zeros. The signed heat response uses the same ζ₀.
-/

namespace RH01

open Complex Filter Set
open scoped Topology

noncomputable section

local notation "γ" => (Real.eulerMascheroniConstant : ℂ)

/-- The continuation of ξ(w) times the centered ramp transform. -/
def signedRamp (w : ℂ) : ℂ :=
  Gammaℝ w / 2 *
    (-deriv riemannZeta₀ w + w * riemannZeta₀ w * (1 + γ) +
      (1 + γ - riemannZeta₀ w) - dslope riemannZeta₀ 1 w)

/-- The signed heat factor with the pole at 1 already canceled. -/
def regularHeatFactor (w : ℂ) : ℂ :=
  -(w * Gammaℝ w / 2) *
    ((w - 1) * (deriv riemannZeta₀ w + riemannZeta₀ w ^ 2) + 2 * riemannZeta₀ w)

theorem signedRamp_eq_cancelled {w : ℂ} (h₁ : w ≠ 1) :
    signedRamp w = Gammaℝ w / 2 *
      (-deriv riemannZeta w + w * riemannZeta w * (1 + γ - 1 / (w - 1))) := by
  unfold signedRamp
  rw [dslope_of_ne _ h₁, slope_def_module, smul_eq_mul, riemannZeta₀_one,
    deriv_riemannZeta_eq_neg_inv_sub_sq_add h₁, riemannZeta_eq_inv_sub_add h₁]
  field_simp [sub_ne_zero.mpr h₁]
  ring

theorem signedRamp_eq_xi_mul {w : ℂ} (h₀ : w ≠ 0) (h₁ : w ≠ 1) (hz : riemannZeta w ≠ 0) :
    signedRamp w = xi w * rampTransform w :=
  (signedRamp_eq_cancelled h₁).trans (xi_mul_rampTransform h₀ h₁ hz).symm

theorem regularHeatFactor_eq {w : ℂ} (h₁ : w ≠ 1) :
    regularHeatFactor w = signedHeatFactor w := by
  unfold regularHeatFactor signedHeatFactor
  rw [deriv_riemannZeta_eq_neg_inv_sub_sq_add h₁, riemannZeta_eq_inv_sub_add h₁]
  field_simp [sub_ne_zero.mpr h₁]
  ring

private theorem differentiableAt_GammaReal {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ Gammaℝ w := by
  have h : (Gammaℝ w)⁻¹ ≠ 0 := inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hw)
  have heq : (fun z : ℂ => ((Gammaℝ z)⁻¹)⁻¹) = Gammaℝ := funext fun _ => inv_inv _
  rw [← heq]
  exact (differentiable_Gammaℝ_inv w).inv h

/-- Both the pole at 1 and all zeros in the right half-plane have been filled in. -/
theorem differentiableOn_signedRamp :
    DifferentiableOn ℂ signedRamp {w : ℂ | 0 < w.re} := by
  have hds : Differentiable ℂ (dslope riemannZeta₀ 1) :=
    differentiableOn_univ.mp
      ((differentiableOn_dslope (univ_mem : Set.univ ∈ 𝓝 (1 : ℂ))).2
        differentiable_riemannZeta₀.differentiableOn)
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  have hG := differentiableAt_GammaReal hw
  have hd := differentiable_riemannZeta₀.deriv w
  have hz := differentiable_riemannZeta₀ w
  have hs := hds w
  unfold signedRamp
  fun_prop

theorem differentiableOn_regularHeatFactor :
    DifferentiableOn ℂ regularHeatFactor {w : ℂ | 0 < w.re} := by
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  have hG := differentiableAt_GammaReal hw
  have hd := differentiable_riemannZeta₀.deriv w
  have hz := differentiable_riemannZeta₀ w
  unfold regularHeatFactor
  fun_prop

/-- The two surviving first-order terms at the removed heat pole. -/
theorem regularHeatFactor_one : regularHeatFactor 1 = -γ := by
  simp [regularHeatFactor]

/-- Moving the real gamma factor up by two makes the cancellation at w=0
explicit. The remaining heat gamma factor still has the Casimir pole at -1. -/
def continuedHeatFactor (w : ℂ) : ℂ :=
  -(Real.pi : ℂ) * Gammaℝ (w + 2) *
    ((w - 1) * (deriv riemannZeta₀ w + riemannZeta₀ w ^ 2) + 2 * riemannZeta₀ w)

theorem continuedHeatFactor_eq {w : ℂ} (h₀ : w ≠ 0) :
    continuedHeatFactor w = regularHeatFactor w := by
  unfold continuedHeatFactor regularHeatFactor
  rw [Gammaℝ_add_two h₀]
  have hp := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hp]

theorem differentiableOn_continuedHeatFactor :
    DifferentiableOn ℂ continuedHeatFactor {w : ℂ | -2 < w.re} := by
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  have hre : -2 < w.re := hw
  have hpos : 0 < (w + 2).re := by simp; linarith
  have hG := differentiableAt_GammaReal hpos
  have hd := differentiable_riemannZeta₀.deriv w
  have hz := differentiable_riemannZeta₀ w
  unfold continuedHeatFactor
  fun_prop

/-- The continued signed heat response has the same Casimir residue. -/
theorem continuedHeat_residue_at_casimir :
    Tendsto (fun w : ℂ => (w + 1) * (Gamma (w + 1) * continuedHeatFactor w))
      (𝓝[≠] (-1 : ℂ)) (𝓝 (2 * (Real.pi : ℂ) * (deriv riemannZeta (-1) + 1 / 144))) := by
  apply signedThetaHeat_residue_at_casimir.congr'
  have h₀ : ∀ᶠ w : ℂ in 𝓝[≠] (-1 : ℂ), w ≠ 0 :=
    nhdsWithin_le_nhds (compl_singleton_mem_nhds (show (-1 : ℂ) ≠ 0 by norm_num))
  have h₁ : ∀ᶠ w : ℂ in 𝓝[≠] (-1 : ℂ), w ≠ 1 :=
    nhdsWithin_le_nhds (compl_singleton_mem_nhds (show (-1 : ℂ) ≠ 1 by norm_num))
  filter_upwards [h₀, h₁] with w h₀ h₁
  rw [continuedHeatFactor_eq h₀, regularHeatFactor_eq h₁]

#print axioms differentiableOn_signedRamp
#print axioms differentiableOn_continuedHeatFactor
#print axioms continuedHeat_residue_at_casimir

end
end RH01
