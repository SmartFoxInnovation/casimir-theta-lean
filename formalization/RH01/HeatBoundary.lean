import RH01.Casimir
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# The Casimir heat boundary

The signed heat response has Mellin factor Γ(w + 1)(-ζ′(w)/ζ(w) - ζ(w)).
Multiplying by ξ cancels the denominator. At w = -1 the remaining factor is
regular and the residue of Γ(w + 1) preserves the exact Casimir contribution.
-/

namespace RH01

open Filter
open scoped Topology

noncomputable section

/-- The signed prime heat trace minus the full integer heat trace, in Mellin
coordinates. -/
def heatTransform (w : ℂ) : ℂ :=
  Complex.Gamma (w + 1) * (-deriv riemannZeta w / riemannZeta w - riemannZeta w)

/-- The regular factor after multiplication by ξ and cancellation of ζ. -/
def signedHeatFactor (w : ℂ) : ℂ :=
  -(w * (w - 1) * Complex.Gammaℝ w / 2) *
    (deriv riemannZeta w + riemannZeta w ^ 2)

theorem xi_mul_heatTransform {w : ℂ} (hz : riemannZeta w ≠ 0) :
    xi w * heatTransform w = Complex.Gamma (w + 1) * signedHeatFactor w := by
  unfold xi heatTransform signedHeatFactor
  field_simp [hz]
  ring

/-- The continued integer-mode sum at the Casimir endpoint. -/
theorem casimirValue : riemannZeta (-1) = (-1 : ℂ) / 12 := by
  have h := riemannZeta_neg_nat_eq_bernoulli 1
  norm_num [bernoulli_two] at h ⊢
  exact h

private theorem gammaReal_neg_one :
    Complex.Gammaℝ (-1) = -2 * (Real.pi : ℂ) := by
  have h := Complex.Gammaℝ_add_two (s := (-1 : ℂ)) (by norm_num)
  have harg : (-1 : ℂ) + 2 = 1 := by norm_num
  rw [harg, Complex.Gammaℝ_one] at h
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply (eq_div_iff hpi).mp at h
  linear_combination 2 * h

theorem signedHeatFactor_at_casimir :
    signedHeatFactor (-1) = 2 * (Real.pi : ℂ) * (deriv riemannZeta (-1) + 1 / 144) := by
  rw [signedHeatFactor, gammaReal_neg_one, casimirValue]
  ring

/-- The signed theta heat factor has the punctured limit defining its residue
at the Casimir endpoint. The coefficient includes the square of -1/12. -/
theorem signedThetaHeat_residue_at_casimir :
    Tendsto (fun w : ℂ => (w + 1) * (Complex.Gamma (w + 1) * signedHeatFactor w))
      (𝓝[≠] (-1 : ℂ)) (𝓝 (2 * (Real.pi : ℂ) * (deriv riemannZeta (-1) + 1 / 144))) := by
  have hshift : Tendsto (fun w : ℂ => w + 1) (𝓝[≠] (-1 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h : ContinuousAt (fun w : ℂ => w + 1) (-1 : ℂ) := by fun_prop
      simpa only [neg_add_cancel] using h.tendsto.mono_left nhdsWithin_le_nhds
    · apply eventually_of_mem self_mem_nhdsWithin
      intro w hw hzero
      exact hw (eq_neg_of_add_eq_zero_left hzero)
  have hgamma := Complex.tendsto_self_mul_Gamma_nhds_zero.comp hshift
  have hz : AnalyticAt ℂ riemannZeta (-1) :=
    analyticOn_riemannZeta _ (by simp; norm_num)
  have hGammaℝ : ContinuousAt Complex.Gammaℝ (-1) := by
    have hnonzero : (Complex.Gammaℝ (-1))⁻¹ ≠ 0 := by
      rw [gammaReal_neg_one]
      exact inv_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    have hdoubleInv : (fun s : ℂ => (Complex.Gammaℝ s)⁻¹)⁻¹ = Complex.Gammaℝ := by
      funext s
      exact inv_inv (Complex.Gammaℝ s)
    rw [← hdoubleInv]
    exact (Complex.differentiable_Gammaℝ_inv (-1)).continuousAt.inv₀ hnonzero
  have hfactor : ContinuousAt signedHeatFactor (-1) := by
    have hderiv := hz.deriv.continuousAt
    have hζ := hz.continuousAt
    unfold signedHeatFactor
    fun_prop
  have hp := hgamma.mul (hfactor.tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [Function.comp_apply, one_mul, mul_assoc, signedHeatFactor_at_casimir] using hp

#print axioms signedThetaHeat_residue_at_casimir

end

end RH01
