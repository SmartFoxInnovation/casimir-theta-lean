import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Shifting the inverse Mellin line

The rectangle identity and convergence of the truncated vertical integrals
give the contour displacement for a holomorphic remainder. The integrand
includes the Mellin power so the two horizontal edges use the same weight.
-/

namespace RH01

open Complex Filter MeasureTheory Set
open scoped Topology Interval

noncomputable section

private theorem horizontal_tendsto_zero {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (height : ℝ → ℝ) {bound : ℝ → ℝ} (hbound : Tendsto bound atTop (𝓝 0))
    (hedge : ∀ᶠ T in atTop, ∀ x ∈ Icc a b, ‖f ((x : ℂ) + height T * I)‖ ≤ bound T) :
    Tendsto (fun T : ℝ => ∫ x in a..b, f ((x : ℂ) + height T * I)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim := hbound.mul_const (b - a)
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using hlim)
  filter_upwards [hedge] with T hT
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := bound T) (f := fun x => f ((x : ℂ) + height T * I))
      (fun x hx => hT x (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hx))))

/-- The two symmetric vertical limits agree after the horizontal edges vanish. -/
theorem verticalLimit_eq_of_holomorphic_strip {f : ℂ → ℂ} {a b : ℝ} {A B : ℂ} (hab : a ≤ b)
    (hf : DifferentiableOn ℂ f {z : ℂ | z.re ∈ Icc a b})
    (ha : Tendsto (fun T : ℝ => ∫ y in -T..T, f ((a : ℂ) + y * I)) atTop (𝓝 A))
    (hb : Tendsto (fun T : ℝ => ∫ y in -T..T, f ((b : ℂ) + y * I)) atTop (𝓝 B))
    {bound : ℝ → ℝ} (hbound : Tendsto bound atTop (𝓝 0))
    (htop : ∀ᶠ T : ℝ in atTop, ∀ x ∈ Icc a b, ‖f ((x : ℂ) + T * I)‖ ≤ bound T)
    (hbottom : ∀ᶠ T in atTop, ∀ x ∈ Icc a b, ‖f ((x : ℂ) + (-T : ℝ) * I)‖ ≤ bound T) :
    B = A := by
  have htop' := horizontal_tendsto_zero hab id hbound htop
  have hbottom' := horizontal_tendsto_zero hab Neg.neg hbound hbottom
  have hlim := ((hbottom'.sub htop').add (hb.const_mul I)).sub (ha.const_mul I)
  have heq : ∀ᶠ T : ℝ in atTop,
      (∫ x in a..b, f ((x : ℂ) + (-T : ℝ) * I)) -
        (∫ x in a..b, f ((x : ℂ) + T * I)) +
        I * (∫ y in -T..T, f ((b : ℂ) + y * I)) -
        I * (∫ y in -T..T, f ((a : ℂ) + y * I)) = 0 := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    have hs : DifferentiableOn ℂ f
        (uIcc (⟨a, -T⟩ : ℂ).re (⟨b, T⟩ : ℂ).re ×ℂ
          uIcc (⟨a, -T⟩ : ℂ).im (⟨b, T⟩ : ℂ).im) := hf.mono (by
      intro z hz
      change z.re ∈ Icc a b
      simpa only [uIcc_of_le hab] using (mem_reProdIm.mp hz).1)
    simpa only [smul_eq_mul] using
      integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, -T⟩ ⟨b, T⟩ hs
  have hzero := tendsto_nhds_unique_of_eventuallyEq hlim tendsto_const_nhds heq
  simp only [sub_self, zero_add] at hzero
  exact mul_left_cancel₀ I_ne_zero (sub_eq_zero.mp hzero)

/-- The two full vertical integrals agree when both lines are integrable. -/
theorem verticalIntegral_eq_of_holomorphic_strip {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : DifferentiableOn ℂ f {z : ℂ | z.re ∈ Icc a b})
    (ha : VerticalIntegrable f a) (hb : VerticalIntegrable f b)
    {bound : ℝ → ℝ} (hbound : Tendsto bound atTop (𝓝 0))
    (htop : ∀ᶠ T : ℝ in atTop, ∀ x ∈ Icc a b, ‖f ((x : ℂ) + T * I)‖ ≤ bound T)
    (hbottom : ∀ᶠ T in atTop, ∀ x ∈ Icc a b, ‖f ((x : ℂ) + (-T : ℝ) * I)‖ ≤ bound T) :
    (∫ y : ℝ, f ((b : ℂ) + y * I)) = ∫ y : ℝ, f ((a : ℂ) + y * I) :=
  verticalLimit_eq_of_holomorphic_strip hab hf
    (intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id)
    (intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id)
    hbound htop hbottom

/-- Inverse Mellin displacement for the regularized signed integrand. -/
theorem mellinInv_eq_of_holomorphic_strip {F : ℂ → ℂ} {a b x : ℝ} (hab : a ≤ b)
    (hf : DifferentiableOn ℂ (fun z => (x : ℂ) ^ (-z) * F z) {z : ℂ | z.re ∈ Icc a b})
    (ha : VerticalIntegrable (fun z => (x : ℂ) ^ (-z) * F z) a)
    (hb : VerticalIntegrable (fun z => (x : ℂ) ^ (-z) * F z) b)
    {bound : ℝ → ℝ} (hbound : Tendsto bound atTop (𝓝 0))
    (hedge : ∀ᶠ T in atTop, ∀ u ∈ Icc a b, ∀ t : ℝ, |t| = T →
      ‖(x : ℂ) ^ (-((u : ℂ) + t * I)) * F ((u : ℂ) + t * I)‖ ≤ bound T) :
    mellinInv b F x = mellinInv a F x := by
  have ht : ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc a b,
      ‖(x : ℂ) ^ (-((u : ℂ) + T * I)) * F ((u : ℂ) + T * I)‖ ≤ bound T := by
    filter_upwards [hedge, eventually_ge_atTop (0 : ℝ)] with T hT h0 u hu
    exact hT u hu T (abs_of_nonneg h0)
  have hl : ∀ᶠ T in atTop, ∀ u ∈ Icc a b,
      ‖(x : ℂ) ^ (-((u : ℂ) + (-T : ℝ) * I)) * F ((u : ℂ) + (-T : ℝ) * I)‖ ≤ bound T := by
    filter_upwards [hedge, eventually_ge_atTop (0 : ℝ)] with T hT h0 u hu
    exact hT u hu (-T) (by rw [abs_neg, abs_of_nonneg h0])
  unfold mellinInv
  simp only [smul_eq_mul]
  rw [verticalIntegral_eq_of_holomorphic_strip hab hf ha hb hbound ht hl]

/-- The inverse line at real part σ costs exactly exp((σ-1/2)D) after
critical normalization. The constant is the vertical L1 norm. -/
theorem normalized_mellinInv_norm_le (F : ℂ → ℂ) (σ D : ℝ) :
    ‖(Real.exp (-D / 2) : ℂ) * mellinInv σ F (Real.exp (-D))‖ ≤
      Real.exp ((σ - 1 / 2) * D) *
        ((1 / (2 * Real.pi)) * ∫ y : ℝ, ‖F ((σ : ℂ) + y * I)‖) := by
  have hw (y : ℝ) :
      ‖(Real.exp (-D) : ℂ) ^ (-((σ : ℂ) + y * I))‖ = Real.exp (σ * D) := by
    have hre : (-((σ : ℂ) + y * I)).re = -σ := by simp [mul_re]
    rw [norm_cpow_eq_rpow_re_of_pos (Real.exp_pos _),
      Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, hre]
    congr 1
    ring
  have hnorm : 0 ≤ (1 / (2 * Real.pi) : ℝ) := by positivity
  rw [norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), mellinInv, norm_smul,
    Real.norm_of_nonneg hnorm]
  calc
    _ ≤ Real.exp (-D / 2) * (1 / (2 * Real.pi) *
        ∫ y : ℝ, ‖(Real.exp (-D) : ℂ) ^ (-((σ : ℂ) + y * I)) • F ((σ : ℂ) + y * I)‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hnorm) (Real.exp_nonneg _)
    _ = _ := by
      simp_rw [norm_smul, hw]
      rw [integral_const_mul]
      calc
        _ = (Real.exp (-D / 2) * Real.exp (σ * D)) *
            (1 / (2 * Real.pi) * ∫ y : ℝ, ‖F ((σ : ℂ) + y * I)‖) := by ring
        _ = _ := by
          rw [← Real.exp_add]
          congr 2
          ring

#print axioms mellinInv_eq_of_holomorphic_strip

end
end RH01
