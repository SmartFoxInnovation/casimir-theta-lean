import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Polynomial decay of the real gamma factor from Euler's integral and recurrence. -/

namespace RH01

open Complex Set MeasureTheory

private theorem norm_Gamma_le {a b : ℝ} {z : ℂ}
    (ha : 0 < a) (haz : a ≤ z.re) (hzb : z.re ≤ b) :
    ‖Gamma z‖ ≤ Real.Gamma a + Real.Gamma b := by
  have hz : 0 < z.re := ha.trans_le haz
  have hb : 0 < b := hz.trans_le hzb
  rw [Complex.Gamma_eq_integral hz, GammaIntegral, Real.Gamma_eq_integral ha,
    Real.Gamma_eq_integral hb, ← integral_add (Real.GammaIntegral_convergent ha)
      (Real.GammaIntegral_convergent hb)]
  refine (norm_integral_le_integral_norm _).trans
    (setIntegral_mono_on (GammaIntegral_convergent hz).norm
      ((Real.GammaIntegral_convergent ha).add (Real.GammaIntegral_convergent hb))
      measurableSet_Ioi fun t ht => ?_)
  change 0 < t at ht
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _), norm_cpow_eq_rpow_re_of_pos ht,
    sub_re, one_re, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  rcases le_or_gt t 1 with h | h
  · exact (Real.rpow_le_rpow_of_exponent_ge ht h (sub_le_sub_right haz _)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg ht.le _))
  · exact (Real.rpow_le_rpow_of_exponent_le h.le (sub_le_sub_right hzb _)).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg ht.le _))

private theorem pow_im_mul_norm_Gamma_le (k : ℕ) {z : ℂ} (hz : 0 < z.re) :
    |z.im| ^ k * ‖Gamma z‖ ≤ ‖Gamma (z + k)‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : 0 < (z + (k : ℂ)).re := by simp; positivity
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ (ne_zero_of_re_pos hpos),
      norm_mul, pow_succ, mul_right_comm _ |z.im| _, mul_comm (|z.im| ^ k * ‖Gamma z‖)]
    refine mul_le_mul ?_ ih (by positivity) (norm_nonneg _)
    simpa using abs_im_le_norm (z + (k : ℂ))

/-- A fixed positive-real strip has a uniform gamma bound after any power of
the imaginary coordinate. -/
theorem pow_im_mul_norm_GammaReal_le (k : ℕ) {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      |z.im| ^ k * ‖Gammaℝ z‖ ≤ C := by
  let K := Real.Gamma (a / 2 + k) + Real.Gamma (b / 2 + k)
  refine ⟨2 ^ k * Real.pi ^ (-a / 2) * |K|, by positivity, fun z haz hzb => ?_⟩
  have h₁ : 0 < (z / 2).re := by rw [div_ofNat_re]; linarith
  have h₂ : a / 2 + (k : ℝ) ≤ (z / 2 + (k : ℂ)).re := by
    simp [div_ofNat_re]
    linarith
  have h₃ : (z / 2 + (k : ℂ)).re ≤ b / 2 + (k : ℝ) := by
    simp [div_ofNat_re]
    linarith
  have h₄ : |(z / 2).im| ^ k * ‖Gamma (z / 2)‖ ≤ |K| :=
    (pow_im_mul_norm_Gamma_le k h₁).trans
      ((norm_Gamma_le (by positivity) h₂ h₃).trans (le_abs_self K))
  rw [Gammaℝ_def, norm_mul, norm_cpow_eq_rpow_re_of_pos Real.pi_pos, div_ofNat_re, neg_re]
  have hp := Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three] : 1 ≤ Real.pi)
    (show -z.re / 2 ≤ -a / 2 by linarith)
  have heq : |z.im| ^ k = 2 ^ k * |(z / 2).im| ^ k := by
    rw [div_ofNat_im, abs_div, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)), ← mul_pow]
    congr 1
    ring
  rw [heq]
  calc
    _ = 2 ^ k * (Real.pi ^ (-z.re / 2) * (|(z / 2).im| ^ k * ‖Gamma (z / 2)‖)) := by ring
    _ ≤ 2 ^ k * (Real.pi ^ (-a / 2) * |K|) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hp h₄ (by positivity) (by positivity)) (by positivity)
    _ = _ := by ring

#print axioms pow_im_mul_norm_GammaReal_le

end RH01
