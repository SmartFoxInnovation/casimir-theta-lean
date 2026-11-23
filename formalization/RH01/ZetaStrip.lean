import RH01.SignedTransforms
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.MeasureTheory.Function.Floor

/-! Fixed-strip bounds from the fractional-part formula for regularized zeta. -/

namespace RH01

open Complex Set MeasureTheory Asymptotics Filter
open scoped Topology

noncomputable section

private def floorError : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator (fun t => ((⌊t⌋₊ : ℝ) - t : ℝ))

private theorem measurable_floorError : Measurable floorError := by
  unfold floorError
  apply Measurable.indicator _ measurableSet_Ioi
  exact continuous_ofReal.measurable.comp
    ((measurable_of_countable (f := fun n : ℕ => (n : ℝ))).comp
      (Nat.measurable_floor (R := ℝ)) |>.sub measurable_id)

private theorem norm_floorError_le (x : ℝ) : ‖floorError x‖ ≤ 1 := by
  by_cases hx : x ∈ Ioi (1 : ℝ)
  · rw [floorError, indicator_of_mem hx, norm_real, Real.norm_eq_abs]
    exact Nat.abs_floor_sub_le (zero_le_one.trans (mem_Ioi.mp hx).le)
  · simp [floorError, indicator_of_notMem hx]

private def fractionalMellin (z : ℂ) := mellin floorError (-z)

private theorem fractionalMellin_properties {z : ℂ} (hz : 0 < z.re) :
    MellinConvergent floorError (-z) ∧
      MellinConvergent (fun t => Real.log t • floorError t) (-z) ∧
      HasDerivAt fractionalMellin (-(mellin (fun t => Real.log t • floorError t) (-z))) z := by
  have hf : LocallyIntegrableOn floorError (Ioi (0 : ℝ)) :=
    (memLp_top_of_bound measurable_floorError.aestronglyMeasurable 1
      (Eventually.of_forall norm_floorError_le)).locallyIntegrable le_top |>.locallyIntegrableOn _
  have htop : floorError =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) :=
    isBigO_of_le atTop (fun t => by simpa using norm_floorError_le t)
  have hbot : floorError =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(-z.re - 1))) := by
    refine IsBigO.of_bound 0 ?_
    have h : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
      nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)
    filter_upwards [h] with t ht
    simp [floorError, not_lt.mpr ht.le]
  have hz₀ : (-z).re < 0 := by simpa using hz
  have hz₁ : -z.re - 1 < (-z).re := by simp
  obtain ⟨hi, hd⟩ := mellin_hasDerivAt_of_isBigO_rpow hf htop hz₀ hbot hz₁
  refine ⟨mellinConvergent_of_isBigO_rpow hf htop hz₀ hbot hz₁, hi, ?_⟩
  change HasDerivAt (mellin floorError ∘ Neg.neg) _ z
  simpa only [mul_neg, mul_one] using hd.comp z (hasDerivAt_id z).neg

private theorem fractionalMellin_eq_integral (z : ℂ) :
    fractionalMellin z = ∫ t in Ioi (1 : ℝ), (((⌊t⌋₊ : ℝ) - t : ℝ) : ℂ) *
      (t : ℂ) ^ (-z - 1) := by
  rw [fractionalMellin, mellin]
  simp only [floorError, smul_eq_mul, ← indicator_mul_right (Ioi (1 : ℝ))
    (fun t : ℝ => (t : ℂ) ^ (-z - 1)), integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num)), mul_comm]

private theorem riemannZeta₀_eq_fractional {z : ℂ} (hz : 0 < z.re) :
    riemannZeta₀ z = 1 + z * fractionalMellin z := by
  let U : Set ℂ := {z | 0 < z.re}
  let f := fun z : ℂ => 1 + z * fractionalMellin z
  have hc : IsPreconnected U :=
    (convex_halfSpace_gt (𝕜 := ℝ) (f := Complex.re) Complex.reLm.isLinear (0 : ℝ)).isPreconnected
  have hA : AnalyticOnNhd ℂ f U := by
    apply DifferentiableOn.analyticOnNhd
    · intro w hw
      exact ((differentiableAt_id.mul
        (fractionalMellin_properties hw).2.2.differentiableAt).const_add _).differentiableWithinAt
    · exact isOpen_lt continuous_const continuous_re
  have hB : AnalyticOnNhd ℂ riemannZeta₀ U :=
    fun w _ => differentiable_riemannZeta₀.analyticAt w
  have hre : ∀ᶠ w : ℂ in 𝓝 (2 : ℂ), 1 < w.re :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
  have heq : f =ᶠ[𝓝 (2 : ℂ)] riemannZeta₀ := by
    filter_upwards [hre] with w hw
    have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (1 : ℂ)) =O[atTop]
        fun n => (n : ℝ) ^ (1 : ℝ) := isBigO_of_le atTop (fun n => by simp)
    have hsum := LSeries_eq_mul_integral (1 : ℕ → ℂ) zero_le_one hw
      (LSeriesSummable_one_iff.mpr hw) hO
    have hpow : -(w + 1) = -w - 1 := by ring
    have he : riemannZeta w = w * ∫ t in Ioi (1 : ℝ), (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-w - 1) := by
      simpa only [LSeries_one_eq_riemannZeta hw, Pi.one_apply, Finset.sum_const,
        Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one, hpow] using hsum
    have hn : w ≠ 1 := fun hh => by norm_num [hh] at hw
    have h₁ : (-w - 1).re < -1 := by simp; linarith
    have h₂ : (-w).re < -1 := by simp; linarith
    have hi : IntegrableOn (fun t : ℝ => (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-w - 1)) (Ioi 1) := by
      have hI := (integrableOn_Ioi_cpow_of_lt h₂ zero_lt_one).norm
      refine hI.mono' ?_ ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_)
      · apply AEStronglyMeasurable.mul
        · exact ((measurable_of_countable (f := fun n : ℕ => (n : ℂ))).comp
            (Nat.measurable_floor (R := ℝ))).aestronglyMeasurable
        · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
          exact continuousOn_of_forall_continuousAt fun t ht =>
            continuousAt_ofReal_cpow_const _ _ (Or.inr (zero_lt_one.trans ht).ne')
      · have ht0 : 0 < t := zero_lt_one.trans ht
        simp only [norm_mul, Complex.norm_natCast, norm_cpow_eq_rpow_re_of_pos ht0, neg_re,
          sub_re, one_re]
        calc
          _ ≤ t * t ^ (-w.re - 1) := mul_le_mul_of_nonneg_right (Nat.floor_le ht0.le)
            (Real.rpow_nonneg ht0.le _)
          _ = t ^ (-w.re) := by
            calc
              _ = t ^ (1 : ℝ) * t ^ (-w.re - 1) := by rw [Real.rpow_one]
              _ = _ := by rw [← Real.rpow_add ht0]; congr 1; ring
    have hpoint (t : ℝ) (ht : t ∈ Ioi (1 : ℝ)) :
        (t : ℂ) * (t : ℂ) ^ (-w - 1) = (t : ℂ) ^ (-w) := by
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
      calc
        _ = (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-w - 1) := by rw [cpow_one]
        _ = _ := by rw [← cpow_add _ _ ht0]; congr 1; ring
    have ht : IntegrableOn (fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-w - 1)) (Ioi 1) := by
      refine (integrableOn_Ioi_cpow_of_lt h₂ zero_lt_one).congr_fun
        (fun t ht => (hpoint t ht).symm) measurableSet_Ioi
    have hti : (∫ t in Ioi (1 : ℝ), (t : ℂ) * (t : ℂ) ^ (-w - 1)) = 1 / (w - 1) := by
      rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_Ioi_cpow_of_lt h₂ zero_lt_one,
        ofReal_one, one_cpow]
      rw [show -w + 1 = -(w - 1) by ring, div_neg, neg_div, neg_neg]
    have hsub : fractionalMellin w =
        (∫ t in Ioi (1 : ℝ), (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-w - 1)) - 1 / (w - 1) := by
      rw [fractionalMellin_eq_integral, ← hti, ← integral_sub hi ht]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      push_cast
      ring
    rw [riemannZeta_eq_inv_sub_add hn] at he
    dsimp only [f]
    rw [hsub]
    field_simp [sub_ne_zero.mpr hn] at he ⊢
    linear_combination -he
  exact (hA.eqOn_of_preconnected_of_eventuallyEq hB hc (by norm_num [U]) heq hz).symm

private theorem norm_mellin_neg_le {a : ℝ} {z : ℂ} (haz : a ≤ z.re)
    {f : ℝ → ℂ} (hf : MellinConvergent f (-(a : ℂ)))
    (hzero : ∀ t : ℝ, t ≤ 1 → f t = 0) :
    ‖mellin f (-z)‖ ≤
      ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (-(a : ℂ) - 1) • f t‖ := by
  unfold mellin
  unfold MellinConvergent IntegrableOn at hf
  refine norm_integral_le_of_norm_le hf.norm
    ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_)
  by_cases h : t ≤ 1
  · simp [hzero t h]
  · simp only [norm_smul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, neg_re, one_re, ofReal_re]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) (by linarith))
      (norm_nonneg _)

/-- On each closed sub-half-plane of positive real part, the two regularized
zeta factors of the signed ramp grow at most linearly in the complex argument. -/
theorem regularZeta_linear_bound {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re →
      ‖riemannZeta₀ z‖ ≤ C * (1 + ‖z‖) ∧
      ‖deriv riemannZeta₀ z‖ ≤ C * (1 + ‖z‖) := by
  let K := ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (-(a : ℂ) - 1) • floorError t‖
  let L := ∫ t in Ioi (0 : ℝ),
    ‖(t : ℂ) ^ (-(a : ℂ) - 1) • (Real.log t • floorError t)‖
  have hK : 0 ≤ K := integral_nonneg fun _ => norm_nonneg _
  have hL : 0 ≤ L := integral_nonneg fun _ => norm_nonneg _
  have h0 (t : ℝ) (ht : t ≤ 1) : floorError t = 0 := by
    exact indicator_of_notMem (not_lt.mpr ht) _
  obtain ⟨hi, hi', _⟩ := fractionalMellin_properties (z := a) (by simpa using ha)
  refine ⟨1 + K + L, by positivity, fun z hz => ?_⟩
  have hF : ‖fractionalMellin z‖ ≤ K := norm_mellin_neg_le hz hi h0
  have hF' : ‖mellin (fun t => Real.log t • floorError t) (-z)‖ ≤ L :=
    norm_mellin_neg_le hz hi' (fun t ht => by simp [h0 t ht])
  have heq : riemannZeta₀ =ᶠ[𝓝 z] (fun w => 1 + w * fractionalMellin w) := by
    have hz' : {w : ℂ | 0 < w.re} ∈ 𝓝 z :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (ha.trans_le hz)
    filter_upwards [hz'] with w hw using riemannZeta₀_eq_fractional hw
  have hd := ((hasDerivAt_id z).fun_mul (fractionalMellin_properties (ha.trans_le hz)).2.2).const_add 1
  have hd' := (hd.congr_of_eventuallyEq heq).deriv
  constructor
  · rw [riemannZeta₀_eq_fractional (ha.trans_le hz)]
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul]
    nlinarith only [mul_le_mul_of_nonneg_left hF (norm_nonneg z),
      mul_nonneg hK (norm_nonneg z), mul_nonneg hL (norm_nonneg z), hK, hL, norm_nonneg z]
  · rw [hd']
    simp only [id_eq, one_mul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_neg]
    nlinarith only [mul_le_mul_of_nonneg_left hF' (norm_nonneg z), hF,
      mul_nonneg hK (norm_nonneg z), hK, hL, norm_nonneg z]

#print axioms regularZeta_linear_bound

end
end RH01
