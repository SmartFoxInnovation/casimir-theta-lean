import RH01.LaplaceInversion
import RH01.ThetaTransform
import RH01.WindowTail

/-! The initial contour for the actual centered ramp and its theta probes. -/

namespace RH01

open Complex MeasureTheory Set
open scoped Convolution

noncomputable section

/-- The arithmetic Mellin identity required on the initial line. -/
def RampMellinOn (p : ℝ) : Prop :=
  ∀ t : ℝ, let w : ℂ := (p : ℂ) + t * I
    (∫ y in Ioi (1 : ℝ), (primeRamp y : ℂ) * (y : ℂ) ^ (-w - 1)) = rampTransform w

def logRamp (t : ℝ) : ℂ := (normalizedRamp (Real.exp t) : ℂ)

private theorem measurable_logRamp : Measurable logRamp :=
  continuous_ofReal.measurable.comp (measurable_normalizedRamp.comp Real.continuous_exp.measurable)

theorem bilateralLaplace_logRamp (s : ℂ) :
    bilateralLaplace logRamp s =
      ∫ y in Ioi (1 : ℝ), (primeRamp y : ℂ) * (y : ℂ) ^ (-(s + 1 / 2) - 1) := by
  let f := fun y : ℝ => (normalizedRamp y : ℂ)
  have he := mellin_log_change f (-2 * s)
  rw [show -2 * s / 2 = -s by ring] at he
  have hscale : (∫ u : ℝ, Complex.exp ((-2 * s) * u) * f (Real.exp (2 * u))) =
      (2 : ℝ)⁻¹ • bilateralLaplace logRamp s := by
    unfold bilateralLaplace
    rw [← abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹),
      ← Measure.integral_comp_mul_left _ (2 : ℝ)]
    apply integral_congr_ae (ae_of_all _ ?_)
    intro u
    dsimp only [f, logRamp]
    rw [ofReal_mul]
    congr 2
    push_cast
    ring
  have hf : bilateralLaplace logRamp s = mellin f (-s) := by
    rw [hscale, Complex.real_smul] at he
    norm_num at he
    linear_combination -2 * he
  rw [hf, mellin]
  let g := fun y : ℝ => (primeRamp y : ℂ) * (y : ℂ) ^ (-(s + 1 / 2) - 1)
  have hpoint (y : ℝ) (hy : y ∈ Ioi (0 : ℝ)) :
      (y : ℂ) ^ (-s - 1) • f y = (Ici (1 : ℝ)).indicator g y := by
    by_cases hy₁ : 1 ≤ y
    · rw [indicator_of_mem (show y ∈ Ici 1 from hy₁)]
      dsimp [f, g]
      rw [normalizedRamp, if_pos hy₁, ofReal_div, ofReal_cpow hy.le, div_eq_mul_inv]
      rw [← cpow_neg, mul_comm ((y : ℂ) ^ (-s - 1)), mul_assoc, ← cpow_add _ _
        (ofReal_ne_zero.mpr hy.ne')]
      congr 2
      push_cast
      ring
    · rw [indicator_of_notMem (show y ∉ Ici 1 from hy₁)]
      simp [f, normalizedRamp, hy₁]
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict_of_subset (show Ici (1 : ℝ) ⊆ Ioi 0 from
      fun _ hy => mem_Ioi.mpr (zero_lt_one.trans_le (mem_Ici.mp hy))), integral_Ici_eq_integral_Ioi]

private theorem integrable_initial_tilt :
    Integrable (fun u : ℝ => Complex.exp (-(4 - 1 / 2 : ℝ) * (u : ℂ)) * logRamp u) := by
  have hi := (integrableOn_exp_mul_Ioi (show -(1 / 2 : ℝ) < 0 by norm_num)
    (0 : ℝ)).const_mul 4
  have hi' : Integrable ((Ioi (0 : ℝ)).indicator (fun u : ℝ => 4 * Real.exp (-(1 / 2 : ℝ) * u))) := by
    rw [integrable_indicator_iff measurableSet_Ioi, IntegrableOn]
    exact hi
  apply hi'.mono'
  · exact ((by fun_prop : Continuous (fun u : ℝ => Complex.exp (-(4 - 1 / 2 : ℝ) *
      (u : ℂ)))).measurable.mul measurable_logRamp).aestronglyMeasurable
  · filter_upwards [(volume : Measure ℝ).ae_ne 0] with u hne
    by_cases hu : u ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hu, norm_mul, Complex.norm_exp]
      simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, neg_re]
      have hn : ‖logRamp u‖ ≤ 4 * Real.exp (3 * u) := by
        rw [logRamp, norm_real, Real.norm_eq_abs]
        exact normalizedRamp_exp_abs_le u
      refine (mul_le_mul_of_nonneg_left hn (Real.exp_nonneg _)).trans_eq ?_
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    · have hu₀ : u < 0 := lt_of_le_of_ne (le_of_not_gt hu) hne
      have he : ¬1 ≤ Real.exp u := not_le.mpr (Real.exp_lt_one_iff.mpr hu₀)
      simp [logRamp, normalizedRamp, he, indicator_of_notMem hu]

private theorem bounded_initial_thetaTilt {q : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hdom : ∀ u, ‖q u‖ ≤ C * thetaWeight u) :
    BddAbove (range fun u : ℝ => ‖Complex.exp (-(4 - 1 / 2 : ℝ) * (u : ℂ)) * q u‖) := by
  obtain ⟨B, hB⟩ := thetaTilt_bounded 4
  have h (u : ℝ) : ‖Complex.exp (-(4 - 1 / 2 : ℝ) * (u : ℂ))‖ ≤ Real.exp (4 * |u|) := by
    rw [Complex.norm_exp, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, neg_re, ofReal_re]
    apply Real.exp_le_exp.mpr
    linarith [abs_nonneg u, neg_le_abs u]
  refine ⟨C * B, fun _ hy => ?_⟩
  obtain ⟨u, rfl⟩ := hy
  change ‖Complex.exp (-(4 - 1 / 2 : ℝ) * (u : ℂ)) * q u‖ ≤ C * B
  rw [norm_mul]
  exact (mul_le_mul (h u) (hdom u) (norm_nonneg _) (Real.exp_nonneg _)).trans
    (by rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (hB u) hC)

/-- Initial-line inversion for the full convolution and any dominated probe
with its exact product transform identity. -/
theorem ramp_convolution_eq_normalized_mellinInv {q : ℝ → ℂ} {A : ℂ → ℂ} {C : ℝ}
    (hq : Continuous q) (hC : 0 ≤ C) (hdom : ∀ u, ‖q u‖ ≤ C * thetaWeight u)
    (hA : VerticalIntegrable A 4)
    (hprod : ∀ t : ℝ, bilateralLaplace q ((4 - 1 / 2 : ℝ) + t * I) *
      bilateralLaplace logRamp ((4 - 1 / 2 : ℝ) + t * I) = A ((4 : ℂ) + t * I))
    (D : ℝ) :
    (∫ u : ℝ, q u * logRamp (D - u)) = (Real.exp (-D / 2) : ℂ) * mellinInv 4 A (Real.exp (-D)) := by
  let p : ℂ := ((4 - 1 / 2 : ℝ) : ℂ)
  let Q := fun u : ℝ => Complex.exp (-p * u) * q u
  let F := fun u : ℝ => Complex.exp (-p * u) * logRamp u
  let L := ContinuousLinearMap.mul ℂ ℂ
  let W := fun D : ℝ => ∫ u : ℝ, q u * logRamp (D - u)
  have hp : ∀ x : ℝ, Complex.exp (-p * x) * W x = (Q ⋆[L] F) x := by
    intro x
    rw [← integral_const_mul, convolution_def]
    apply integral_congr_ae (ae_of_all _ ?_)
    intro u
    change Complex.exp (-p * x) * (q u * logRamp (x - u)) =
      (Complex.exp (-p * u) * q u) * (Complex.exp (-p * (x - u : ℝ)) * logRamp (x - u))
    rw [show -p * (x : ℂ) = -p * (u : ℂ) + -p * (x - u : ℝ) by push_cast; ring,
      Complex.exp_add]
    ring
  have hQ : Integrable Q := thetaTilt_integrable_of_bound hq.measurable hC hdom (-p)
  have hF : Integrable F := integrable_initial_tilt
  have hQc : Continuous Q := by dsimp [Q]; fun_prop
  have hc : Continuous (fun x : ℝ => Complex.exp (-p * x) * W x) := by
    rw [funext hp]
    exact (bounded_initial_thetaTilt hC hdom).continuous_convolution_left_of_integrable L hQc hF
  have hi : Integrable (fun x : ℝ => Complex.exp (-p * x) * W x) := by
    rw [funext hp]
    exact hQ.integrable_convolution L hF
  refine eq_normalized_mellinInv (p := 4) (g := W)
    hc hi hA (fun t => ?_) D
  let s := ((4 - 1 / 2 : ℝ) : ℂ) + t * I
  have hre : (-s).re = -(4 - 1 / 2 : ℝ) := by simp [s, mul_re]
  have hFs : Integrable (fun u : ℝ => Complex.exp (-s * u) * logRamp u) := by
    apply integrable_initial_tilt.norm.mono'
    · exact ((by fun_prop : Continuous (fun u : ℝ => Complex.exp (-s * u))).measurable.mul
        measurable_logRamp).aestronglyMeasurable
    · filter_upwards with u
      simp only [norm_mul, Complex.norm_exp, mul_re, ofReal_re, ofReal_im, mul_zero,
        sub_zero, hre, neg_re]
      exact le_rfl
  exact (bilateralLaplace_convolution
    (thetaTilt_integrable_of_bound hq.measurable hC hdom (-s)) hFs).trans (hprod t)

#print axioms bilateralLaplace_logRamp
#print axioms ramp_convolution_eq_normalized_mellinInv

end
end RH01
