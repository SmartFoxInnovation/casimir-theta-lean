import RH01.SignedRampContour
import RH01.RampConvolution
import RH01.ThetaProbe

/-! The actual theta certificate built from the signed Mellin contour. -/

namespace RH01

open Complex Filter MeasureTheory Set
open scoped Topology

noncomputable section

private def initialW (t : ℝ) : ℂ := (4 : ℂ) + t * I
private def initialS (t : ℝ) : ℂ := ((4 - 1 / 2 : ℝ) : ℂ) + t * I

private theorem initialW_re (t : ℝ) : (initialW t).re = 4 := by simp [initialW, mul_re]

private theorem initialS_add (t : ℝ) : initialS t + 1 / 2 = initialW t := by
  unfold initialS initialW
  push_cast
  ring

private theorem initialRamp_product (hM : RampMellinOn 4) (t : ℝ) :
    completedXi (initialS t + 1 / 2) * bilateralLaplace logRamp (initialS t) =
      signedRamp (initialW t) := by
  have hpos : 1 < (initialW t).re := by rw [initialW_re]; norm_num
  have h₀ : initialW t ≠ 0 := ne_zero_of_re_pos (zero_lt_one.trans hpos)
  have h₁ : initialW t ≠ 1 := fun h => by norm_num [h] at hpos
  have hm : (∫ y in Ioi (1 : ℝ), (primeRamp y : ℂ) * (y : ℂ) ^ (-initialW t - 1)) =
      rampTransform (initialW t) := by
    simpa [initialW] using hM t
  rw [bilateralLaplace_logRamp, initialS_add, hm,
    completedXi_eq_xi (zero_lt_one.trans hpos) h₁]
  exact (signedRamp_eq_xi_mul h₀ h₁ (riemannZeta_ne_zero_of_one_lt_re hpos)).symm

private theorem sample_conv_integrable {q : ℝ → ℂ} {C : ℝ} (hq : Continuous q)
    (hC : 0 ≤ C) (hdom : ∀ u, ‖q u‖ ≤ C * thetaWeight u) {Y : ℝ} (hY : 0 < Y) :
    Integrable (fun u => q u * (normalizedRamp (sample Y u) : ℂ)) := by
  let D := 5 / 4 * Real.log Y
  have he (u : ℝ) : sample Y u = Real.exp (D - u) := sample_eq_exp hY u
  simp_rw [he]
  have hm : Measurable (fun u : ℝ => (normalizedRamp (Real.exp (D - u)) : ℂ)) :=
    continuous_ofReal.measurable.comp (measurable_normalizedRamp.comp (by fun_prop))
  refine ((integrable_exp_mul_thetaWeight 3).const_mul (4 * C * Real.exp (3 * D))).mono'
    (hq.measurable.mul hm).aestronglyMeasurable (ae_of_all _ fun u => ?_)
  rw [norm_mul, norm_real, Real.norm_eq_abs]
  have h := normalizedRamp_exp_abs_le (D - u)
  have hx : Real.exp (3 * (D - u)) ≤ Real.exp (3 * D) * Real.exp (3 * |u|) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [neg_le_abs u])
  exact ((mul_le_mul (hdom u) h (abs_nonneg _) (mul_nonneg hC (thetaWeight_pos _).le)).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (by norm_num))
      (mul_nonneg hC (thetaWeight_pos _).le))).trans_eq (by ring)

private theorem normalized_residue_eq {ρ r : ℂ} {Y : ℝ} (hY : 0 < Y) :
    let D : ℝ := 5 / 4 * Real.log Y
    (Real.exp (-D / 2) : ℂ) * (r * (Real.exp (-D) : ℂ) ^ (-ρ)) =
      r * (Y ^ (5 * (ρ.re - 1 / 2) / 4) : ℝ) *
        Complex.exp ((ρ.im * D : ℝ) * I) := by
  dsimp only
  let D := 5 / 4 * Real.log Y
  change (Real.exp (-D / 2) : ℂ) * (r * (Real.exp (-D) : ℂ) ^ (-ρ)) = _
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos _).ne'), ← ofReal_log
    (Real.exp_nonneg _), Real.log_exp, Real.rpow_def_of_pos hY, ofReal_exp, ofReal_exp]
  have hr : Real.log Y * (5 * (ρ.re - 1 / 2) / 4) = (ρ.re - 1 / 2) * D := by dsimp [D]; ring
  rw [hr]
  calc
    _ = r * Complex.exp (((-D / 2 : ℝ) : ℂ) + ((-D : ℝ) : ℂ) * -ρ) := by
      rw [Complex.exp_add]; ring
    _ = _ := by
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      dsimp only [D]
      push_cast
      linear_combination (5 / 4 * (Real.log Y : ℂ)) * (re_add_im ρ).symm

private theorem eventually_normalized_error_le_one (C : ℝ) :
    ∀ᶠ Y : ℝ in atTop, Real.exp ((1 / 4 - 1 / 2) * (5 / 4 * Real.log Y)) * C ≤ 1 := by
  have hlog : Tendsto (fun Y : ℝ => (1 / 4 - 1 / 2) * (5 / 4 * Real.log Y)) atTop atBot := by
    have he : ∀ Y : ℝ, (1 / 4 - 1 / 2) * (5 / 4 * Real.log Y) = -(5 / 16) * Real.log Y := by
      intro Y
      ring
    simp_rw [he]
    exact Real.tendsto_log_atTop.const_mul_atTop_of_neg (by norm_num)
  have h : Tendsto (fun Y : ℝ => Real.exp ((1 / 4 - 1 / 2) * (5 / 4 * Real.log Y)) * C)
      atTop (𝓝 0) := by simpa using (Real.tendsto_exp_atBot.comp hlog).mul_const C
  exact (h.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))).mono fun _ hY => hY.le

/-- Build the actual signed detector at any right-half zeta zero. The only
input beyond the zero is the initial-line identity for the centered ramp. -/
theorem thetaCertificate_of_rampMellin (hM : RampMellinOn 4) {ρ : ℂ}
    (hre : 1 / 2 < ρ.re) (hρ : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    Nonempty (ThetaCertificate (ρ.re - 1 / 2)) := by
  have hp : 0 < ρ.re := (by norm_num : (0 : ℝ) < 1 / 2).trans hre
  have haρ : 1 / 4 < ρ.re := (by norm_num : (1 / 4 : ℝ) < 1 / 2).trans hre
  have hρb : ρ.re < 4 := (le_of_not_gt (fun h => riemannZeta_ne_zero_of_one_lt_re h hz)).trans_lt
    (by norm_num : (1 : ℝ) < 4)
  obtain ⟨k, g, hg, hgn, hfact⟩ := zeta_factor_at_zero hρ hz
  obtain ⟨r, G, hr, hG, hdec⟩ := signedRamp_divided_pole_of_factor hp hρ hg hgn hfact
  obtain ⟨q, C, hq, hC, hdom, hQ⟩ := exists_theta_probe hp hρ hg hfact
  let q₀ : ℝ → ℂ := fun u => (thetaWeight u : ℂ)
  have hq₀ : Continuous q₀ := continuous_ofReal.comp continuous_thetaWeight
  have hdom₀ (u : ℝ) : ‖q₀ u‖ ≤ 1 * thetaWeight u := by
    dsimp only [q₀]
    rw [norm_real, Real.norm_of_nonneg (thetaWeight_pos _).le, one_mul]
  let A := fun w : ℂ => signedRamp w / (w - ρ) ^ (k + 1)
  have hA : VerticalIntegrable A 4 := verticalIntegrable_dividedRamp _ (by norm_num) hρb.ne.symm
  have hP : ∀ t : ℝ, bilateralLaplace q (initialS t) * bilateralLaplace logRamp (initialS t) =
      A (initialW t) := by
    intro t
    have he : initialS t - (ρ - 1 / 2) = initialW t - ρ := by rw [← initialS_add]; ring
    have hn : (initialW t - ρ) ^ (k + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (fun h => by
      have hh := congrArg Complex.re h
      rw [initialW_re] at hh
      exact hρb.ne hh.symm))
    have h := hQ (initialS t)
    rw [he] at h
    apply (eq_div_iff hn).2
    rw [mul_right_comm, mul_comm _ ((initialW t - ρ) ^ (k + 1)), h]
    exact initialRamp_product hM t
  have h₀ (D : ℝ) := ramp_convolution_eq_normalized_mellinInv hq₀ zero_le_one hdom₀
    (verticalIntegrable_signedRamp (by norm_num)) (fun t => by
      change bilateralLaplace q₀ (initialS t) * bilateralLaplace logRamp (initialS t) =
        signedRamp (initialW t)
      rw [show bilateralLaplace q₀ (initialS t) = completedXi (initialS t + 1 / 2) from
        bilateralLaplace_thetaWeight_eq_completedXi _]
      exact initialRamp_product hM t) D
  have h₁ (D : ℝ) := ramp_convolution_eq_normalized_mellinInv hq hC hdom hA hP D
  let B₀ := (1 / (2 * Real.pi)) * ∫ y : ℝ, ‖signedRamp ((1 / 4 : ℝ) + y * I)‖
  let B₁ := (1 / (2 * Real.pi)) * ∫ y : ℝ, ‖A ((1 / 4 : ℝ) + y * I)‖
  have heft := (eventually_ge_atTop (1 : ℝ)).and (eventually_thetaWindowTail_le_one.and
    ((eventually_normalized_error_le_one B₀).and (eventually_normalized_error_le_one B₁)))
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp heft
  refine ⟨{
      weight := thetaWeight
      probe := q
      domination := C
      domination_nonneg := hC
      weight_nonneg := fun u => (thetaWeight_pos u).le
      weight_integrable := by simpa using integrable_exp_mul_thetaWeight 0
      probe_dom := hdom
      cutoff := Y₀
      signed_integrable := ?_
      probe_integrable := ?_
      signed_balance := ?_
      tail_bound := fun Y hY => (hY₀ Y ((le_max_right _ _).trans hY)).2.1
      residue := r
      residue_ne_zero := hr
      frequency := ρ.im
      residue_error := ?_ }⟩
  · intro Y hY
    have hi := sample_conv_integrable hq₀ zero_le_one hdom₀
      (zero_lt_one.trans_le ((le_max_left _ _).trans hY))
    have hi' := hi.re
    simpa [q₀, mul_re] using hi'
  · intro Y hY
    exact sample_conv_integrable hq hC hdom (zero_lt_one.trans_le ((le_max_left _ _).trans hY))
  · intro Y hY
    have h := hY₀ Y ((le_max_right _ _).trans hY)
    let D := 5 / 4 * Real.log Y
    have he : (∫ u, thetaWeight u * normalizedRamp (sample Y u) : ℝ) =
        (∫ u, q₀ u * logRamp (D - u)).re := by
      have hi := sample_conv_integrable hq₀ zero_le_one hdom₀ (zero_lt_one.trans_le h.1)
      have he' := integral_re hi
      simpa [q₀, logRamp, D, sample_eq_exp (zero_lt_one.trans_le h.1), mul_re] using he'
    rw [he, h₀ D, mellinInv_signedRamp_shift (show (0 : ℝ) < 1 / 4 by norm_num)
      (show (1 / 4 : ℝ) ≤ 4 by norm_num) (Real.exp_pos _)]
    exact (abs_re_le_norm _).trans ((normalized_mellinInv_norm_le signedRamp (1 / 4) D).trans h.2.2.1)
  · intro Y hY
    have h := hY₀ Y ((le_max_right _ _).trans hY)
    have hYpos := zero_lt_one.trans_le h.1
    let D := 5 / 4 * Real.log Y
    have he (u : ℝ) : (normalizedRamp (sample Y u) : ℂ) = logRamp (D - u) := by
      rw [sample_eq_exp hYpos]
      rfl
    have hs : mellinInv 4 A (Real.exp (-D)) - mellinInv (1 / 4) A (Real.exp (-D)) =
        r * (Real.exp (-D) : ℂ) ^ (-ρ) :=
      mellinInv_dividedRamp_shift_of_decomp (by norm_num) haρ hρb (Real.exp_pos _) hG hdec
    simp_rw [he]
    rw [h₁ D, ← normalized_residue_eq (ρ := ρ) (r := r) hYpos, ← mul_sub, ← hs, sub_sub_cancel]
    exact (normalized_mellinInv_norm_le A (1 / 4) D).trans h.2.2.2

/-- The source-assisted Casimir route with all theta estimates discharged. -/
theorem riemannHypothesis_of_window_and_rampMellin (hwin : PrimeWindowBound)
    (hM : RampMellinOn 4) : RiemannHypothesis :=
  riemannHypothesis_of_casimir_theta hwin fun _ hre hρ hz =>
    thetaCertificate_of_rampMellin hM hre hρ hz

#print axioms thetaCertificate_of_rampMellin
#print axioms riemannHypothesis_of_window_and_rampMellin

end
end RH01
