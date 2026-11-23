import RH01.ProbeDivision
import RH01.MellinShift
import Mathlib.Analysis.Fourier.Inversion

/-! Fourier inversion in the critically normalized Mellin coordinate. -/

namespace RH01

open Complex MeasureTheory
open scoped FourierTransform RealInnerProductSpace

/-- The signed convolution on the logarithmic axis is the critically
normalized inverse Mellin transform on the initial line. -/
theorem eq_normalized_mellinInv {p : ℝ} {g : ℝ → ℂ} {A : ℂ → ℂ}
    (hg : Continuous (fun u : ℝ => Complex.exp (-(p - 1 / 2 : ℝ) * (u : ℂ)) * g u))
    (hi : Integrable (fun u : ℝ => Complex.exp (-(p - 1 / 2 : ℝ) * (u : ℂ)) * g u))
    (hA : VerticalIntegrable A p)
    (hLaplace : ∀ t : ℝ, bilateralLaplace g ((p - 1 / 2 : ℝ) + t * I) = A ((p : ℂ) + t * I))
    (D : ℝ) : g D = (Real.exp (-D / 2) : ℂ) * mellinInv p A (Real.exp (-D)) := by
  let c : ℝ := 2 * Real.pi
  let f := fun u : ℝ => Complex.exp (-(p - 1 / 2 : ℝ) * (u : ℂ)) * g u
  have hc : 0 < c := by dsimp [c]; positivity
  have hF (y : ℝ) : 𝓕 f y = A ((p : ℂ) + (c * y : ℝ) * I) := by
    rw [← hLaplace (c * y), Real.fourier_eq', bilateralLaplace]
    apply integral_congr_ae (ae_of_all _ ?_)
    intro u
    dsimp only [f]
    simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    dsimp [c]
    push_cast
    ring
  have hFi : Integrable (𝓕 f) := by
    have hv : Integrable (fun t : ℝ => A ((p : ℂ) + t * I)) := hA
    rw [funext hF]
    exact hv.comp_mul_left' hc.ne'
  have hInv := congrFun (hg.fourierInv_fourier_eq hi hFi) D
  have hnorm : ∀ t : ℝ,
      (Real.exp (-D) : ℂ) ^ (-((p : ℂ) + t * I)) =
        Complex.exp ((p : ℂ) * D) * Complex.exp ((t : ℂ) * I * D) := by
    intro t
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos _).ne'), ← ofReal_log
      (Real.exp_nonneg _), Real.log_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  change 𝓕⁻ (𝓕 f) D = f D at hInv
  rw [Real.fourierInv_eq'] at hInv
  simp only [hF, smul_eq_mul] at hInv
  have hscale : (∫ y : ℝ, Complex.exp (↑(2 * Real.pi * ⟪y, D⟫) * I) *
         A ((p : ℂ) + (c * y : ℝ) * I)) =
      c⁻¹ • ∫ t : ℝ, Complex.exp ((t : ℂ) * I * D) * A ((p : ℂ) + t * I) := by
    rw [← abs_of_pos (inv_pos.mpr hc), ← Measure.integral_comp_mul_left _ c]
    apply integral_congr_ae (ae_of_all _ ?_)
    intro y
    congr 2
    simp [RCLike.inner_apply, c]
    ring
  rw [hscale] at hInv
  let J := ∫ t : ℝ, Complex.exp ((t : ℂ) * I * D) * A ((p : ℂ) + t * I)
  change c⁻¹ • J = f D at hInv
  unfold mellinInv
  have hterm (t : ℝ) : (Real.exp (-D) : ℂ) ^ (-((p : ℂ) + t * I)) *
      A ((p : ℂ) + t * I) = Complex.exp ((p : ℂ) * D) *
        (Complex.exp ((t : ℂ) * I * D) * A ((p : ℂ) + t * I)) := by
    rw [hnorm, mul_assoc]
  simp_rw [smul_eq_mul, hterm, integral_const_mul]
  change g D = (Real.exp (-D / 2) : ℂ) * ((1 / (2 * Real.pi)) • (Complex.exp ((p : ℂ) * D) * J))
  rw [show (1 / (2 * Real.pi) : ℝ) = c⁻¹ by simp [c]]
  have he : c⁻¹ • (Complex.exp ((p : ℂ) * D) * J) =
      Complex.exp ((p : ℂ) * D) * (c⁻¹ • J) := by
    simp only [Complex.real_smul]
    ring
  rw [he, hInv]
  dsimp only [f]
  rw [ofReal_exp, ← mul_assoc, ← Complex.exp_add, ← mul_assoc, ← Complex.exp_add]
  have hz : ((-D / 2 : ℝ) : ℂ) + (p : ℂ) * D + (-(p - 1 / 2 : ℝ) : ℂ) * D = 0 := by
    push_cast
    ring
  rw [hz, Complex.exp_zero, one_mul]

#print axioms eq_normalized_mellinInv

end RH01
