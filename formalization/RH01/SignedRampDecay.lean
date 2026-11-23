import RH01.GammaDecay
import RH01.ZetaStrip

/-! Uniform vertical decay after the full signed ramp cancellation. -/

namespace RH01

open Complex Set

noncomputable section

/-- The actual signed ramp decays faster than any fixed inverse power of
height on a closed strip in the positive half-plane. -/
theorem signedRamp_rapidDecay (k : ℕ) {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      |z.im| ^ k * ‖signedRamp z‖ ≤ C := by
  obtain ⟨C₀, hC₀, hζ⟩ := regularZeta_linear_bound ha
  obtain ⟨K, hK, hΓ⟩ := pow_im_mul_norm_GammaReal_le (k + 2) (b := b) ha
  let γ := (Real.eulerMascheroniConstant : ℂ)
  let C := 1 + C₀ + ‖γ‖
  refine ⟨6 * C ^ 2 * (b + 2) ^ 2 * K, by positivity, fun z haz hzb ht => ?_⟩
  let U := 1 + ‖z‖
  have hC : 1 ≤ C := by dsimp [C]; linarith [norm_nonneg γ]
  have hU : 1 ≤ U := by dsimp [U]; linarith [norm_nonneg z]
  have hCU : 1 ≤ C * U := by simpa using mul_le_mul hC hU zero_le_one (by linarith)
  have hC₁ : C₀ ≤ C := by dsimp [C]; linarith [norm_nonneg γ]
  have hζ₀ : ‖riemannZeta₀ z‖ ≤ C * U :=
    (hζ z haz).1.trans (mul_le_mul_of_nonneg_right hC₁ (by linarith))
  have hζ₁ : ‖deriv riemannZeta₀ z‖ ≤ C * U :=
    (hζ z haz).2.trans (mul_le_mul_of_nonneg_right hC₁ (by linarith))
  have hγ : ‖1 + γ‖ ≤ C := (norm_add_le _ _).trans (by simp [C]; linarith)
  have hγ₀ : ‖γ‖ ≤ C * U := by
    exact (show ‖γ‖ ≤ C by dsimp [C]; linarith).trans (le_mul_of_one_le_right (by linarith) hU)
  have hz : ‖z‖ ≤ U := by dsimp [U]; linarith
  have hdist : 1 ≤ ‖z - 1‖ := ht.trans (by simpa using abs_im_le_norm (z - 1))
  have hz₁ : z ≠ 1 := by intro h; norm_num [h] at hdist
  have hds : ‖dslope riemannZeta₀ 1 z‖ ≤ 2 * (C * U) := by
    rw [dslope_of_ne _ hz₁, slope_def_module, smul_eq_mul, norm_mul, norm_inv,
      riemannZeta₀_one]
    have hinv : ‖z - 1‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hdist
    exact (mul_le_mul_of_nonneg_right hinv (norm_nonneg _)).trans (by
      rw [one_mul]
      exact (norm_sub_le _ _).trans (by dsimp only [γ] at hγ₀; linarith))
  have hprod : ‖z * riemannZeta₀ z * (1 + γ)‖ ≤ (C * U) ^ 2 := by
    simp only [norm_mul]
    calc
      _ ≤ U * (C * U) * C := by gcongr
      _ = _ := by ring
  have hsmall : C * U ≤ (C * U) ^ 2 := by nlinarith only [hCU, sq_nonneg (C * U - 1)]
  have hsigned : ‖signedRamp z‖ ≤ ‖Gammaℝ z‖ * (6 * (C * U) ^ 2) := by
    unfold signedRamp
    rw [norm_mul, norm_div, norm_ofNat]
    have hζneg : ‖-deriv riemannZeta₀ z‖ ≤ C * U := by rwa [norm_neg]
    have hbr := (norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add hζneg hprod))
        ((norm_sub_le _ _).trans (add_le_add hγ hζ₀)))) hds)
    have hγ' : C ≤ C * U := le_mul_of_one_le_right (by linarith) hU
    dsimp only [γ] at hbr
    calc
      _ ≤ ‖Gammaℝ z‖ / 2 * (C * U + (C * U) ^ 2 + (C + C * U) + 2 * (C * U)) :=
        mul_le_mul_of_nonneg_left hbr (by positivity)
      _ ≤ ‖Gammaℝ z‖ * (6 * (C * U) ^ 2) := by
        rw [div_mul_eq_mul_div, mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        linarith
  have hb : 0 ≤ b := ha.le.trans (haz.trans hzb)
  have hUb : U ≤ (b + 2) * |z.im| := by
    have hn := norm_le_abs_re_add_abs_im z
    rw [abs_of_nonneg (ha.le.trans haz)] at hn
    dsimp only [U]
    nlinarith only [hn, hzb, ht, mul_nonneg (by linarith : 0 ≤ b + 1) (sub_nonneg.mpr ht)]
  have hp : (C * U) ^ 2 ≤ C ^ 2 * (b + 2) ^ 2 * |z.im| ^ 2 := by
    calc
      _ ≤ (C * ((b + 2) * |z.im|)) ^ 2 := by gcongr
      _ = _ := by ring
  calc
    _ ≤ |z.im| ^ k * (‖Gammaℝ z‖ * (6 * (C * U) ^ 2)) :=
      mul_le_mul_of_nonneg_left hsigned (by positivity)
    _ ≤ |z.im| ^ k * (‖Gammaℝ z‖ * (6 * (C ^ 2 * (b + 2) ^ 2 * |z.im| ^ 2))) := by gcongr
    _ = 6 * C ^ 2 * (b + 2) ^ 2 * (|z.im| ^ (k + 2) * ‖Gammaℝ z‖) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hΓ z haz hzb) (by positivity)

#print axioms signedRamp_rapidDecay

end
end RH01
