import RH01.ContourResidue
import RH01.ProbeResidue
import RH01.SignedRampDecay

/-! Applying the inverse Mellin displacements to the actual signed ramp. -/

namespace RH01

open Complex Filter MeasureTheory Set
open scoped Topology

noncomputable section

private def verticalPoint (u t : ℝ) : ℂ := (u : ℂ) + t * I

@[simp] private theorem verticalPoint_re (u t : ℝ) : (verticalPoint u t).re = u := by
  simp [verticalPoint, mul_re]

@[simp] private theorem verticalPoint_im (u t : ℝ) : (verticalPoint u t).im = t := by
  simp [verticalPoint, mul_im]

private theorem verticalIntegrable_of_tail {F : ℂ → ℂ} {p C R : ℝ} (hR : 1 ≤ R)
    (hcont : Continuous (fun y => F (verticalPoint p y)))
    (hdecay : ∀ t : ℝ, R ≤ |t| → |t| ^ 2 * ‖F (verticalPoint p t)‖ ≤ C) :
    VerticalIntegrable F p := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-R) R) hcont.continuousOn
  let K := max (2 * C) ((1 + R ^ 2) * |B|)
  have hK (t : ℝ) : (1 + t ^ 2) * ‖F (verticalPoint p t)‖ ≤ K := by
    by_cases ht : R ≤ |t|
    · have hs : 1 ≤ t ^ 2 := by
        rw [← sq_abs]
        nlinarith [hR.trans ht]
      have hd := hdecay t ht
      rw [sq_abs] at hd
      apply le_max_of_le_left
      nlinarith only [hd, mul_nonneg (sub_nonneg.mpr hs) (norm_nonneg (F (verticalPoint p t)))]
    · apply le_max_of_le_right
      have ht' : |t| ≤ R := le_of_not_ge ht
      have hb := (hB t (abs_le.mp ht')).trans (le_abs_self B)
      have hsq : t ^ 2 ≤ R ^ 2 := by
        rw [← sq_abs t]
        gcongr
      gcongr
  exact (integrable_inv_one_add_sq.const_mul K).mono'
    hcont.aestronglyMeasurable (ae_of_all _ fun t => by
      change _ ≤ K * (1 + t ^ 2)⁻¹
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
      exact hK t)

private theorem norm_mellin_weight_le {x a b : ℝ} (hx : 0 < x) (ha : 0 ≤ a)
    {z : ℂ} (haz : a ≤ z.re) (hzb : z.re ≤ b) :
    ‖(x : ℂ) ^ (-z)‖ ≤ Real.exp (b * |Real.log x|) := by
  rw [norm_cpow_eq_rpow_re_of_pos hx, Real.rpow_def_of_pos hx, neg_re]
  apply Real.exp_le_exp.mpr
  have hza := ha.trans haz
  calc
    _ ≤ |Real.log x * -z.re| := le_abs_self _
    _ = z.re * |Real.log x| := by rw [abs_mul, abs_neg, abs_of_nonneg hza, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right hzb (abs_nonneg _)

private theorem verticalIntegrable_mellin_weight {F : ℂ → ℂ} {p x : ℝ} (hx : 0 < x)
    (h : VerticalIntegrable F p) : VerticalIntegrable (fun z => (x : ℂ) ^ (-z) * F z) p := by
  change Integrable (fun y => (x : ℂ) ^ (-verticalPoint p y) * F (verticalPoint p y))
  have h' : Integrable (fun y => F (verticalPoint p y)) := h
  refine h'.bdd_mul (c := x ^ (-p)) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    have hpow := differentiable_neg.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))
    exact hpow.continuous.comp (by unfold verticalPoint; fun_prop)
  · filter_upwards with y
    rw [norm_cpow_eq_rpow_re_of_pos hx, neg_re, verticalPoint_re]

private theorem signedRamp_continuous_line {p : ℝ} (hp : 0 < p) :
    Continuous (fun y => signedRamp (verticalPoint p y)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have ho : {z : ℂ | 0 < z.re} ∈ 𝓝 (verticalPoint p t) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by simpa using hp)
  exact (differentiableOn_signedRamp.differentiableAt ho).continuousAt.comp
    (by unfold verticalPoint; fun_prop)

theorem verticalIntegrable_signedRamp {p : ℝ} (hp : 0 < p) :
    VerticalIntegrable signedRamp p := by
  obtain ⟨C, _, hC⟩ := signedRamp_rapidDecay 2 (b := p) hp
  refine verticalIntegrable_of_tail (C := C) (R := 1) le_rfl (signedRamp_continuous_line hp) ?_
  intro t ht
  simpa using hC (verticalPoint p t) (by simp) (by simp) (by simpa using ht)

/-- The two absolute vertical integrals and both horizontal edges of the full
signed ramp are controlled at every positive-real contour. -/
theorem mellinInv_signedRamp_shift {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b) (hx : 0 < x) :
    mellinInv b signedRamp x = mellinInv a signedRamp x := by
  obtain ⟨C, hC, hb⟩ := signedRamp_rapidDecay 2 (b := b) ha
  let K := Real.exp (b * |Real.log x|) * C
  have hpow := (differentiable_neg.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne')) :
    Differentiable ℂ (fun z : ℂ => (x : ℂ) ^ (-z)))
  refine mellinInv_eq_of_holomorphic_strip hab
    (hpow.differentiableOn.mul (differentiableOn_signedRamp.mono (fun z hz => ha.trans_le hz.1)))
    (verticalIntegrable_mellin_weight hx (verticalIntegrable_signedRamp ha))
    (verticalIntegrable_mellin_weight hx (verticalIntegrable_signedRamp (ha.trans_le hab)))
    (bound := fun T : ℝ => K * T⁻¹ ^ 2)
    (by simpa using (tendsto_inv_atTop_zero.pow 2).const_mul K) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT u hu t ht
  let z := verticalPoint u t
  have hz : |z.im| = T := by simpa [z] using ht
  have hdecay := hb z (by simpa [z] using hu.1) (by simpa [z] using hu.2) (by rwa [hz])
  rw [hz] at hdecay
  have hnorm : ‖signedRamp z‖ ≤ C * T⁻¹ ^ 2 := by
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < T ^ 2), mul_comm]
    exact hdecay
  have hw := norm_mellin_weight_le (b := b) hx ha.le (z := z)
    (by simpa [z] using hu.1) (by simpa [z] using hu.2)
  change ‖(x : ℂ) ^ (-z) * signedRamp z‖ ≤ K * T⁻¹ ^ 2
  rw [norm_mul]
  exact (mul_le_mul hw hnorm (norm_nonneg _) (Real.exp_nonneg _)).trans_eq (by dsimp [K]; ring)

/-- Division by the chosen zero factor remains integrable on both sides of
that zero, with no restrictions on its height or order. -/
theorem verticalIntegrable_dividedRamp {p : ℝ} {ρ : ℂ} (m : ℕ) (hp : 0 < p)
    (hpρ : p ≠ ρ.re) :
    VerticalIntegrable (fun z => signedRamp z / (z - ρ) ^ m) p := by
  obtain ⟨C, _, hb⟩ := signedRamp_rapidDecay 2 (b := p) hp
  apply verticalIntegrable_of_tail (C := C) (R := |ρ.im| + 1) (by linarith [abs_nonneg ρ.im])
  · exact (signedRamp_continuous_line hp).div
      (by unfold verticalPoint; fun_prop) (fun t => pow_ne_zero _ (sub_ne_zero.mpr fun h =>
        hpρ (by simpa using congrArg Complex.re h)))
  · intro t ht
    have ht₁ : 1 ≤ |t| := by linarith [abs_nonneg ρ.im]
    have him : |t| ≤ |t - ρ.im| + |ρ.im| := by
      simpa only [sub_add_cancel] using abs_add_le (t - ρ.im) ρ.im
    have hn : 1 ≤ ‖verticalPoint p t - ρ‖ :=
      (show 1 ≤ |t - ρ.im| by linarith).trans
        (by simpa only [sub_im, verticalPoint_im] using abs_im_le_norm (verticalPoint p t - ρ))
    have hdiv : ‖signedRamp (verticalPoint p t) / (verticalPoint p t - ρ) ^ m‖ ≤
        ‖signedRamp (verticalPoint p t)‖ := by
      rw [norm_div, norm_pow]
      exact div_le_self (norm_nonneg _) (one_le_pow₀ hn)
    exact (mul_le_mul_of_nonneg_left hdiv (by positivity)).trans
      (by simpa using hb (verticalPoint p t) (by simp) (by simp) (by simpa using ht₁))

/-- The divided contour crosses only the selected pole. The nonzero residue
uses the actual multiplicity of that zero. -/
theorem mellinInv_dividedRamp_shift_of_decomp {a b x : ℝ} {ρ r : ℂ}
    {m : ℕ} {G : ℂ → ℂ} (ha : 0 < a)
    (haρ : a < ρ.re) (hρb : ρ.re < b) (hx : 0 < x)
    (hG : DifferentiableOn ℂ G {w : ℂ | 0 < w.re})
    (hdef : ∀ w ≠ ρ, signedRamp w / (w - ρ) ^ m = r / (w - ρ) + G w) :
    mellinInv b (fun z => signedRamp z / (z - ρ) ^ m) x -
      mellinInv a (fun z => signedRamp z / (z - ρ) ^ m) x =
        r * (x : ℂ) ^ (-ρ) := by
  obtain ⟨C, hC, hdecay⟩ := signedRamp_rapidDecay 2 (b := b) ha
  let K := 4 * Real.exp (b * |Real.log x|) * C + ‖r * (x : ℂ) ^ (-ρ)‖
  have hlim : Tendsto (fun T : ℝ => K * T⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul K
  have hedges : ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc a b, ∀ t : ℝ, |t| = T →
      ‖mellinRegularPart x ρ r G (verticalPoint u t + ρ.im * I)‖ ≤ K * T⁻¹ := by
    filter_upwards [eventually_ge_atTop (2 * |ρ.im| + 2)] with T hT u hu t ht
    let z := verticalPoint u t + ρ.im * I
    have hT₁ : 1 ≤ T := by linarith [abs_nonneg ρ.im]
    have hre : z.re = u := by simp [z, add_re, mul_re]
    have him : z.im = t + ρ.im := by simp [z, add_im, mul_im]
    have hdist : T ≤ ‖z - ρ‖ := by
      have h := abs_im_le_norm (z - ρ)
      rwa [sub_im, him, add_sub_cancel_right, ht] at h
    have hn : z ≠ ρ := by
      intro he
      rw [he, sub_self, norm_zero] at hdist
      linarith
    have himB : T / 2 ≤ |z.im| := by
      have h := abs_add_le (t + ρ.im) (-ρ.im)
      rw [add_neg_cancel_right, ht, abs_neg, ← him] at h
      linarith
    have him₁ : 1 ≤ |z.im| := by linarith [abs_nonneg ρ.im]
    have hnorm : ‖signedRamp z‖ ≤ 4 * C * T⁻¹ := by
      have hh := hdecay z (by rw [hre]; exact hu.1) (by rw [hre]; exact hu.2) him₁
      have hsq : T / 4 ≤ |z.im| ^ 2 := by
        nlinarith only [himB, him₁, mul_nonneg (sub_nonneg.mpr him₁) (abs_nonneg z.im)]
      rw [← div_eq_mul_inv, le_div_iff₀ (by linarith : 0 < T)]
      nlinarith only [hh, mul_le_mul_of_nonneg_right hsq (norm_nonneg (signedRamp z))]
    have hpow := norm_mellin_weight_le (b := b) hx ha.le
      (show a ≤ z.re by rw [hre]; exact hu.1) (show z.re ≤ b by rw [hre]; exact hu.2)
    have hquo : ‖signedRamp z / (z - ρ) ^ m‖ ≤ ‖signedRamp z‖ := by
      rw [norm_div, norm_pow]
      exact div_le_self (norm_nonneg _) (one_le_pow₀ (hT₁.trans hdist))
    have hinv : ‖z - ρ‖⁻¹ ≤ T⁻¹ := inv_anti₀ (by linarith) hdist
    have hreg : mellinRegularPart x ρ r G z =
        (x : ℂ) ^ (-z) * (signedRamp z / (z - ρ) ^ m) -
          (r * (x : ℂ) ^ (-ρ)) / (z - ρ) := by
      rw [mellinRegularPart, dslope_of_ne _ hn, slope_def_module, smul_eq_mul, hdef _ hn]
      ring
    change ‖mellinRegularPart x ρ r G z‖ ≤ K * T⁻¹
    rw [hreg]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul ((x : ℂ) ^ (-z)),
      norm_div (r * (x : ℂ) ^ (-ρ)) _, div_eq_mul_inv ‖r * (x : ℂ) ^ (-ρ)‖]
    calc
      _ ≤ Real.exp (b * |Real.log x|) * (4 * C * T⁻¹) +
          ‖r * (x : ℂ) ^ (-ρ)‖ * T⁻¹ := add_le_add
            (mul_le_mul hpow (hquo.trans hnorm) (norm_nonneg _) (Real.exp_nonneg _))
            (mul_le_mul_of_nonneg_left hinv (norm_nonneg _))
      _ = _ := by ring
  apply mellinInv_sub_eq_pole hx haρ hρb
    (hG.mono (fun z hz' => ha.trans_le hz'.1)) hdef
    (verticalIntegrable_mellin_weight hx (verticalIntegrable_dividedRamp m ha haρ.ne))
    (verticalIntegrable_mellin_weight hx
      (verticalIntegrable_dividedRamp m (ha.trans (haρ.trans hρb)) hρb.ne.symm)) hlim
  · filter_upwards [hedges, eventually_ge_atTop (0 : ℝ)] with T hT h₀ u hu
    exact hT u hu T (abs_of_nonneg h₀)
  · filter_upwards [hedges, eventually_ge_atTop (0 : ℝ)] with T hT h₀ u hu
    exact hT u hu (-T) (by rw [abs_neg, abs_of_nonneg h₀])

theorem mellinInv_dividedRamp_shift {a b : ℝ} {ρ : ℂ} (ha : 0 < a)
    (haρ : a < ρ.re) (hρb : ρ.re < b) (hρ : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    ∃ (m : ℕ) (r : ℂ), 0 < m ∧ r ≠ 0 ∧ ∀ x : ℝ, 0 < x →
      mellinInv b (fun z => signedRamp z / (z - ρ) ^ m) x -
        mellinInv a (fun z => signedRamp z / (z - ρ) ^ m) x =
          r * (x : ℂ) ^ (-ρ) := by
  obtain ⟨m, r, G, hm, hr, hG, hdef⟩ := signedRamp_divided_pole (ha.trans haρ) hρ hz
  exact ⟨m, r, hm, hr, fun _ hx =>
    mellinInv_dividedRamp_shift_of_decomp ha haρ hρb hx hG hdef⟩

#print axioms mellinInv_signedRamp_shift
#print axioms mellinInv_dividedRamp_shift

end
end RH01
