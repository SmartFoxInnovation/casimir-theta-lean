import RH01.MellinShift
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The simple-pole contribution to a vertical contour shift

The pole is subtracted with its actual complex residue. Truncated vertical
integrals of its real-centered reciprocal give ±π, so the regular part can
be shifted by Cauchy–Goursat even when its two absolute integrals diverge.
-/

namespace RH01

open Complex Filter MeasureTheory Set
open scoped Topology Interval

noncomputable section

private theorem reciprocalLine_continuous {c : ℝ} (hc : c ≠ 0) :
    Continuous (fun t : ℝ => ((c : ℂ) + t * I)⁻¹) := by
  refine Continuous.inv₀ (by fun_prop) fun t h => hc ?_
  simpa using congrArg Complex.re h

private theorem integral_reciprocalLine {c : ℝ} (hc : c ≠ 0) (T : ℝ) :
    (∫ t : ℝ in -T..T, ((c : ℂ) + t * I)⁻¹) = (2 * Real.arctan (T / c) : ℝ) := by
  let f := fun t : ℝ => ((c : ℂ) + t * I)⁻¹
  have hf : IntervalIntegrable f volume (-T) T :=
    (reciprocalLine_continuous hc).intervalIntegrable _ _
  apply Complex.ext
  · change RCLike.re (∫ t in -T..T, f t) = _
    rw [← intervalIntegral.intervalIntegral_re hf]
    have hre (t : ℝ) : (f t).re = c⁻¹ * (1 + (t / c) ^ 2)⁻¹ := by
      have h₁ : c * c + t * t ≠ 0 := by
        exact ne_of_gt (by nlinarith [sq_pos_of_ne_zero hc, sq_nonneg t])
      have h₂ : 1 + (t / c) ^ 2 ≠ 0 := by positivity
      simp only [f, Complex.inv_re, normSq_apply, add_re, ofReal_re, mul_re, I_re, ofReal_im,
        I_im, mul_zero, sub_zero, add_zero, add_im, mul_im, mul_one, zero_add]
      field_simp [hc, h₁, h₂]
    change (∫ t in -T..T, (f t).re) = _
    simp_rw [hre]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_div (fun t : ℝ => (1 + t ^ 2)⁻¹) hc,
      smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul,
      integral_inv_one_add_sq, neg_div, Real.arctan_neg, ofReal_re]
    ring
  · change RCLike.im (∫ t in -T..T, f t) = _
    rw [← intervalIntegral.intervalIntegral_im hf, ofReal_im]
    have him (t : ℝ) : (f (-t)).im = -(f t).im := by
      simp [f, Complex.inv_im, normSq_apply, neg_mul, neg_div]
    have h := intervalIntegral.integral_comp_neg (a := -T) (b := T) (fun t => (f t).im)
    simp only [him, neg_neg, intervalIntegral.integral_neg] at h
    change (∫ t in -T..T, (f t).im) = 0
    linarith

private theorem tendsto_reciprocalLine {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T, ((c : ℂ) + t * I)⁻¹)
      atTop (𝓝 (if 0 < c then (Real.pi : ℂ) else -(Real.pi : ℂ))) := by
  simp_rw [integral_reciprocalLine hc]
  by_cases h : 0 < c
  · rw [if_pos h]
    have ha := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (tendsto_id.atTop_div_const h)
    have hp : 2 * (Real.pi / 2) = Real.pi := by ring
    simpa only [Function.comp_def, id_eq, hp] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp (ha.const_mul 2)
  · rw [if_neg h]
    have hc' : c < 0 := lt_of_le_of_ne (le_of_not_gt h) hc
    have ha := (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
      (tendsto_id.atTop_div_const_of_neg hc')
    have hp : 2 * -(Real.pi / 2) = -Real.pi := by ring
    simpa only [Function.comp_def, id_eq, hp, ofReal_neg] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp (ha.const_mul 2)

/-- A right-to-left vertical displacement crosses a simple pole of residue r.
The real-centered coordinate can be obtained by translating the imaginary axis. -/
theorem verticalIntegral_sub_eq_residue {a b c : ℝ} {f regular : ℂ → ℂ} {r : ℂ}
    (hac : a < c) (hcb : c < b)
    (hregular : DifferentiableOn ℂ regular {z : ℂ | z.re ∈ Icc a b})
    (hdecomp : ∀ z ≠ (c : ℂ), f z = r / (z - c) + regular z)
    (ha : VerticalIntegrable f a) (hb : VerticalIntegrable f b)
    {bound : ℝ → ℝ} (hbound : Tendsto bound atTop (𝓝 0))
    (htop : ∀ᶠ T : ℝ in atTop, ∀ x ∈ Icc a b, ‖regular ((x : ℂ) + T * I)‖ ≤ bound T)
    (hbottom : ∀ᶠ T in atTop, ∀ x ∈ Icc a b, ‖regular ((x : ℂ) + (-T : ℝ) * I)‖ ≤ bound T) :
    (∫ y : ℝ, f ((b : ℂ) + y * I)) - (∫ y : ℝ, f ((a : ℂ) + y * I)) =
      (2 * (Real.pi : ℂ)) * r := by
  have hline (x : ℝ) (hx : x ≠ c) (hi : VerticalIntegrable f x) :
      Tendsto (fun T : ℝ => ∫ y in -T..T, regular ((x : ℂ) + y * I)) atTop
        (𝓝 ((∫ y : ℝ, f ((x : ℂ) + y * I)) -
          r * (if 0 < x - c then (Real.pi : ℂ) else -(Real.pi : ℂ)))) := by
    have hlim := (intervalIntegral_tendsto_integral hi tendsto_neg_atTop_atBot tendsto_id).sub
      ((tendsto_reciprocalLine (sub_ne_zero.mpr hx)).const_mul r)
    apply hlim.congr
    intro T
    dsimp only [id_eq]
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub hi.intervalIntegrable
        (((reciprocalLine_continuous (sub_ne_zero.mpr hx)).const_mul r).intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    have hn : (x : ℂ) + t * I ≠ (c : ℂ) := fun h => hx (by simpa using congrArg Complex.re h)
    rw [hdecomp _ hn, div_eq_mul_inv]
    have he : (x : ℂ) + t * I - c = ((x - c : ℝ) : ℂ) + t * I := by push_cast; ring
    rw [he, add_sub_cancel_left]
  have h := verticalLimit_eq_of_holomorphic_strip (hac.trans hcb).le hregular
    (hline a hac.ne ha) (hline b hcb.ne.symm hb) hbound htop hbottom
  simp only [if_pos (sub_pos.mpr hcb),
    if_neg (not_lt.mpr (sub_nonpos.mpr hac.le))] at h
  linear_combination h

/-- The same residue formula with the contour centered at the imaginary part
of the pole. The actual vertical integrals are translation invariant. -/
theorem verticalIntegral_sub_eq_complexResidue {a b : ℝ} {ρ r : ℂ}
    {f regular : ℂ → ℂ} (haρ : a < ρ.re) (hρb : ρ.re < b)
    (hregular : DifferentiableOn ℂ regular {z : ℂ | z.re ∈ Icc a b})
    (hdecomp : ∀ z ≠ ρ, f z = r / (z - ρ) + regular z)
    (ha : VerticalIntegrable f a) (hb : VerticalIntegrable f b)
    {bound : ℝ → ℝ} (hbound : Tendsto bound atTop (𝓝 0))
    (htop : ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc a b,
      ‖regular ((u : ℂ) + T * I + ρ.im * I)‖ ≤ bound T)
    (hbottom : ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc a b,
      ‖regular ((u : ℂ) + (-T : ℝ) * I + ρ.im * I)‖ ≤ bound T) :
    (∫ y : ℝ, f ((b : ℂ) + y * I)) - (∫ y : ℝ, f ((a : ℂ) + y * I)) =
      (2 * (Real.pi : ℂ)) * r := by
  let shift := fun z : ℂ => z + (ρ.im : ℂ) * I
  have hshift (z : ℂ) : shift z - ρ = z - (ρ.re : ℂ) := by
    dsimp only [shift]
    linear_combination re_add_im ρ
  have hreg : DifferentiableOn ℂ (regular ∘ shift) {z : ℂ | z.re ∈ Icc a b} :=
    hregular.comp (by dsimp only [shift]; fun_prop) (by
      intro z hz
      simpa [shift, mul_re] using hz)
  have hdec (z : ℂ) (hz : z ≠ (ρ.re : ℂ)) :
      (f ∘ shift) z = r / (z - (ρ.re : ℂ)) + (regular ∘ shift) z := by
    have hn : shift z ≠ ρ := sub_ne_zero.mp (hshift z ▸ sub_ne_zero.mpr hz)
    change f (shift z) = _
    rw [hdecomp _ hn, hshift]
    rfl
  have hline (p : ℝ) :
      (fun y : ℝ => (f ∘ shift) ((p : ℂ) + y * I)) =
        fun y : ℝ => f ((p : ℂ) + (y + ρ.im : ℝ) * I) := by
    funext y
    dsimp only [Function.comp_apply, shift]
    push_cast
    congr 1
    ring
  have hi (p : ℝ) (hp : VerticalIntegrable f p) : VerticalIntegrable (f ∘ shift) p := by
    unfold VerticalIntegrable
    rw [hline]
    exact hp.comp_add_right ρ.im
  have h := verticalIntegral_sub_eq_residue haρ hρb hreg hdec (hi a ha) (hi b hb)
    hbound htop hbottom
  simpa only [hline, integral_add_right_eq_self (fun y : ℝ => f ((b : ℂ) + y * I)),
    integral_add_right_eq_self (fun y : ℝ => f ((a : ℂ) + y * I))] using h

/-- Holomorphic remainder after applying the inverse Mellin weight and
subtracting the resulting weighted simple pole. -/
def mellinRegularPart (x : ℝ) (ρ r : ℂ) (G : ℂ → ℂ) (z : ℂ) : ℂ :=
  (x : ℂ) ^ (-z) * G z + r * dslope (fun w : ℂ => (x : ℂ) ^ (-w)) ρ z

/-- Mellin displacement across a simple pole, with the full complex phase. -/
theorem mellinInv_sub_eq_pole {a b x : ℝ} {ρ r : ℂ} {F G : ℂ → ℂ}
    (hx : 0 < x) (haρ : a < ρ.re) (hρb : ρ.re < b)
    (hG : DifferentiableOn ℂ G {z : ℂ | z.re ∈ Icc a b})
    (hF : ∀ z ≠ ρ, F z = r / (z - ρ) + G z)
    (ha : VerticalIntegrable (fun z => (x : ℂ) ^ (-z) * F z) a)
    (hb : VerticalIntegrable (fun z => (x : ℂ) ^ (-z) * F z) b)
    {bound : ℝ → ℝ} (hbound : Tendsto bound atTop (𝓝 0))
    (htop : ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc a b,
      ‖mellinRegularPart x ρ r G ((u : ℂ) + T * I + ρ.im * I)‖ ≤ bound T)
    (hbottom : ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc a b,
      ‖mellinRegularPart x ρ r G ((u : ℂ) + (-T : ℝ) * I + ρ.im * I)‖ ≤ bound T) :
    mellinInv b F x - mellinInv a F x = r * (x : ℂ) ^ (-ρ) := by
  let p := fun z : ℂ => (x : ℂ) ^ (-z)
  have hp : Differentiable ℂ p :=
    differentiable_neg.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))
  have hds : Differentiable ℂ (dslope p ρ) :=
    differentiableOn_univ.mp
      ((differentiableOn_dslope (univ_mem : Set.univ ∈ 𝓝 ρ)).2 hp.differentiableOn)
  have hg : DifferentiableOn ℂ (mellinRegularPart x ρ r G) {z : ℂ | z.re ∈ Icc a b} :=
    (hp.differentiableOn.mul hG).add (hds.differentiableOn.const_mul r)
  have hdefl (z : ℂ) (hz : z ≠ ρ) :
      (x : ℂ) ^ (-z) * F z =
        (r * (x : ℂ) ^ (-ρ)) / (z - ρ) + mellinRegularPart x ρ r G z := by
    rw [hF _ hz, mellinRegularPart, dslope_of_ne _ hz, slope_def_module, smul_eq_mul]
    field_simp [sub_ne_zero.mpr hz]
    ring
  have h := verticalIntegral_sub_eq_complexResidue haρ hρb hg hdefl ha hb hbound htop hbottom
  simp only [mellinInv, smul_eq_mul]
  rw [← smul_sub, h, Complex.real_smul]
  push_cast
  field_simp [Real.pi_ne_zero]

#print axioms mellinInv_sub_eq_pole

end
end RH01
