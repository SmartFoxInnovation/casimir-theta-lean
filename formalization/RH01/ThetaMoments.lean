import RH01.ThetaWeight
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven

/-!
# Derivatives of the Gaussian theta series

The k-th moment inserts the k-th power of the Gaussian argument. Its
derivative is a linear combination of two adjacent moments. A local
geometric majorant justifies differentiation through the full series.
-/

namespace RH01

open Set MeasureTheory HurwitzZeta

noncomputable section

def gaussianArgument (n : ℕ) (u : ℝ) : ℝ :=
  Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u)

def gaussianMomentTerm (k n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (u / 2) * gaussianArgument n u ^ k * Real.exp (-gaussianArgument n u)

def gaussianMoment (k : ℕ) (u : ℝ) : ℝ := ∑' n, gaussianMomentTerm k n u

private theorem gaussianArgument_pos (n : ℕ) (u : ℝ) : 0 < gaussianArgument n u := by
  unfold gaussianArgument
  positivity

theorem gaussianMomentTerm_nonneg (k n : ℕ) (u : ℝ) : 0 ≤ gaussianMomentTerm k n u := by
  unfold gaussianMomentTerm
  have := gaussianArgument_pos n u
  positivity

/-- Absorb any fixed power into half of the Gaussian exponent. -/
theorem gaussianMomentTerm_bound (k n : ℕ) (u : ℝ) :
    gaussianMomentTerm k n u ≤
      ((2 : ℝ) ^ k * k.factorial) * Real.exp (u / 2) *
        Real.exp (-gaussianArgument n u / 2) := by
  let a := gaussianArgument n u
  have ha : 0 < a := gaussianArgument_pos n u
  have h := Real.pow_div_factorial_le_exp (x := a / 2) (by positivity) k
  have hfac : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hp : a ^ k ≤ ((2 : ℝ) ^ k * k.factorial) * Real.exp (a / 2) := by
    rw [div_pow, div_div] at h
    simpa only [mul_comm] using (div_le_iff₀ (mul_pos (by positivity) hfac)).mp h
  calc
    gaussianMomentTerm k n u = Real.exp (u / 2) * a ^ k * Real.exp (-a) := rfl
    _ ≤ Real.exp (u / 2) * (((2 : ℝ) ^ k * k.factorial) * Real.exp (a / 2)) * Real.exp (-a) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = _ := by
      rw [show -a / 2 = a / 2 + -a by ring, Real.exp_add]
      ring

private theorem gaussianMomentTerm_local_bound (k n : ℕ) {v r R : ℝ} (h₁ : r ≤ v) (h₂ : v ≤ R) :
    gaussianMomentTerm k n v ≤
      ((2 : ℝ) ^ k * k.factorial) * Real.exp (R / 2) *
        (Real.exp (-(Real.pi * Real.exp (2 * r)) / 2)) ^ n := by
  have he : Real.exp (2 * r) ≤ Real.exp (2 * v) := Real.exp_le_exp.mpr (by linarith)
  have hn : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have ha : (n : ℝ) * (Real.pi * Real.exp (2 * r)) ≤ gaussianArgument n v := by
    unfold gaussianArgument
    have hmin := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ Real.pi * Real.exp (2 * r))
    have hmax := mul_le_mul_of_nonneg_left he
      (by positivity : 0 ≤ Real.pi * ((n : ℝ) + 1) ^ 2)
    linarith only [hmin, hmax]
  apply (gaussianMomentTerm_bound k n v).trans
  rw [← Real.exp_nat_mul]
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  · exact Real.exp_le_exp.mpr (by linarith only [ha])
  · positivity
  · positivity

theorem summable_gaussianMomentTerm (k : ℕ) (u : ℝ) : Summable (fun n => gaussianMomentTerm k n u) := by
  have hq : Real.exp (-(Real.pi * Real.exp (2 * u)) / 2) < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_lt_zero.mpr (by positivity)) two_pos)
  exact Summable.of_nonneg_of_le (fun n => gaussianMomentTerm_nonneg k n u)
    (fun n => gaussianMomentTerm_local_bound k n le_rfl le_rfl)
    ((summable_geometric_of_lt_one (Real.exp_nonneg _) hq).mul_left _)

private theorem hasDerivAt_gaussianMomentTerm (k n : ℕ) (u : ℝ) :
    HasDerivAt (gaussianMomentTerm k n)
      (((1 / 2 : ℝ) + 2 * k) * gaussianMomentTerm k n u - 2 * gaussianMomentTerm (k + 1) n u) u := by
  have hArg : HasDerivAt (gaussianArgument n) (2 * gaussianArgument n u) u := by
    have h := (((hasDerivAt_id u).const_mul (2 : ℝ)).exp).const_mul
      (Real.pi * ((n : ℝ) + 1) ^ 2)
    have he : Real.pi * ((n : ℝ) + 1) ^ 2 * (Real.exp (2 * u) * (2 * 1)) =
        2 * gaussianArgument n u := by unfold gaussianArgument; ring
    exact he ▸ h
  have hExp := ((hasDerivAt_id u).div_const (2 : ℝ)).exp
  have hp := hArg.fun_pow k
  have hm := hArg.neg.exp
  have h := (hExp.fun_mul hp).fun_mul hm
  let a := gaussianArgument n u
  have hpure : (k : ℝ) * a ^ (k - 1) * (2 * a) = 2 * k * a ^ k := by
    cases k with
    | zero => simp
    | succ k => simp only [Nat.succ_sub_one, pow_succ]; ring
  have heq :
      (Real.exp (u / 2) * (1 / 2) * a ^ k +
        Real.exp (u / 2) * ((k : ℝ) * a ^ (k - 1) * (2 * a))) * Real.exp (-a) +
        Real.exp (u / 2) * a ^ k * (Real.exp (-a) * -(2 * a)) =
      ((1 / 2 : ℝ) + 2 * k) * gaussianMomentTerm k n u - 2 * gaussianMomentTerm (k + 1) n u := by
    unfold gaussianMomentTerm
    change _ = ((1 / 2 : ℝ) + 2 * k) * (Real.exp (u / 2) * a ^ k * Real.exp (-a)) -
      2 * (Real.exp (u / 2) * a ^ (k + 1) * Real.exp (-a))
    rw [hpure, pow_succ]
    ring
  exact heq ▸ h

theorem hasDerivAt_gaussianMoment (k : ℕ) (u : ℝ) :
    HasDerivAt (gaussianMoment k)
      (((1 / 2 : ℝ) + 2 * k) * gaussianMoment k u - 2 * gaussianMoment (k + 1) u) u := by
  let c : ℝ := 1 / 2 + 2 * k
  let q := Real.exp (-(Real.pi * Real.exp (2 * (u - 1))) / 2)
  let C := fun j : ℕ => ((2 : ℝ) ^ j * j.factorial) * Real.exp ((u + 1) / 2)
  let D := fun n : ℕ => (c * C k + 2 * C (k + 1)) * q ^ n
  have hq : q < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_lt_zero.mpr (by positivity)) two_pos)
  have hd : Summable D :=
    (summable_geometric_of_lt_one (Real.exp_nonneg _) hq).mul_left _
  have hu : u ∈ Ioo (u - 1) (u + 1) := ⟨by linarith, by linarith⟩
  have hbound (n : ℕ) (v : ℝ) (hv : v ∈ Ioo (u - 1) (u + 1)) :
      ‖c * gaussianMomentTerm k n v - 2 * gaussianMomentTerm (k + 1) n v‖ ≤ D n := by
    have hc : 0 ≤ c := by dsimp only [c]; positivity
    have h₁ : gaussianMomentTerm k n v ≤ C k * q ^ n :=
      gaussianMomentTerm_local_bound k n hv.1.le hv.2.le
    have h₂ : gaussianMomentTerm (k + 1) n v ≤ C (k + 1) * q ^ n :=
      gaussianMomentTerm_local_bound (k + 1) n hv.1.le hv.2.le
    refine (norm_sub_le _ _).trans ?_
    rw [Real.norm_of_nonneg (mul_nonneg hc (gaussianMomentTerm_nonneg _ _ _)),
      Real.norm_of_nonneg (mul_nonneg two_pos.le (gaussianMomentTerm_nonneg _ _ _))]
    calc
      _ ≤ c * (C k * q ^ n) + 2 * (C (k + 1) * q ^ n) :=
        add_le_add (mul_le_mul_of_nonneg_left h₁ hc) (mul_le_mul_of_nonneg_left h₂ two_pos.le)
      _ = _ := by dsimp only [D]; ring
  have h := hasDerivAt_tsum_of_isPreconnected hd isOpen_Ioo (convex_Ioo _ _).isPreconnected
    (fun n v _ => hasDerivAt_gaussianMomentTerm k n v) hbound hu
    (summable_gaussianMomentTerm k u) hu
  rw [Summable.tsum_sub ((summable_gaussianMomentTerm k u).mul_left _)
    ((summable_gaussianMomentTerm (k + 1) u).mul_left _), tsum_mul_left, tsum_mul_left] at h
  exact h

/-- On the positive half-line the explicit kernel is the second derivative
of the zeroth Gaussian moment with one quarter of that moment subtracted. -/
theorem thetaWeight_eq_gaussianMoments {u : ℝ} (hu : 0 ≤ u) :
    thetaWeight u = 4 * gaussianMoment 2 u - 6 * gaussianMoment 1 u := by
  unfold gaussianMoment thetaWeight
  rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_sub
    ((summable_gaussianMomentTerm 2 u).mul_left _) ((summable_gaussianMomentTerm 1 u).mul_left _)]
  apply tsum_congr
  intro n
  have ha : thetaArgument n u = gaussianArgument n u := by
    unfold thetaArgument thetaScale gaussianArgument
    rw [abs_of_nonneg hu]
    ring
  unfold thetaTerm gaussianMomentTerm
  rw [abs_of_nonneg hu, ha]
  ring

theorem gaussianMoment_nonneg (k : ℕ) (u : ℝ) : 0 ≤ gaussianMoment k u :=
  tsum_nonneg fun n => gaussianMomentTerm_nonneg k n u

theorem continuous_gaussianMoment (k : ℕ) : Continuous (gaussianMoment k) :=
  continuous_iff_continuousAt.mpr fun u => (hasDerivAt_gaussianMoment k u).continuousAt

private theorem gaussianArgument_abs (n : ℕ) (u : ℝ) :
    gaussianArgument n |u| = thetaArgument n u := by
  unfold gaussianArgument thetaArgument thetaScale
  ring

theorem gaussianMoment_abs_le_thetaWeight {k : ℕ} (hk : k ≤ 2) (u : ℝ) :
    gaussianMoment k |u| ≤ thetaWeight u := by
  unfold gaussianMoment thetaWeight
  refine (summable_gaussianMomentTerm k |u|).tsum_le_tsum (fun n => ?_) (summable_thetaTerm u)
  have hA := (thetaScale_ge u).trans (argument_ge_scale n u)
  have ha : thetaArgument n u ^ k ≤ thetaArgument n u ^ 2 :=
    pow_le_pow_right₀ (show 1 ≤ thetaArgument n u by linarith) hk
  have hpoly : thetaArgument n u ^ 2 ≤ 4 * thetaArgument n u ^ 2 - 6 * thetaArgument n u := by
    nlinarith only [mul_nonneg (by linarith : 0 ≤ thetaArgument n u)
      (show 0 ≤ thetaArgument n u - 2 by linarith)]
  unfold gaussianMomentTerm thetaTerm
  rw [gaussianArgument_abs]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (ha.trans hpoly) (Real.exp_nonneg _)) (Real.exp_nonneg _)

theorem integrable_exp_mul_gaussianMoment {k : ℕ} (hk : k ≤ 2) (c : ℝ) :
    Integrable (fun u => Real.exp (c * |u|) * gaussianMoment k |u|) := by
  have hm : Continuous (fun u => Real.exp (c * |u|) * gaussianMoment k |u|) :=
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (c * |u|))).mul
      ((continuous_gaussianMoment k).comp continuous_abs)
  apply (integrable_exp_mul_thetaWeight c).mono' hm.aestronglyMeasurable
  filter_upwards with u
  change ‖Real.exp (c * |u|) * gaussianMoment k |u|‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (gaussianMoment_nonneg _ _))]
  exact mul_le_mul_of_nonneg_left (gaussianMoment_abs_le_thetaWeight hk u) (Real.exp_nonneg _)

/-- The zeroth moment is the nonconstant part of the even Jacobi kernel. -/
theorem gaussianMoment_zero_eq_evenKernel (u : ℝ) :
    gaussianMoment 0 u = Real.exp (u / 2) * (evenKernel 0 (Real.exp (2 * u)) - 1) / 2 := by
  have h := (hasSum_nat_cosKernel₀ 0 (Real.exp_pos (2 * u))).mul_left (Real.exp (u / 2) / 2)
  have hterm (n : ℕ) : gaussianMomentTerm 0 n u =
      (Real.exp (u / 2) / 2) *
        (2 * Real.cos (2 * Real.pi * 0 * ((n : ℝ) + 1)) *
          Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u))) := by
    unfold gaussianMomentTerm gaussianArgument
    simp
    ring
  rw [gaussianMoment, funext hterm, h.tsum_eq]
  simp only [QuotientAddGroup.mk_zero, ← evenKernel_eq_cosKernel_of_zero]
  ring

theorem evenKernel_exp_neg (u : ℝ) :
    evenKernel 0 (Real.exp (2 * -u)) = Real.exp u * evenKernel 0 (Real.exp (2 * u)) := by
  rw [evenKernel_functional_equation, ← evenKernel_eq_cosKernel_of_zero]
  have h₁ : Real.exp (2 * -u) ^ (1 / 2 : ℝ) = Real.exp (-u) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  have h₂ : 1 / Real.exp (2 * -u) = Real.exp (2 * u) := by
    rw [show 2 * -u = -(2 * u) by ring, Real.exp_neg, one_div, inv_inv]
  rw [h₁, h₂, one_div, ← Real.exp_neg, neg_neg]

/-- The Jacobi inversion identity keeps its full zero-mode correction. -/
theorem gaussianMoment_zero_neg (u : ℝ) :
    gaussianMoment 0 (-u) = gaussianMoment 0 u +
      (Real.exp (u / 2) - Real.exp (-u / 2)) / 2 := by
  rw [gaussianMoment_zero_eq_evenKernel, gaussianMoment_zero_eq_evenKernel, evenKernel_exp_neg]
  have hE : Real.exp (-u / 2) * Real.exp u = Real.exp (u / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-u / 2) * Real.exp u) * evenKernel 0 (Real.exp (2 * u)) / 2 -
        Real.exp (-u / 2) / 2 := by ring
    _ = _ := by rw [hE]; ring

def gaussianMomentSlope (u : ℝ) : ℝ := gaussianMoment 0 u / 2 - 2 * gaussianMoment 1 u

theorem hasDerivAt_gaussianMoment_zero (u : ℝ) :
    HasDerivAt (gaussianMoment 0) (gaussianMomentSlope u) u := by
  simpa [gaussianMomentSlope, div_eq_mul_inv, mul_comm] using hasDerivAt_gaussianMoment 0 u

theorem hasDerivAt_gaussianMomentSlope (u : ℝ) (hu : 0 ≤ u) :
    HasDerivAt gaussianMomentSlope (thetaWeight u + gaussianMoment 0 u / 4) u := by
  have h := ((hasDerivAt_gaussianMoment 0 u).div_const 2).sub
    ((hasDerivAt_gaussianMoment 1 u).const_mul 2)
  rw [thetaWeight_eq_gaussianMoments hu]
  have he :
      (((1 / 2 : ℝ) + 2 * (0 : ℕ)) * gaussianMoment 0 u - 2 * gaussianMoment (0 + 1) u) / 2 -
        2 * (((1 / 2 : ℝ) + 2 * (1 : ℕ)) * gaussianMoment 1 u - 2 * gaussianMoment (1 + 1) u) =
      (4 * gaussianMoment 2 u - 6 * gaussianMoment 1 u) + gaussianMoment 0 u / 4 := by norm_num; ring
  exact he ▸ h

theorem gaussianMomentSlope_zero : gaussianMomentSlope 0 = -(1 / 4 : ℝ) := by
  have hleft : HasDerivAt (fun u : ℝ => gaussianMoment 0 (-u)) (-gaussianMomentSlope 0) 0 := by
    simpa only [Function.comp_def, neg_zero, mul_neg_one] using
      (hasDerivAt_gaussianMoment_zero (-(0 : ℝ))).comp 0 (hasDerivAt_neg 0)
  have hplus := ((hasDerivAt_id (0 : ℝ)).div_const 2).exp
  have hminus := ((hasDerivAt_neg (0 : ℝ)).div_const 2).exp
  have hright : HasDerivAt (fun u : ℝ => gaussianMoment 0 u +
      (Real.exp (u / 2) - Real.exp (-u / 2)) / 2) (gaussianMomentSlope 0 + 1 / 2) 0 := by
    have h := (hasDerivAt_gaussianMoment_zero 0).fun_add ((hplus.sub hminus).div_const 2)
    norm_num [Pi.sub_apply] at h ⊢
    exact h
  have heq := hleft.deriv.symm.trans ((funext gaussianMoment_zero_neg) ▸ hright.deriv)
  linarith

theorem continuous_thetaWeight : Continuous thetaWeight := by
  have h (u : ℝ) : thetaWeight u = 4 * gaussianMoment 2 |u| - 6 * gaussianMoment 1 |u| := by
    rw [← thetaWeight_eq_gaussianMoments (abs_nonneg u)]
    rcases le_or_gt 0 u with hu | hu
    · rw [abs_of_nonneg hu]
    · rw [abs_of_neg hu, thetaWeight_even u]
  rw [funext h]
  exact (((continuous_gaussianMoment 2).comp continuous_abs).const_mul 4).sub
    (((continuous_gaussianMoment 1).comp continuous_abs).const_mul 6)

#print axioms hasDerivAt_gaussianMoment
#print axioms thetaWeight_eq_gaussianMoments
#print axioms gaussianMomentSlope_zero

end
end RH01
