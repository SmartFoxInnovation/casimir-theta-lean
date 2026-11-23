import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The positive theta weight

The n-th term is exp(|u|/2) (4a² - 6a) exp(-a), where
a = π(n+1)² exp(2|u|). This is the differential theta kernel on u ≥ 0,
extended evenly. The estimates below use the full series.
-/

namespace RH01

open MeasureTheory Set

noncomputable section

def thetaScale (u : ℝ) : ℝ := Real.pi * Real.exp (2 * |u|)

def thetaArgument (n : ℕ) (u : ℝ) : ℝ := thetaScale u * ((n : ℝ) + 1) ^ 2

def thetaTerm (n : ℕ) (u : ℝ) : ℝ :=
  let a := thetaArgument n u
  Real.exp (|u| / 2) * (4 * a ^ 2 - 6 * a) * Real.exp (-a)

def thetaWeight (u : ℝ) : ℝ := ∑' n, thetaTerm n u

theorem thetaScale_ge (u : ℝ) : 3 ≤ thetaScale u := by
  have h := Real.one_le_exp (show 0 ≤ 2 * |u| by positivity)
  exact Real.pi_gt_three.le.trans (by
    simpa [thetaScale] using mul_le_mul_of_nonneg_left h Real.pi_pos.le)

theorem argument_ge_scale (n : ℕ) (u : ℝ) : thetaScale u ≤ thetaArgument n u := by
  unfold thetaArgument
  have h : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  simpa using mul_le_mul_of_nonneg_left (one_le_pow₀ h) (by linarith [thetaScale_ge u])

theorem thetaTerm_pos (n : ℕ) (u : ℝ) : 0 < thetaTerm n u := by
  have ha := (thetaScale_ge u).trans (argument_ge_scale n u)
  have hpoly : 0 < 4 * thetaArgument n u ^ 2 - 6 * thetaArgument n u := by
    have h : 0 < thetaArgument n u * (4 * thetaArgument n u - 6) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  exact mul_pos (mul_pos (Real.exp_pos _) hpoly) (Real.exp_pos _)

private def thetaGeometric (n : ℕ) : ℝ := Real.exp (-((n : ℝ) + 1) / 4)

private theorem summable_thetaGeometric : Summable thetaGeometric := by
  have hq : Real.exp (- (1 / 4 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  refine ((summable_geometric_of_lt_one (Real.exp_nonneg _) hq).mul_left
    (Real.exp (-(1 / 4 : ℝ)))).congr fun n => ?_
  unfold thetaGeometric
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

private theorem thetaTerm_le (n : ℕ) (u : ℝ) :
    thetaTerm n u ≤ (32 * Real.exp (|u| / 2) * Real.exp (-thetaScale u / 4)) *
      thetaGeometric n := by
  let a := thetaArgument n u
  have hA : 3 ≤ thetaScale u := thetaScale_ge u
  have haA : thetaScale u ≤ a := argument_ge_scale n u
  have ha : 0 ≤ a := by linarith
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hnsq : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by
    simpa only [mul_one, pow_two] using mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ (n : ℝ) + 1)
  have han : (n : ℝ) + 1 ≤ a := by
    exact hnsq.trans (by
      simpa [a, thetaArgument] using mul_le_mul_of_nonneg_right
        (show 1 ≤ thetaScale u by linarith) (sq_nonneg ((n : ℝ) + 1)))
  have hp := Real.pow_div_factorial_le_exp (x := a / 2) (by positivity) 2
  norm_num [Nat.factorial_succ] at hp
  have hpoly : 4 * a ^ 2 - 6 * a ≤ 32 * Real.exp (a / 2) := by nlinarith
  have hsplit : -a / 2 ≤ -thetaScale u / 4 + (-((n : ℝ) + 1) / 4) := by linarith
  calc
    thetaTerm n u = Real.exp (|u| / 2) * (4 * a ^ 2 - 6 * a) * Real.exp (-a) := rfl
    _ ≤ Real.exp (|u| / 2) * (32 * Real.exp (a / 2)) * Real.exp (-a) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (Real.exp_nonneg _))
        (Real.exp_nonneg _)
    _ = (32 * Real.exp (|u| / 2)) * Real.exp (-a / 2) := by
      rw [show -a / 2 = a / 2 + (-a) by ring, Real.exp_add]
      ring
    _ ≤ (32 * Real.exp (|u| / 2)) *
        Real.exp (-thetaScale u / 4 + (-((n : ℝ) + 1) / 4)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsplit) (by positivity)
    _ = _ := by rw [Real.exp_add, thetaGeometric]; ring

theorem summable_thetaTerm (u : ℝ) : Summable fun n => thetaTerm n u :=
  Summable.of_nonneg_of_le (fun n => (thetaTerm_pos n u).le)
    (fun n => thetaTerm_le n u) (summable_thetaGeometric.mul_left _)

theorem thetaWeight_pos (u : ℝ) : 0 < thetaWeight u :=
  (summable_thetaTerm u).tsum_pos (fun n => (thetaTerm_pos n u).le) 0 (thetaTerm_pos 0 u)

theorem thetaWeight_even : Function.Even thetaWeight := by
  intro u
  simp [thetaWeight, thetaTerm, thetaArgument, thetaScale]

/-- The complete positive series has a fixed double-exponential majorant. -/
theorem thetaWeight_bound (u : ℝ) :
    thetaWeight u ≤ (32 * Real.exp (|u| / 2) * Real.exp (-thetaScale u / 4)) *
      ∑' n, thetaGeometric n := by
  unfold thetaWeight
  rw [← tsum_mul_left]
  exact (summable_thetaTerm u).tsum_le_tsum (fun n => thetaTerm_le n u)
    (summable_thetaGeometric.mul_left _)

private theorem thetaTilt_decay (c : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, Real.exp (c * |u|) * thetaWeight u ≤
      K * Real.exp (-|u|) := by
  let C := (c + 3 / 2) ^ 2 / 3
  let K := 32 * (∑' n, thetaGeometric n) * Real.exp C
  have hsum : 0 ≤ ∑' n, thetaGeometric n := tsum_nonneg fun _ => Real.exp_nonneg _
  refine ⟨K, by dsimp only [K]; positivity, fun u => ?_⟩
  have hexp := Real.pow_div_factorial_le_exp
    (x := 2 * |u|) (by positivity) 2
  norm_num [Nat.factorial_succ] at hexp
  have hgauss : (3 / 4 : ℝ) * |u| ^ 2 ≤ thetaScale u / 4 := by
    have haux := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.exp_nonneg (2 * |u|))
    unfold thetaScale
    nlinarith
  have he : c * |u| + |u| / 2 + -thetaScale u / 4 ≤ C + -|u| := by
    dsimp only [C]
    nlinarith [sq_nonneg (|u| - (2 / 3) * (c + 3 / 2))]
  calc
    _ ≤ Real.exp (c * |u|) *
        ((32 * Real.exp (|u| / 2) * Real.exp (-thetaScale u / 4)) *
          ∑' n, thetaGeometric n) :=
      mul_le_mul_of_nonneg_left (thetaWeight_bound u) (Real.exp_nonneg _)
    _ = (32 * ∑' n, thetaGeometric n) *
          Real.exp (c * |u| + |u| / 2 + -thetaScale u / 4) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    _ ≤ (32 * ∑' n, thetaGeometric n) * Real.exp (C + -|u|) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
    _ = _ := by rw [Real.exp_add]; dsimp only [K]; ring

theorem thetaTilt_bounded (c : ℝ) :
    ∃ K : ℝ, ∀ u : ℝ, Real.exp (c * |u|) * thetaWeight u ≤ K := by
  obtain ⟨K, hK, h⟩ := thetaTilt_decay c
  refine ⟨K, fun u => (h u).trans ?_⟩
  simpa using mul_le_mul_of_nonneg_left
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg u))) hK

/-- An arbitrary fixed exponential tilt is still integrable. -/
theorem integrable_exp_mul_thetaWeight (c : ℝ) :
    Integrable (fun u => Real.exp (c * |u|) * thetaWeight u) := by
  have hm : Measurable thetaWeight := by
    unfold thetaWeight
    apply Measurable.tsum
    intro n
    unfold thetaTerm thetaArgument thetaScale
    fun_prop
  have hneg : IntegrableOn (fun u : ℝ => Real.exp (-|u|)) (Iic 0) :=
    (integrableOn_exp_Iic 0).congr_fun
      (fun _ hu => by rw [abs_of_nonpos (mem_Iic.mp hu), neg_neg]) measurableSet_Iic
  have hpos : IntegrableOn (fun u : ℝ => Real.exp (-|u|)) (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).congr_fun
      (fun _ hu => by rw [abs_of_pos (mem_Ioi.mp hu)]) measurableSet_Ioi
  have hi : Integrable (fun u : ℝ => Real.exp (-|u|)) := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact hneg.union hpos
  obtain ⟨K, _, hK⟩ := thetaTilt_decay c
  apply (hi.const_mul K).mono'
    ((by fun_prop : Measurable (fun u : ℝ => Real.exp (c * |u|))).mul hm).aestronglyMeasurable
  filter_upwards with u
  change ‖Real.exp (c * |u|) * thetaWeight u‖ ≤ K * Real.exp (-|u|)
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (thetaWeight_pos u).le)]
  exact hK u

open Complex in
theorem thetaTilt_integrable_of_bound {g : ℝ → ℂ} (hg : Measurable g)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, ‖g u‖ ≤ C * thetaWeight u) (s : ℂ) :
    Integrable (fun u : ℝ => Complex.exp (s * u) * g u) := by
  have hf : Measurable (fun u : ℝ => Complex.exp (s * u) * g u) :=
    (by fun_prop : Measurable (fun u : ℝ => Complex.exp (s * u))).mul hg
  apply ((integrable_exp_mul_thetaWeight |s.re|).const_mul C).mono' hf.aestronglyMeasurable
  filter_upwards with u
  change ‖Complex.exp (s * u) * g u‖ ≤ C * (Real.exp (|s.re| * |u|) * thetaWeight u)
  have h := le_abs_self (s.re * u)
  rw [abs_mul] at h
  have hRe : (s * (u : ℂ)).re = s.re * u := by simp [mul_re]
  rw [norm_mul, norm_exp, hRe]
  calc
    _ ≤ Real.exp (s.re * u) * (C * thetaWeight u) :=
      mul_le_mul_of_nonneg_left (hb u) (Real.exp_nonneg _)
    _ ≤ Real.exp (|s.re| * |u|) * (C * thetaWeight u) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h) (mul_nonneg hC (thetaWeight_pos u).le)
    _ = _ := by ring

#print axioms thetaWeight_pos
#print axioms thetaWeight_bound
#print axioms integrable_exp_mul_thetaWeight

end
end RH01
