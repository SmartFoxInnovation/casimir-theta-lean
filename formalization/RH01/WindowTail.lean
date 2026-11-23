import RH01.Casimir
import RH01.ThetaWeight
import Mathlib.MeasureTheory.Function.Floor

/-! The moving-window tail for the actual centered prime ramp. -/

namespace RH01

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

theorem measurable_primeRamp : Measurable primeRamp := by
  let T (n : ℕ) (x : ℝ) :=
    if n ∈ Finset.Icc 1 ⌊x⌋₊ then ArithmeticFunction.vonMangoldt n *
      max (x / (n : ℝ) - 1) 0 else 0
  have hT (n : ℕ) : Measurable (T n) := by
    change Measurable (fun x : ℝ => if n ∈ Finset.Icc 1 ⌊x⌋₊ then _ else _)
    have hset : MeasurableSet {x : ℝ | n ∈ Finset.Icc 1 ⌊x⌋₊} := by
      by_cases hn : 1 ≤ n
      · simpa only [Finset.mem_Icc, hn, true_and] using
          measurableSet_le (f := fun _ : ℝ => n) measurable_const (Nat.measurable_floor (R := ℝ))
      · simp [Finset.mem_Icc, hn]
    exact Measurable.ite hset (by fun_prop) measurable_const
  have hsum : (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ArithmeticFunction.vonMangoldt n * max (x / (n : ℝ) - 1) 0) = fun x => ∑' n, T n x := by
    funext x
    rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn => if_neg hn)]
    exact Finset.sum_congr rfl fun n hn => (if_pos hn).symm
  have hs : Measurable (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ArithmeticFunction.vonMangoldt n * max (x / (n : ℝ) - 1) 0) := by
    rw [hsum]
    exact Measurable.tsum hT
  exact hs.sub (by fun_prop)

theorem measurable_normalizedRamp : Measurable normalizedRamp := by
  unfold normalizedRamp
  exact Measurable.ite (measurableSet_le measurable_const measurable_id)
    (measurable_primeRamp.div (by fun_prop)) measurable_const

private theorem primeRamp_abs_le {x : ℝ} (hx : 1 ≤ x) : |primeRamp x| ≤ 4 * x ^ 3 := by
  let f := fun n : ℕ => ArithmeticFunction.vonMangoldt n * max (x / (n : ℝ) - 1) 0
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hlog₀ : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  have hsum₀ : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n :=
    Finset.sum_nonneg fun n _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_max_right ..)
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊x⌋₊) : f n ≤ x ^ 2 := by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1
    have hn0 : 0 < (n : ℝ) := zero_lt_one.trans_le hn1
    have hnx : (n : ℝ) ≤ x := (by exact_mod_cast h2 : (n : ℝ) ≤ ⌊x⌋₊).trans
      (Nat.floor_le hx0.le)
    have hΛ : ArithmeticFunction.vonMangoldt n ≤ x :=
      ArithmeticFunction.vonMangoldt_le_log.trans ((Real.log_le_log hn0 hnx).trans hlog)
    have hr : max (x / (n : ℝ) - 1) 0 ≤ x := by
      have hd : x / (n : ℝ) ≤ x := (div_le_iff₀ hn0).2 (by nlinarith only [mul_nonneg hx0.le (sub_nonneg.mpr hn1)])
      exact max_le (by linarith) hx0.le
    simpa only [pow_two] using mul_le_mul hΛ hr (le_max_right ..) hx0.le
  have hc : ((Finset.Icc 1 ⌊x⌋₊).card : ℝ) ≤ x := by
    rw [Nat.card_Icc]
    simpa using Nat.floor_le hx0.le
  have hsum : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n ≤ x ^ 3 := calc
    _ ≤ ∑ _ ∈ Finset.Icc 1 ⌊x⌋₊, x ^ 2 := Finset.sum_le_sum hterm
    _ = ((Finset.Icc 1 ⌊x⌋₊).card : ℝ) * x ^ 2 := by simp [nsmul_eq_mul]
    _ ≤ x * x ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = _ := by ring
  have hcenter : |Real.log x - 1 - Real.eulerMascheroniConstant| ≤ x + 2 := by
    apply abs_le.mpr
    constructor <;> linarith [Real.one_half_lt_eulerMascheroniConstant,
      Real.eulerMascheroniConstant_lt_two_thirds]
  have hx2 : x ≤ x ^ 2 := by nlinarith only [mul_nonneg hx0.le (sub_nonneg.mpr hx)]
  have hx3 : x ^ 2 ≤ x ^ 3 := by nlinarith only [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx)]
  unfold primeRamp
  change |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n) -
    x * (Real.log x - 1 - Real.eulerMascheroniConstant)| ≤ _
  calc
    _ ≤ |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n)| +
        |x * (Real.log x - 1 - Real.eulerMascheroniConstant)| := abs_sub _ _
    _ ≤ x ^ 3 + x * (x + 2) := by
      rw [abs_of_nonneg hsum₀, abs_mul, abs_of_pos hx0]
      exact add_le_add hsum (mul_le_mul_of_nonneg_left hcenter hx0.le)
    _ ≤ _ := by linarith only [hx2, hx3]

theorem normalizedRamp_exp_abs_le (t : ℝ) :
    |normalizedRamp (Real.exp t)| ≤ 4 * Real.exp (3 * t) := by
  by_cases hx : 1 ≤ Real.exp t
  · have hx1 : 1 ≤ (Real.exp t) ^ (1 / 2 : ℝ) := Real.one_le_rpow hx (by norm_num)
    rw [normalizedRamp, if_pos hx, abs_div, abs_of_nonneg (Real.rpow_nonneg (Real.exp_nonneg _) _)]
    calc
      _ ≤ |primeRamp (Real.exp t)| := div_le_self (abs_nonneg _) hx1
      _ ≤ 4 * Real.exp t ^ 3 := primeRamp_abs_le hx
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  · simp [normalizedRamp, hx, Real.exp_nonneg]

theorem sample_eq_exp {Y : ℝ} (hY : 0 < Y) (u : ℝ) :
    sample Y u = Real.exp (5 / 4 * Real.log Y - u) := by
  rw [sample, Real.rpow_def_of_pos hY, ← Real.exp_add]
  congr 1
  ring

theorem outsideWindow_abs_ge {Y u : ℝ} (hY : 1 ≤ Y) (hu : u ∈ outsideWindow Y) :
    Real.log Y / 4 ≤ |u| := by
  have hy0 := zero_lt_one.trans_le hY
  by_contra! h
  have hins : Y ≤ sample Y u ∧ sample Y u ≤ Y ^ (3 / 2 : ℝ) := by
    rw [sample_eq_exp hy0, Real.rpow_def_of_pos hy0, ← Real.exp_log hy0]
    simp only [Real.log_exp]
    constructor
    · exact Real.exp_le_exp.mpr (by linarith [le_abs_self u])
    · exact Real.exp_le_exp.mpr (by linarith [neg_le_abs u])
  exact hu hins

/-- Every off-window contribution is bounded using one additional fixed
exponential tilt of the complete positive weight. -/
theorem thetaWindowTail_le {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ u, (outsideWindow Y).indicator
      (fun v => thetaWeight v * |normalizedRamp (sample Y v)|) u) ≤
      (4 * ∫ u : ℝ, Real.exp (19 * |u|) * thetaWeight u) *
        Real.exp (-Real.log Y / 4) := by
  let C := 4 * Real.exp (-Real.log Y / 4)
  have hi := integrable_exp_mul_thetaWeight 19
  have hnon (u : ℝ) :
      0 ≤ (outsideWindow Y).indicator (fun v => thetaWeight v * |normalizedRamp (sample Y v)|) u :=
    Set.indicator_nonneg (fun v _ => mul_nonneg (thetaWeight_pos v).le (abs_nonneg _)) _
  have h := integral_mono_of_nonneg (ae_of_all _ hnon) (hi.const_mul C)
    (ae_of_all _ (fun u => show (outsideWindow Y).indicator
      (fun v => thetaWeight v * |normalizedRamp (sample Y v)|) u ≤
      C * (Real.exp (19 * |u|) * thetaWeight u) from by
        by_cases hu : u ∈ outsideWindow Y
        · rw [Set.indicator_of_mem hu, sample_eq_exp (zero_lt_one.trans_le hY)]
          have habs := outsideWindow_abs_ge hY hu
          have he : 3 * (5 / 4 * Real.log Y - u) ≤ -Real.log Y / 4 + 19 * |u| := by
            linarith [neg_le_abs u]
          calc
            _ ≤ thetaWeight u * (4 * Real.exp (3 * (5 / 4 * Real.log Y - u))) :=
              mul_le_mul_of_nonneg_left (normalizedRamp_exp_abs_le _) (thetaWeight_pos _).le
            _ ≤ thetaWeight u * (4 * Real.exp (-Real.log Y / 4 + 19 * |u|)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by norm_num))
                (thetaWeight_pos _).le
            _ = _ := by rw [Real.exp_add]; dsimp only [C]; ring
        · rw [Set.indicator_of_notMem hu]
          exact mul_nonneg (by dsimp only [C]; positivity)
            (mul_nonneg (Real.exp_nonneg _) (thetaWeight_pos u).le)))
  rw [integral_const_mul] at h
  exact h.trans_eq (by dsimp only [C]; ring)

/-- The actual off-window term in the detector certificate is eventually at most one. -/
theorem eventually_thetaWindowTail_le_one : ∀ᶠ Y : ℝ in atTop,
    (∫ u, (outsideWindow Y).indicator
      (fun v => thetaWeight v * |normalizedRamp (sample Y v)|) u) ≤ 1 := by
  have hlog : Tendsto (fun Y : ℝ => -Real.log Y / 4) atTop atBot :=
    (tendsto_neg_atTop_atBot.comp Real.tendsto_log_atTop).atBot_div_const (by norm_num)
  have h := (Real.tendsto_exp_atBot.comp hlog).const_mul
    (4 * ∫ u : ℝ, Real.exp (19 * |u|) * thetaWeight u)
  have ht : Tendsto (fun Y : ℝ => (4 * ∫ u : ℝ, Real.exp (19 * |u|) * thetaWeight u) *
        Real.exp (-Real.log Y / 4)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using h
  have hlim : ∀ᶠ Y : ℝ in atTop,
      (4 * ∫ u : ℝ, Real.exp (19 * |u|) * thetaWeight u) *
        Real.exp (-Real.log Y / 4) < 1 := by
    exact ht.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlim] with Y hy hY
  exact (thetaWindowTail_le hy).trans hY.le

#print axioms eventually_thetaWindowTail_le_one

end
end RH01
