import RH01.ThetaWeight
import RH01.ProbeDivision

/-!
# A theta comparison uniform over all primitive divisions

The entire positive series is comparable with the first Gaussian term.
This exact scale is needed before taking ratios of nearby tails.
-/

namespace RH01

open Complex MeasureTheory Set

noncomputable section

def thetaFirstEnvelope (u : ℝ) : ℝ :=
  Real.exp (|u| / 2) * thetaScale u ^ 2 * Real.exp (-thetaScale u)

private def thetaComparison : ℝ := 8 * Real.exp 1 * ∑' n : ℕ, Real.exp (-(n : ℝ))

private theorem summable_exp_neg_nat : Summable (fun n : ℕ => Real.exp (-(n : ℝ))) := by
  refine (summable_geometric_of_lt_one (Real.exp_nonneg (-1 : ℝ))
    (Real.exp_lt_one_iff.mpr (by norm_num))).congr fun n => ?_
  rw [← Real.exp_nat_mul, mul_neg_one]

private theorem thetaComparison_pos : 0 < thetaComparison := by
  have hs := summable_exp_neg_nat.tsum_pos (fun n => Real.exp_nonneg _) 0 (Real.exp_pos _)
  unfold thetaComparison
  positivity

theorem thetaFirstEnvelope_le (u : ℝ) : thetaFirstEnvelope u ≤ thetaWeight u := by
  have ha := thetaScale_ge u
  have hpoly : thetaScale u ^ 2 ≤ 4 * thetaScale u ^ 2 - 6 * thetaScale u := by
    nlinarith only [mul_nonneg (by linarith : 0 ≤ thetaScale u) (by linarith : 0 ≤ thetaScale u - 2)]
  have h0 : thetaArgument 0 u = thetaScale u := by simp [thetaArgument]
  have hfirst : thetaFirstEnvelope u ≤ thetaTerm 0 u := by
    unfold thetaFirstEnvelope thetaTerm
    dsimp only
    rw [h0]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpoly (Real.exp_nonneg _)) (Real.exp_nonneg _)
  have hs := (summable_thetaTerm u).sum_le_tsum {0}
    (fun n _ => (thetaTerm_pos n u).le)
  exact hfirst.trans (by simpa [thetaWeight] using hs)

private theorem thetaWeight_le_firstEnvelope (u : ℝ) :
    thetaWeight u ≤ thetaComparison * thetaFirstEnvelope u := by
  let A := thetaScale u
  have hA : 3 ≤ A := thetaScale_ge u
  have hterm (n : ℕ) : thetaTerm n u ≤
      (8 * Real.exp 1 * thetaFirstEnvelope u) * Real.exp (-(n : ℝ)) := by
    let p : ℝ := ((n : ℝ) + 1) ^ 2
    let d := p - 1
    have hn : (n : ℝ) ≤ d := by
      dsimp only [d, p]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hd : 0 ≤ d := (Nat.cast_nonneg n).trans hn
    have hp : 0 ≤ p := sq_nonneg _
    have ha : thetaArgument n u = A * p := rfl
    have hpoly := Real.pow_div_factorial_le_exp (x := p) hp 2
    norm_num [Nat.factorial_succ] at hpoly
    have he : Real.exp (-(A * p)) = Real.exp (-A) * Real.exp (-(A * d)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [d]
      ring
    have he' : p + -(A * d) ≤ 1 + -(n : ℝ) := by
      have hmul := mul_nonneg (sub_nonneg.mpr hA) hd
      dsimp only [d] at *
      linarith
    calc
      thetaTerm n u ≤ Real.exp (|u| / 2) * (4 * (A * p) ^ 2) * Real.exp (-(A * p)) := by
        unfold thetaTerm
        dsimp only
        rw [ha]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (by nlinarith only [mul_nonneg (by linarith : 0 ≤ A) hp]) (Real.exp_nonneg _)) (Real.exp_nonneg _)
      _ = thetaFirstEnvelope u * (4 * p ^ 2 * Real.exp (-(A * d))) := by
        rw [he]
        unfold thetaFirstEnvelope
        change _ = Real.exp (|u| / 2) * A ^ 2 * Real.exp (-A) * _
        ring
      _ ≤ thetaFirstEnvelope u * (8 * Real.exp p * Real.exp (-(A * d))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith only [hpoly])
          (Real.exp_nonneg _)) (by unfold thetaFirstEnvelope; positivity)
      _ ≤ _ := by
        calc
          _ = (8 * thetaFirstEnvelope u) * Real.exp (p + -(A * d)) := by rw [Real.exp_add]; ring
          _ ≤ (8 * thetaFirstEnvelope u) * Real.exp (1 + -(n : ℝ)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he') (by unfold thetaFirstEnvelope; positivity)
          _ = _ := by rw [Real.exp_add]; ring
  have h := (summable_thetaTerm u).tsum_le_tsum hterm (summable_exp_neg_nat.mul_left _)
  rw [tsum_mul_left] at h
  unfold thetaWeight thetaComparison
  exact h.trans_eq (by ring)

private theorem thetaFirstEnvelope_step {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    thetaFirstEnvelope v = thetaFirstEnvelope u *
      Real.exp (9 / 2 * (v - u) - (thetaScale v - thetaScale u)) := by
  have hv := hu.trans huv
  have h₁ : Real.exp (v / 2) = Real.exp (u / 2) * Real.exp ((v - u) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h₂ : thetaScale v = thetaScale u * Real.exp (2 * (v - u)) := by
    unfold thetaScale
    rw [abs_of_nonneg hu, abs_of_nonneg hv, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have h₃ : Real.exp (-thetaScale v) =
      Real.exp (-thetaScale u) * Real.exp (-(thetaScale v - thetaScale u)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h₄ : Real.exp ((v - u) / 2) * Real.exp (2 * (v - u)) ^ 2 *
      Real.exp (-(thetaScale v - thetaScale u)) =
        Real.exp (9 / 2 * (v - u) - (thetaScale v - thetaScale u)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  unfold thetaFirstEnvelope
  rw [abs_of_nonneg hv, abs_of_nonneg hu, h₁, h₃, ← h₄]
  have hA₂ : thetaScale v ^ 2 = thetaScale u ^ 2 * Real.exp (2 * (v - u)) ^ 2 := by rw [h₂, mul_pow]
  rw [hA₂]
  ring

/-- On a distant right tail the comparison holds at any prescribed exponential
rate. The constant is uniform over the base point and the longer displacement. -/
theorem thetaWeight_tail_ratio {rate u v : ℝ} (hRate : 0 ≤ rate) (hu : rate + 5 ≤ u) (huv : u ≤ v) :
    thetaWeight v ≤ thetaComparison * thetaWeight u * Real.exp (-rate * (v - u)) := by
  have hu₀ : 0 ≤ u := by linarith
  have hv₀ := hu₀.trans huv
  have hA : thetaScale v = thetaScale u * Real.exp (2 * (v - u)) := by
    unfold thetaScale
    rw [abs_of_nonneg hu₀, abs_of_nonneg hv₀, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hA₀ : 0 ≤ thetaScale u := by unfold thetaScale; positivity
  have hdiff : 2 * thetaScale u * (v - u) ≤ thetaScale v - thetaScale u := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (2 * (v - u))) hA₀
    rw [hA]
    linarith only [h]
  have hrate : rate + 9 / 2 ≤ 2 * thetaScale u := by
    have h := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.exp_nonneg (2 * u))
    have h' := Real.add_one_le_exp (2 * u)
    unfold thetaScale
    rw [abs_of_nonneg hu₀]
    linarith
  have hE : 9 / 2 * (v - u) - (thetaScale v - thetaScale u) ≤ -rate * (v - u) := by
    linarith only [hdiff, mul_le_mul_of_nonneg_right hrate (sub_nonneg.mpr huv)]
  calc
    thetaWeight v ≤ thetaComparison * thetaFirstEnvelope v := thetaWeight_le_firstEnvelope v
    _ = thetaComparison * thetaFirstEnvelope u *
          Real.exp (9 / 2 * (v - u) - (thetaScale v - thetaScale u)) := by
      rw [thetaFirstEnvelope_step hu₀ huv, mul_assoc]
    _ ≤ _ := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (thetaFirstEnvelope_le u) thetaComparison_pos.le)
        (Real.exp_le_exp.mpr hE) (Real.exp_nonneg _)
        (mul_nonneg thetaComparison_pos.le (thetaWeight_pos u).le)

theorem norm_exp_mul_real (a : ℂ) (u : ℝ) :
    ‖Complex.exp (a * u)‖ = Real.exp (a.re * u) := by
  simp [Complex.norm_exp, Complex.mul_re]

private theorem right_probe_bound {a : ℂ} {g : ℝ → ℂ} {C : ℝ} (hg : Measurable g) (hC : 0 ≤ C)
    (hdom : ∀ v, ‖g v‖ ≤ C * thetaWeight v)
    {rate u : ℝ} (hRate : |a.re| + 1 ≤ rate) (hu : rate + 5 ≤ u) :
    ‖Complex.exp (a * u) * ∫ v in Ioi u, Complex.exp (-a * v) * g v‖ ≤
      (C * thetaComparison) * thetaWeight u := by
  let K := (C * thetaComparison) * thetaWeight u
  have hRate₀ : 0 ≤ rate := by linarith [abs_nonneg a.re]
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hC thetaComparison_pos.le) (thetaWeight_pos u).le
  have hi := thetaTilt_integrable_of_bound hg hC hdom (-a)
  have he (v : ℝ) : Real.exp (u - v) = Real.exp u * Real.exp (-v) := by
    rw [sub_eq_add_neg, Real.exp_add]
  have hmaj : IntegrableOn (fun v => K * Real.exp (u - v)) (Ioi u) := by
    simp_rw [he]
    exact ((integrableOn_exp_neg_Ioi u).const_mul _).const_mul _
  have hpoint (v : ℝ) (hv : v ∈ Ioi u) :
      Real.exp (a.re * u) * ‖Complex.exp (-a * v) * g v‖ ≤ K * Real.exp (u - v) := by
    have hv' : u ≤ v := hv.le
    have hΘ := thetaWeight_tail_ratio hRate₀ hu hv'
    have hE : a.re * u + (-a).re * v + -rate * (v - u) ≤ u - v := by
      rw [Complex.neg_re]
      have hrate : (1 : ℝ) ≤ a.re + rate := by linarith [neg_le_abs a.re]
      linarith only [mul_le_mul_of_nonneg_right hrate (sub_nonneg.mpr hv')]
    rw [norm_mul, norm_exp_mul_real]
    calc
      _ ≤ Real.exp (a.re * u) * (Real.exp ((-a).re * v) * (C * thetaWeight v)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hdom v) (Real.exp_nonneg _)) (Real.exp_nonneg _)
      _ ≤ Real.exp (a.re * u) * (Real.exp ((-a).re * v) *
          (C * (thetaComparison * thetaWeight u * Real.exp (-rate * (v - u))))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hΘ hC) (Real.exp_nonneg _)) (Real.exp_nonneg _)
      _ = K * Real.exp (a.re * u + (-a).re * v + -rate * (v - u)) := by
        rw [Real.exp_add, Real.exp_add]
        dsimp only [K]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE) hK
  calc
    _ = Real.exp (a.re * u) * ‖∫ v in Ioi u, Complex.exp (-a * v) * g v‖ := by
      rw [norm_mul, norm_exp_mul_real]
    _ ≤ Real.exp (a.re * u) * ∫ v in Ioi u, ‖Complex.exp (-a * v) * g v‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (Real.exp_nonneg _)
    _ = ∫ v in Ioi u, Real.exp (a.re * u) * ‖Complex.exp (-a * v) * g v‖ :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ v in Ioi u, K * Real.exp (u - v) :=
      setIntegral_mono_on ((hi.norm.const_mul _).integrableOn) hmaj measurableSet_Ioi hpoint
    _ = _ := by
      simp_rw [he]
      rw [integral_const_mul, integral_const_mul, integral_exp_neg_Ioi, ← Real.exp_add,
        add_neg_cancel, Real.exp_zero, mul_one]

private theorem thetaWeight_compact_lower {R u : ℝ} (hu : |u| ≤ R) :
    Real.exp (-(Real.pi * Real.exp (2 * R))) ≤ thetaWeight u := by
  have hr := Real.exp_le_exp.mpr (show 2 * |u| ≤ 2 * R by linarith)
  have hA : thetaScale u ≤ Real.pi * Real.exp (2 * R) :=
    mul_le_mul_of_nonneg_left hr Real.pi_pos.le
  have h1 : 1 ≤ Real.exp (|u| / 2) * thetaScale u ^ 2 := by
    have ht : (1 : ℝ) ≤ thetaScale u := by linarith [thetaScale_ge u]
    simpa only [one_mul] using mul_le_mul (Real.one_le_exp (by positivity : 0 ≤ |u| / 2))
      (one_le_pow₀ ht) (by norm_num : (0 : ℝ) ≤ 1) (Real.exp_nonneg _)
  apply le_trans _ (thetaFirstEnvelope_le u)
  unfold thetaFirstEnvelope
  exact (Real.exp_le_exp.mpr (neg_le_neg hA)).trans (le_mul_of_one_le_left (Real.exp_nonneg _) h1)

/-- The exact signed primitive preserves domination by the same theta weight.
The cancellation at a switches to the right integral on the positive tail. -/
theorem probePrimitive_dom_theta {a : ℂ} {g : ℝ → ℂ} {C : ℝ} (hg : Measurable g)
    (hC : 0 ≤ C) (hdom : ∀ u, ‖g u‖ ≤ C * thetaWeight u)
    (hz : bilateralLaplace g a = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u, ‖probePrimitive a g u‖ ≤ K * thetaWeight u := by
  let rate := |a.re| + 1
  let R := rate + 5
  let δ := Real.exp (-(Real.pi * Real.exp (2 * R)))
  let B := Real.exp (|a.re| * R) * ∫ v : ℝ, ‖Complex.exp (-a * v) * g v‖
  have hi := thetaTilt_integrable_of_bound hg hC hdom (-a)
  have hB : 0 ≤ B := mul_nonneg (Real.exp_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  have hδ : 0 < δ := Real.exp_pos _
  refine ⟨max (C * thetaComparison) (B / δ),
    le_max_of_le_left (mul_nonneg hC thetaComparison_pos.le), fun u => ?_⟩
  by_cases hright : R ≤ u
  · rw [probePrimitive_eq_negative_right hi hz, neg_mul, norm_neg]
    exact (right_probe_bound hg hC hdom (rate := rate) le_rfl hright).trans
      (mul_le_mul_of_nonneg_right (le_max_left ..) (thetaWeight_pos _).le)
  by_cases hleft : u ≤ -R
  · let g' := fun v : ℝ => g (-v)
    have hflip : (∫ v in Ioi (-u), Complex.exp (-(-a) * v) * g' v) =
        ∫ v in Iic u, Complex.exp (-a * v) * g v := by
      have h := integral_comp_neg_Ioi (-u) (fun v : ℝ => Complex.exp (-a * v) * g v)
      rw [neg_neg] at h
      rw [← h]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v _
      have hv : -(-a) * (v : ℂ) = -a * ((-v : ℝ) : ℂ) := by push_cast; ring
      change Complex.exp (-(-a) * v) * g (-v) = Complex.exp (-a * (-v : ℝ)) * g (-v)
      rw [hv]
    have he : Complex.exp (a * u) = Complex.exp ((-a) * (-u : ℝ)) := by
      congr 1
      push_cast
      ring
    have hdom' (v : ℝ) : ‖g' v‖ ≤ C * thetaWeight v := by
      simpa only [g', thetaWeight_even v] using hdom (-v)
    have hl := right_probe_bound (hg.comp measurable_neg) hC hdom' (a := -a)
      (rate := rate) (by simp [rate]) (u := -u) (by linarith)
    change ‖Complex.exp (-a * (-u : ℝ)) *
      (∫ v in Ioi (-u), Complex.exp (-(-a) * v) * g' v)‖ ≤
        C * thetaComparison * thetaWeight (-u) at hl
    rw [thetaWeight_even u, hflip, ← he] at hl
    exact hl.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (thetaWeight_pos _).le)
  have hsmall : |u| ≤ R := abs_le.mpr ⟨(le_of_not_ge hleft), (le_of_not_ge hright)⟩
  have hexp : Real.exp (a.re * u) ≤ Real.exp (|a.re| * R) := by
    apply Real.exp_le_exp.mpr
    have h := le_abs_self (a.re * u)
    rw [abs_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left hsmall (abs_nonneg _))
  have hcompact : ‖probePrimitive a g u‖ ≤ B := calc
    _ = Real.exp (a.re * u) * ‖∫ v in Iic u, Complex.exp (-a * v) * g v‖ := by
      rw [probePrimitive, norm_mul, norm_exp_mul_real]
    _ ≤ Real.exp (a.re * u) * ∫ v in Iic u, ‖Complex.exp (-a * v) * g v‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (Real.exp_nonneg _)
    _ ≤ B := mul_le_mul hexp (setIntegral_le_integral hi.norm (ae_of_all _ fun _ => norm_nonneg _))
      (integral_nonneg fun _ => norm_nonneg _) (Real.exp_nonneg _)
  calc
    _ ≤ B := hcompact
    _ = (B / δ) * δ := (div_mul_cancel₀ _ hδ.ne').symm
    _ ≤ (B / δ) * thetaWeight u :=
      mul_le_mul_of_nonneg_left (thetaWeight_compact_lower hsmall) (div_nonneg hB hδ.le)
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) (thetaWeight_pos _).le

#print axioms thetaWeight_tail_ratio
#print axioms probePrimitive_dom_theta

end
end RH01
