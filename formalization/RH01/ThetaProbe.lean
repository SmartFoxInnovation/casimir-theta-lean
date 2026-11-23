import RH01.ThetaTransform
import RH01.ThetaDomination
import RH01.ProbeResidue

/-! Iterated signed division through the full local multiplicity of a zero. -/

namespace RH01

open Complex MeasureTheory Filter Set
open scoped Topology

noncomputable section

theorem continuous_bilateralLaplace_of_dom {g : ℝ → ℂ} {C : ℝ}
    (hg : Measurable g) (hdom : ∀ u, ‖g u‖ ≤ C * thetaWeight u) :
    Continuous (bilateralLaplace g) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  have hnear : ∀ᶠ z : ℂ in 𝓝 a, |z.re| < |a.re| + 1 :=
    (isOpen_lt continuous_re.abs continuous_const).mem_nhds (by simp)
  unfold bilateralLaplace
  refine continuousAt_of_dominated
    (Eventually.of_forall fun z => ((by fun_prop : Continuous
      (fun u : ℝ => Complex.exp (-z * u))).measurable.mul hg).aestronglyMeasurable)
    (hnear.mono fun z hz => ae_of_all _ fun u => ?_)
    ((integrable_exp_mul_thetaWeight (|a.re| + 1)).const_mul C)
    (ae_of_all _ fun u => by fun_prop)
  rw [norm_mul, norm_exp_mul_real, neg_re]
  have hb : -z.re * u ≤ (|a.re| + 1) * |u| := by
    calc
      _ ≤ |-z.re * u| := le_abs_self _
      _ = |z.re| * |u| := by rw [abs_mul, abs_neg]
      _ ≤ _ := mul_le_mul_of_nonneg_right hz.le (abs_nonneg _)
  exact (mul_le_mul (Real.exp_le_exp.mpr hb) (hdom u) (norm_nonneg _)
      (Real.exp_nonneg _)).trans_eq (by ring)

/-- The signed primitive can be iterated up to the order of the transform
zero. Each iteration keeps domination by the same full theta envelope. -/
theorem exists_divided_probe {a : ℂ} {m : ℕ} {g : ℝ → ℂ} {C : ℝ}
    (hg : Continuous g) (hC : 0 ≤ C) (hdom : ∀ u, ‖g u‖ ≤ C * thetaWeight u)
    {H : ℂ → ℂ} (hH : ContinuousAt H a)
    (hfactor : bilateralLaplace g =ᶠ[𝓝 a] fun w => (w - a) ^ m * H w) :
    ∃ (q : ℝ → ℂ) (C' : ℝ), Continuous q ∧ 0 ≤ C' ∧
      (∀ u, ‖q u‖ ≤ C' * thetaWeight u) ∧
      ∀ w : ℂ, (w - a) ^ m * bilateralLaplace q w = bilateralLaplace g w := by
  induction m generalizing g C with
  | zero => exact ⟨g, C, hg, hC, hdom, fun _ => by simp⟩
  | succ m ih =>
    have hz : bilateralLaplace g a = 0 := by simpa using hfactor.self_of_nhds
    let p := probePrimitive a g
    obtain ⟨E, hE, hdomp⟩ := probePrimitive_dom_theta hg.measurable hC hdom hz
    have hd := hasDerivAt_probePrimitive hg (thetaTilt_integrable_of_bound hg.measurable hC hdom (-a))
    have hp : Continuous p := continuous_iff_continuousAt.mpr fun u => (hd u).continuousAt
    have hdiv (w : ℂ) : (w - a) * bilateralLaplace p w = bilateralLaplace g w :=
      bilateralLaplace_mul_sub hd (thetaTilt_integrable_of_bound hp.measurable hE hdomp (-w))
        (thetaTilt_integrable_of_bound hg.measurable hC hdom (-w))
    have hevent : bilateralLaplace p =ᶠ[𝓝[≠] a] fun w => (w - a) ^ m * H w := by
      have hf : ∀ᶠ w in 𝓝[≠] a, bilateralLaplace g w = (w - a) ^ (m + 1) * H w :=
        hfactor.filter_mono nhdsWithin_le_nhds
      filter_upwards [hf, self_mem_nhdsWithin (s := {a}ᶜ)] with w hw hne
      apply mul_left_cancel₀ (sub_ne_zero.mpr (show w ≠ a from hne))
      rw [hdiv, hw, pow_succ]
      ring
    have hself : bilateralLaplace p a = (a - a) ^ m * H a :=
      tendsto_nhds_unique_of_eventuallyEq
        ((continuous_bilateralLaplace_of_dom hp.measurable hdomp).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds)
        ((((continuous_id.sub continuous_const).pow m).continuousAt.mul hH).tendsto.mono_left
          nhdsWithin_le_nhds) hevent
    have hfac : bilateralLaplace p =ᶠ[𝓝 a] fun w => (w - a) ^ m * H w := by
      change ∀ᶠ w in 𝓝[≠] a, bilateralLaplace p w = (w - a) ^ m * H w at hevent
      rw [eventually_nhdsWithin_iff] at hevent
      filter_upwards [hevent] with w hw
      by_cases hwa : w = a
      · simpa only [hwa] using hself
      · exact hw hwa
    obtain ⟨q, D, hq, hD, hdomq, hqfac⟩ := ih hp hE hdomp hfac
    refine ⟨q, D, hq, hD, hdomq, fun w => ?_⟩
    rw [pow_succ, mul_right_comm, mul_comm _ (w - a), hqfac, hdiv]

/-- The full even theta weight supplies a dominated detector at every
positive-real zero, using the multiplicity of the original zeta zero. -/
theorem exists_theta_probe {ρ : ℂ} (hre : 0 < ρ.re) (hρ : ρ ≠ 1)
    {k : ℕ} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g ρ)
    (hfact : riemannZeta =ᶠ[𝓝 ρ] fun w => (w - ρ) ^ (k + 1) * g w) :
    ∃ (q : ℝ → ℂ) (C : ℝ), Continuous q ∧ 0 ≤ C ∧
      (∀ u, ‖q u‖ ≤ C * thetaWeight u) ∧
      ∀ s : ℂ, (s - (ρ - 1 / 2)) ^ (k + 1) * bilateralLaplace q s =
        completedXi (s + 1 / 2) := by
  let a := ρ - (1 / 2 : ℂ)
  let H := fun w : ℂ => w * (w - 1) * Gammaℝ w * g w / 2
  have ha : a + (1 / 2 : ℂ) = ρ := by dsimp [a]; ring
  have hΓ₀ : (Gammaℝ ρ)⁻¹ ≠ 0 := inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hre)
  have hΓ := ((differentiable_Gammaℝ_inv ρ).inv hΓ₀).continuousAt
  have heΓ : (fun s => ((Gammaℝ s)⁻¹)⁻¹) = Gammaℝ := funext fun _ => inv_inv _
  have hΓ : ContinuousAt Gammaℝ ρ := heΓ ▸ hΓ
  have hH : ContinuousAt H ρ := by unfold H; fun_prop (disch := exact hg.continuousAt)
  have ht : Tendsto (fun s : ℂ => s + 1 / 2) (𝓝 a) (𝓝 ρ) := ha ▸
    ((continuous_id.add continuous_const).continuousAt : ContinuousAt (fun s : ℂ => s + 1 / 2) a)
  have hfac : bilateralLaplace (fun u => (thetaWeight u : ℂ)) =ᶠ[𝓝 a]
      fun s => (s - a) ^ (k + 1) * H (s + 1 / 2) := by
    have hre' := (isOpen_lt continuous_const continuous_re).mem_nhds hre
    filter_upwards [ht.eventually hfact, ht.eventually hre',
      ht.eventually (compl_singleton_mem_nhds hρ)] with s hs hsre hs₁
    rw [bilateralLaplace_thetaWeight_eq_completedXi, completedXi_eq_xi hsre hs₁, xi, hs]
    dsimp only [H, a]
    rw [show s + 1 / 2 - ρ = s - (ρ - 1 / 2) by ring]
    ring
  obtain ⟨q, C, hq, hC, hdom, hres⟩ :=
    exists_divided_probe (continuous_ofReal.comp continuous_thetaWeight) zero_le_one
      (fun u => by
        change ‖(thetaWeight u : ℂ)‖ ≤ _
        rw [norm_real, Real.norm_of_nonneg (thetaWeight_pos u).le, one_mul])
      (hH.comp_of_eq ((continuous_id.add continuous_const).continuousAt) ha) hfac
  exact ⟨q, C, hq, hC, hdom, fun s => (hres s).trans (bilateralLaplace_thetaWeight_eq_completedXi s)⟩

#print axioms exists_divided_probe
#print axioms exists_theta_probe

end
end RH01
