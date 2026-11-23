import RH01.SignedTransforms
import Mathlib.Analysis.Analytic.Order

/-!
# The divided signed probe at a zeta zero

At a zero of order k+1 the signed transform has order k. Thus division
by the full zero factor leaves one simple pole even at a multiple zero.
-/

namespace RH01

open Complex Filter Set
open scoped Topology

noncomputable section

local notation "γ" => (Real.eulerMascheroniConstant : ℂ)

theorem zeta_factor_at_zero {ρ : ℂ} (hρ : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    ∃ (k : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      riemannZeta =ᶠ[𝓝 ρ] fun w => (w - ρ) ^ (k + 1) * g w := by
  have h₁ : AnalyticOnNhd ℂ riemannZeta₁ univ := fun w _ =>
    differentiable_riemannZeta₁.analyticAt w
  have hfin : analyticOrderAt riemannZeta₁ ρ ≠ ⊤ := by
    intro ht
    have heq := h₁.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ ρ) (analyticOrderAt_eq_top.mp ht)
    have h := heq (mem_univ (1 : ℂ))
    simp at h
  obtain ⟨g, hg, hgn, hfact⟩ := ((h₁ ρ (mem_univ ρ)).analyticOrderAt_ne_top).mp hfin
  have hinv : AnalyticAt ℂ (fun w : ℂ => (w - 1)⁻¹) ρ :=
    (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hρ)
  let G := fun w => (w - 1)⁻¹ * g w
  have hG : AnalyticAt ℂ G ρ := hinv.mul hg
  have hGn : G ρ ≠ 0 := mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hρ)) hgn
  have hZ : riemannZeta =ᶠ[𝓝 ρ] fun w => (w - ρ) ^ analyticOrderNatAt riemannZeta₁ ρ * G w := by
    filter_upwards [hfact, compl_singleton_mem_nhds hρ] with w hw hne
    rw [riemannZeta_eq_inv_sub_mul hne, hw, smul_eq_mul]
    dsimp only [G]
    ring
  cases he : analyticOrderNatAt riemannZeta₁ ρ with
  | zero =>
    rw [he] at hZ
    exact (hGn (by simpa only [pow_zero, one_mul, hz] using hZ.self_of_nhds.symm)).elim
  | succ k =>
    exact ⟨k, G, hG, hGn, by simpa only [he] using hZ⟩

private theorem signedRamp_factor {ρ : ℂ} (hre : 0 < ρ.re) (hρ : ρ ≠ 1)
    {k : ℕ} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g ρ)
    (hfact : riemannZeta =ᶠ[𝓝 ρ] fun w => (w - ρ) ^ (k + 1) * g w) :
    ∃ V : ℂ → ℂ, AnalyticAt ℂ V ρ ∧
      V ρ = -(Gammaℝ ρ / 2) * ((k : ℂ) + 1) * g ρ ∧
      signedRamp =ᶠ[𝓝 ρ] fun w => (w - ρ) ^ k * V w := by
  let V := fun w : ℂ => Gammaℝ w / 2 *
    (-((k : ℂ) + 1) * g w - (w - ρ) * deriv g w +
      w * (w - ρ) * g w * (1 + γ - 1 / (w - 1)))
  have hΓ : AnalyticAt ℂ Gammaℝ ρ := by
    have hinv := differentiable_Gammaℝ_inv.analyticAt ρ
    have hinv' := hinv.inv (show (Gammaℝ ρ)⁻¹ ≠ 0 from inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hre))
    have heq : (fun w : ℂ => ((Gammaℝ w)⁻¹)⁻¹) = Gammaℝ := funext fun w => inv_inv _
    exact heq ▸ hinv'
  have hd := hg.deriv
  have hv : AnalyticAt ℂ V ρ := by
    unfold V
    fun_prop (disch := exact sub_ne_zero.mpr hρ)
  refine ⟨V, hv, ?_, ?_⟩
  · simp [V]
    ring
  · filter_upwards [hfact, hfact.deriv, hg.eventually_analyticAt, compl_singleton_mem_nhds hρ]
      with w hfw hdw hgw hw₁
    have hp : HasDerivAt (fun z : ℂ => (z - ρ) ^ (k + 1))
        (((k : ℂ) + 1) * (w - ρ) ^ k) w := by
      simpa using ((hasDerivAt_id w).sub_const ρ).fun_pow (k + 1)
    rw [signedRamp_eq_cancelled hw₁, hfw, hdw, (hp.fun_mul hgw.differentiableAt.hasDerivAt).deriv,
      pow_succ]
    dsimp only [V]
    ring

/-- The divided signed ramp has a holomorphic remainder on the right half-plane
and one nonzero residue. Its order is the actual order of the chosen zero. -/
theorem signedRamp_divided_pole_of_factor {ρ : ℂ} (hre : 0 < ρ.re) (hρ : ρ ≠ 1)
    {k : ℕ} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g ρ) (hgn : g ρ ≠ 0)
    (hfact : riemannZeta =ᶠ[𝓝 ρ] fun w => (w - ρ) ^ (k + 1) * g w) :
    ∃ (r : ℂ) (F : ℂ → ℂ), r ≠ 0 ∧
      DifferentiableOn ℂ F {w : ℂ | 0 < w.re} ∧
      ∀ w ≠ ρ, signedRamp w / (w - ρ) ^ (k + 1) = r / (w - ρ) + F w := by
  obtain ⟨V, hV, hr, hVeq⟩ := signedRamp_factor hre hρ hg hfact
  let F := Function.update
    (fun w : ℂ => signedRamp w / (w - ρ) ^ (k + 1) - V ρ / (w - ρ))
    ρ (deriv V ρ)
  have hrn : V ρ ≠ 0 := by
    rw [hr]
    refine mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr
      (div_ne_zero (Gammaℝ_ne_zero_of_re_pos hre) two_ne_zero)) ?_) hgn
    exact_mod_cast (Nat.succ_ne_zero k)
  refine ⟨V ρ, F, hrn, ?_, ?_⟩
  · intro w hw
    apply DifferentiableAt.differentiableWithinAt
    by_cases hwρ : w = ρ
    · subst w
      have hN : {z : ℂ | AnalyticAt ℂ V z} ∈ 𝓝 ρ := hV.eventually_analyticAt
      have hD : DifferentiableOn ℂ V {z : ℂ | AnalyticAt ℂ V z} :=
        fun z hz' => hz'.differentiableAt.differentiableWithinAt
      have hd := ((differentiableOn_dslope hN).2 hD).differentiableAt hN
      apply hd.congr_of_eventuallyEq
      filter_upwards [hVeq] with z hVw
      by_cases hzρ : z = ρ
      · subst z
        simp [F]
      · have hz' := sub_ne_zero.mpr hzρ
        dsimp only [F]
        rw [Function.update_of_ne hzρ, dslope_of_ne _ hzρ, slope_def_module,
          smul_eq_mul, hVw, pow_succ]
        field_simp [hz', pow_ne_zero k hz']
    · have hs := differentiableOn_signedRamp.differentiableAt
        ((isOpen_lt continuous_const continuous_re).mem_nhds hw)
      have hraw : DifferentiableAt ℂ
          (fun z : ℂ => signedRamp z / (z - ρ) ^ (k + 1) - V ρ / (z - ρ)) w := by
        fun_prop (disch := first | exact sub_ne_zero.mpr hwρ | exact pow_ne_zero _ (sub_ne_zero.mpr hwρ))
      apply hraw.congr_of_eventuallyEq
      filter_upwards [compl_singleton_mem_nhds hwρ] with z hz'
      dsimp only [F]
      rw [Function.update_of_ne hz']
  · intro w hw
    dsimp only [F]
    rw [Function.update_of_ne hw]
    ring

theorem signedRamp_divided_pole {ρ : ℂ} (hre : 0 < ρ.re) (hρ : ρ ≠ 1)
    (hz : riemannZeta ρ = 0) :
    ∃ (m : ℕ) (r : ℂ) (F : ℂ → ℂ), 0 < m ∧ r ≠ 0 ∧
      DifferentiableOn ℂ F {w : ℂ | 0 < w.re} ∧
      ∀ w ≠ ρ, signedRamp w / (w - ρ) ^ m = r / (w - ρ) + F w := by
  obtain ⟨k, g, hg, hgn, hfact⟩ := zeta_factor_at_zero hρ hz
  obtain ⟨r, F, hr, hF, he⟩ := signedRamp_divided_pole_of_factor hre hρ hg hgn hfact
  exact ⟨k + 1, r, F, Nat.succ_pos _, hr, hF, he⟩

#print axioms signedRamp_divided_pole

end
end RH01
