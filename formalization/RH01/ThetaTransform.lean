import RH01.ThetaMoments
import RH01.ProbeDivision
import RH01.Casimir
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Transform of the explicit theta weight

Jacobi inversion identifies the regular completed zeta integral with the
folded zeroth moment. Twice integrating the explicit differential kernel
retains the boundary contribution 1/2.
-/

namespace RH01

open Complex MeasureTheory Set Filter HurwitzZeta
open scoped Topology

noncomputable section

/-- The entire completion of ξ. At the two removable points it has value 1/2. -/
def completedXi (w : ℂ) : ℂ := (w * (w - 1) * completedRiemannZeta₀ w + 1) / 2

theorem completedXi_eq_xi {w : ℂ} (hre : 0 < w.re) (h₁ : w ≠ 1) :
    completedXi w = xi w := by
  have h₀ : w ≠ 0 := fun h => by simp [h] at hre
  rw [completedXi, xi, riemannZeta_def_of_ne_zero h₀, completedRiemannZeta_eq]
  field_simp [h₀, sub_ne_zero.mpr h₁, sub_ne_zero.mpr h₁.symm, Gammaℝ_ne_zero_of_re_pos hre]
  ring

private def pairedExp (s : ℂ) (u : ℝ) : ℂ := Complex.exp (-s * u) + Complex.exp (s * u)

private def pairedExp' (s : ℂ) (u : ℝ) : ℂ := s * (Complex.exp (s * u) - Complex.exp (-s * u))

private theorem hasDerivAt_exp_linear (s : ℂ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.exp (s * v)) (Complex.exp (s * u) * s) u := by
  simpa only [id_eq, mul_one] using (((hasDerivAt_id (u : ℂ)).const_mul s).cexp).comp_ofReal

private theorem pairedExp_deriv (s : ℂ) (u : ℝ) :
    HasDerivAt (pairedExp s) (pairedExp' s u) u := by
  have h := (hasDerivAt_exp_linear (-s) u).add (hasDerivAt_exp_linear s u)
  have he : Complex.exp (-s * u) * -s + Complex.exp (s * u) * s = pairedExp' s u := by
    unfold pairedExp'
    ring
  exact he ▸ h

private theorem pairedExp'_deriv (s : ℂ) (u : ℝ) :
    HasDerivAt (pairedExp' s) (s ^ 2 * pairedExp s u) u := by
  have h := ((hasDerivAt_exp_linear s u).sub (hasDerivAt_exp_linear (-s) u)).const_mul s
  have he : s * (Complex.exp (s * u) * s - Complex.exp (-s * u) * -s) = s ^ 2 * pairedExp s u := by
    unfold pairedExp
    ring
  exact he ▸ h

private theorem fold_bilateral {g : ℝ → ℂ} (he : Function.Even g) (s : ℂ)
    (h₁ : Integrable (fun u : ℝ => Complex.exp (-s * u) * g u))
    (h₂ : Integrable (fun u : ℝ => Complex.exp (s * u) * g u)) :
    bilateralLaplace g s = ∫ u in Ioi (0 : ℝ), pairedExp s u * g u := by
  have h := integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) h₁
  simp only [compl_Ioi] at h
  rw [bilateralLaplace, ← h, ← show
      (∫ x : ℝ in Ioi (0 : ℝ), (fun u : ℝ => Complex.exp (-s * u) * g u) (-x)) =
        ∫ x in Iic (0 : ℝ), Complex.exp (-s * x) * g x by
    simpa only [neg_zero] using (integral_comp_neg_Ioi 0 (fun u : ℝ => Complex.exp (-s * u) * g u))]
  have heq (u : ℝ) : Complex.exp (-s * (-u : ℝ)) * g (-u) = Complex.exp (s * u) * g u := by
    rw [he u, ofReal_neg, mul_neg, neg_mul, neg_neg]
  simp_rw [heq]
  simp only [pairedExp, add_mul, integral_add h₁.integrableOn h₂.integrableOn]

private theorem integrableOn_tilt_gaussianMoment {k : ℕ} (hk : k ≤ 2) (s : ℂ) :
    IntegrableOn (fun u : ℝ => Complex.exp (s * u) * (gaussianMoment k u : ℂ)) (Ioi 0) := by
  have hi := thetaTilt_integrable_of_bound (g := fun u => (gaussianMoment k |u| : ℂ))
    (continuous_ofReal.comp ((continuous_gaussianMoment k).comp continuous_abs)).measurable
    zero_le_one (fun u => by
      rw [norm_real, Real.norm_of_nonneg (gaussianMoment_nonneg _ _), one_mul]
      exact gaussianMoment_abs_le_thetaWeight hk u) s
  exact hi.integrableOn.congr_fun (fun u hu => by
    dsimp only
    rw [abs_of_pos (mem_Ioi.mp hu)]) measurableSet_Ioi

private theorem pairedExp_gaussianMoment_integrable {k : ℕ} (hk : k ≤ 2) (s : ℂ) :
    IntegrableOn (fun u : ℝ => pairedExp s u * (gaussianMoment k u : ℂ)) (Ioi 0) := by
  have hi := (integrableOn_tilt_gaussianMoment hk (-s)).add (integrableOn_tilt_gaussianMoment hk s)
  refine hi.congr_fun (fun u _ => ?_) measurableSet_Ioi
  exact (add_mul _ _ _).symm

private theorem thetaLaplace_eq_pairedMoment (s : ℂ) :
    bilateralLaplace (fun u => (thetaWeight u : ℂ)) s =
      (s ^ 2 - 1 / 4) * (∫ u in Ioi (0 : ℝ), pairedExp s u * (gaussianMoment 0 u : ℂ)) + 1 / 2 := by
  let H := fun u : ℝ => (gaussianMoment 0 u : ℂ)
  let H' := fun u : ℝ => (gaussianMomentSlope u : ℂ)
  let θ := fun u : ℝ => (thetaWeight u : ℂ)
  have hθ (z : ℂ) : Integrable (fun u : ℝ => Complex.exp (z * u) * θ u) :=
    thetaTilt_integrable_of_bound (continuous_ofReal.comp continuous_thetaWeight).measurable
      zero_le_one (fun u => by
        change ‖(thetaWeight u : ℂ)‖ ≤ _
        rw [norm_real, Real.norm_of_nonneg (thetaWeight_pos u).le, one_mul]) z
  rw [fold_bilateral (g := θ) (fun u => congrArg ofReal (thetaWeight_even u)) s (hθ (-s)) (hθ s)]
  let Q := fun u : ℝ => pairedExp s u * H' u - pairedExp' s u * H u
  let dQ := fun u : ℝ => pairedExp s u * θ u - (s ^ 2 - 1 / 4) * (pairedExp s u * H u)
  have hd (u : ℝ) (hu : 0 ≤ u) : HasDerivAt Q (dQ u) u := by
    have hp := (pairedExp_deriv s u).fun_mul (hasDerivAt_gaussianMomentSlope u hu |>.ofReal_comp)
    have hm := (pairedExp'_deriv s u).fun_mul (hasDerivAt_gaussianMoment_zero u |>.ofReal_comp)
    have he : pairedExp' s u * H' u + pairedExp s u * (↑(thetaWeight u + gaussianMoment 0 u / 4)) -
        (s ^ 2 * pairedExp s u * H u + pairedExp' s u * H' u) = dQ u := by
      dsimp only [dQ, H, θ]
      push_cast
      ring
    exact he ▸ hp.sub hm
  have hKi : IntegrableOn (fun u : ℝ => pairedExp s u * θ u) (Ioi 0) := by
    have hi := (hθ (-s)).integrableOn.add (hθ s).integrableOn (s := Ioi (0 : ℝ))
    refine hi.congr_fun (fun u _ => ?_) measurableSet_Ioi
    exact (add_mul _ _ _).symm
  have hM : IntegrableOn (fun u : ℝ => pairedExp s u * H u) (Ioi 0) :=
    pairedExp_gaussianMoment_integrable (by omega : (0 : ℕ) ≤ 2) s
  have hdi : IntegrableOn dQ (Ioi 0) := hKi.sub (hM.const_mul _)
  have hQ : IntegrableOn Q (Ioi 0) := by
    have h1 := pairedExp_gaussianMoment_integrable (by omega : (1 : ℕ) ≤ 2) s
    have he₁ : (fun u : ℝ => pairedExp s u * H' u) =
        fun u => (pairedExp s u * H u) / 2 - 2 * (pairedExp s u * ↑(gaussianMoment 1 u)) := by
      funext u
      dsimp only [H, H', gaussianMomentSlope]
      push_cast
      ring
    have he₂ : (fun u : ℝ => pairedExp' s u * H u) =
        fun u : ℝ => s * (Complex.exp (s * u) * H u - Complex.exp (-s * u) * H u) := by
      funext u
      unfold pairedExp'
      ring
    unfold Q
    apply IntegrableOn.sub
    · rw [he₁]
      exact (hM.div_const 2).sub (h1.const_mul 2)
    · rw [he₂]
      exact ((integrableOn_tilt_gaussianMoment (by omega : (0 : ℕ) ≤ 2) s).sub
        (integrableOn_tilt_gaussianMoment (by omega : (0 : ℕ) ≤ 2) (-s))).const_mul s
  have hlim : Tendsto Q atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (fun u hu => hd u hu.le) hdi hQ
  have hrec := integral_Ioi_of_hasDerivAt_of_tendsto' (fun u hu => hd u hu) hdi hlim
  have hQ₀ : Q 0 = -(1 / 2 : ℂ) := by
    simp [Q, H', pairedExp, pairedExp', gaussianMomentSlope_zero]
    ring
  rw [hQ₀, zero_sub, neg_neg] at hrec
  change (∫ u in Ioi (0 : ℝ), pairedExp s u * θ u -
    (s ^ 2 - 1 / 4) * (pairedExp s u * H u)) = _ at hrec
  rw [integral_sub hKi (hM.const_mul _), integral_const_mul] at hrec
  exact sub_eq_iff_eq_add.mp hrec |>.trans (add_comm _ _)

theorem mellin_log_change (f : ℝ → ℂ) (w : ℂ) :
    mellin f (w / 2) / 2 = ∫ u : ℝ, Complex.exp (w * u) * f (Real.exp (2 * u)) := by
  let h := fun u : ℝ => Real.exp (2 * u)
  have hI : h '' (univ : Set ℝ) = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨u, _, rfl⟩
      exact Real.exp_pos _
    · intro hx
      refine ⟨Real.log x / 2, mem_univ _, ?_⟩
      dsimp only [h]
      rw [show 2 * (Real.log x / 2) = Real.log x by ring, Real.exp_log hx]
  have hd (u : ℝ) : HasDerivAt h (2 * Real.exp (2 * u)) u := by
    simpa [h, id_eq, mul_comm] using
      (((hasDerivAt_id u).const_mul (2 : ℝ)).exp)
  have hj : Function.Injective h := fun a b hab => by
    have he := Real.exp_injective hab
    linarith
  have he : mellin f (w / 2) =
      ∫ u : ℝ, (2 : ℂ) * (Complex.exp (w * u) * f (Real.exp (2 * u))) := by
    rw [mellin, ← hI, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun u _ => (hd u).hasDerivWithinAt) hj.injOn, setIntegral_univ]
    apply integral_congr_ae (ae_of_all _ ?_)
    intro u
    dsimp only [h]
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * Real.exp (2 * u)), Complex.real_smul,
      smul_eq_mul, cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ← ofReal_log (Real.exp_nonneg _), Real.log_exp]
    push_cast
    have hexp : Complex.exp (2 * (u : ℂ)) *
        Complex.exp ((2 * (u : ℂ)) * (w / 2 - 1)) = Complex.exp (w * u) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [← hexp]
    ring
  rw [he, integral_const_mul]
  ring

private theorem thetaFEModif_log {u : ℝ} (hu : u ≠ 0) :
    (hurwitzEvenFEPair 0).f_modif (Real.exp (2 * u)) =
      2 * (Real.exp (-u / 2) : ℂ) * (gaussianMoment 0 |u| : ℂ) := by
  let x := Real.exp (2 * u)
  have hx : 0 < x := Real.exp_pos _
  rcases hu.lt_or_gt with hu | hu
  · have hx1 : x < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have ha : x ^ (-(1 / 2 : ℝ)) = Real.exp (-u) := by
      rw [Real.rpow_def_of_pos hx]
      dsimp only [x]
      rw [Real.log_exp]
      congr 1
      ring
    have hmod : evenKernel 0 x =
        Real.exp (-u) * evenKernel 0 (Real.exp (2 * -u)) := by
      simpa only [x, neg_neg] using evenKernel_exp_neg (-u)
    change (hurwitzEvenFEPair 0).f_modif x = _
    rw [WeakFEPair.f_modif, Pi.add_apply, indicator_of_notMem (notMem_Ioi.mpr hx1.le),
      zero_add, indicator_of_mem (mem_Ioo.mpr ⟨hx, hx1⟩), abs_of_neg hu,
      gaussianMoment_zero_eq_evenKernel]
    change (evenKernel 0 x : ℂ) - (1 * (x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (1 : ℂ) = _
    rw [ha, hmod]
    push_cast
    rw [smul_eq_mul]
    have he : Real.exp (-u / 2) * Real.exp (-u / 2) = Real.exp (-u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hec := congrArg ofReal he
    push_cast at hec
    linear_combination (-(evenKernel 0 (Real.exp (2 * -u)) : ℂ) + 1) * hec
  · have hx1 : 1 < x := Real.one_lt_exp_iff.mpr (by linarith)
    change (hurwitzEvenFEPair 0).f_modif x = _
    rw [WeakFEPair.f_modif, Pi.add_apply, indicator_of_mem (mem_Ioi.mpr hx1),
      indicator_of_notMem (show x ∉ Ioo (0 : ℝ) 1 from fun hx => (lt_asymm hx1 hx.2)),
      add_zero, abs_of_pos hu, gaussianMoment_zero_eq_evenKernel]
    change (evenKernel 0 x : ℂ) - (if (0 : UnitAddCircle) = 0 then 1 else 0) = _
    simp only [if_true]
    push_cast
    have he : Complex.exp (-(u : ℂ) / 2) * Complex.exp ((u : ℂ) / 2) = 1 := by
      rw [← Complex.exp_add, show -(u : ℂ) / 2 + (u : ℂ) / 2 = 0 by ring, Complex.exp_zero]
    have h : (evenKernel 0 x : ℂ) - 1 = 2 * Complex.exp (-(u : ℂ) / 2) *
        (Complex.exp ((u : ℂ) / 2) * ((evenKernel 0 x : ℂ) - 1) / 2) := by
      linear_combination (1 - (evenKernel 0 x : ℂ)) * he
    exact h

private theorem completedZeta_eq_foldedMoment (w : ℂ) :
    completedRiemannZeta₀ w =
      2 * ∫ u in Ioi (0 : ℝ), pairedExp (w - 1 / 2) u * (gaussianMoment 0 u : ℂ) := by
  let H := fun u : ℝ => (gaussianMoment 0 |u| : ℂ)
  let s := w - 1 / 2
  have hH (q : ℂ) : Integrable (fun u : ℝ => Complex.exp (q * u) * H u) :=
    thetaTilt_integrable_of_bound
      (continuous_ofReal.comp ((continuous_gaussianMoment 0).comp continuous_abs)).measurable
      zero_le_one (fun u => by
        change ‖(gaussianMoment 0 |u| : ℂ)‖ ≤ _
        rw [norm_real, Real.norm_of_nonneg (gaussianMoment_nonneg _ _), one_mul]
        exact gaussianMoment_abs_le_thetaWeight (by omega : (0 : ℕ) ≤ 2) u) q
  have he : completedRiemannZeta₀ w = 2 * bilateralLaplace H (-s) := by
    rw [completedRiemannZeta₀, completedHurwitzZetaEven₀, WeakFEPair.Λ₀, mellin_log_change,
      bilateralLaplace, ← integral_const_mul]
    have hzero : ∀ᵐ u : ℝ, u ≠ 0 := by
      rw [ae_iff]
      simp
    apply integral_congr_ae
    filter_upwards [hzero] with u hu
    rw [thetaFEModif_log hu, neg_neg, ofReal_exp]
    have hexp : Complex.exp (w * (u : ℂ)) * Complex.exp ↑(-u / 2) =
        Complex.exp (s * u) := by
      rw [← Complex.exp_add]
      push_cast
      dsimp only [s]
      congr 1
      ring
    rw [← hexp]
    ring
  rw [he, fold_bilateral (g := H) (fun u => by simp [H]) (-s)
    (by simpa only [neg_neg] using hH s) (hH (-s))]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only [pairedExp, H]
  rw [abs_of_pos (mem_Ioi.mp hu), neg_neg]
  change (Complex.exp (s * u) + Complex.exp (-s * u)) * (gaussianMoment 0 u : ℂ) =
    (Complex.exp (-s * u) + Complex.exp (s * u)) * (gaussianMoment 0 u : ℂ)
  rw [add_comm (Complex.exp (s * u))]

/-- The explicit positive theta series has bilateral transform equal to the
entire completed ξ with its critical shift. -/
theorem bilateralLaplace_thetaWeight_eq_completedXi (s : ℂ) :
    bilateralLaplace (fun u => (thetaWeight u : ℂ)) s = completedXi (s + 1 / 2) := by
  rw [thetaLaplace_eq_pairedMoment, completedXi, completedZeta_eq_foldedMoment]
  rw [show s + 1 / 2 - 1 / 2 = s by ring]
  ring

#print axioms bilateralLaplace_thetaWeight_eq_completedXi

end
end RH01
