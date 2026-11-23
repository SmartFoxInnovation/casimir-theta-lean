import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Ring

/-! The signed primitive used to divide the theta transform by s-a. -/

namespace RH01

open Complex MeasureTheory Set
open scoped Convolution

noncomputable section

def bilateralLaplace (g : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ u : ℝ, Complex.exp (-s * u) * g u

def probePrimitive (a : ℂ) (g : ℝ → ℂ) (u : ℝ) : ℂ :=
  Complex.exp (a * u) * ∫ v in Iic u, Complex.exp (-a * v) * g v

/-- Differentiating the actual primitive gives q' = a q + g. -/
theorem hasDerivAt_probePrimitive {a : ℂ} {g : ℝ → ℂ} (hg : Continuous g)
    (hi : Integrable (fun v : ℝ => Complex.exp (-a * v) * g v)) (u : ℝ) :
    HasDerivAt (probePrimitive a g) (a * probePrimitive a g u + g u) u := by
  let w := fun v : ℝ => Complex.exp (-a * v) * g v
  have hw : Continuous w := by dsimp only [w]; fun_prop
  have hsplit : (fun t : ℝ => ∫ v in Iic t, w v) =
      fun t : ℝ => (∫ v in Iic (0 : ℝ), w v) + ∫ v in (0 : ℝ)..t, w v := by
    funext t
    rw [← intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]
    abel
  have hInt : HasDerivAt (fun t : ℝ => ∫ v in Iic t, w v) (w u) u := by
    rw [hsplit]
    exact (intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable 0 u)
      hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt).const_add _
  have hE : HasDerivAt (fun v : ℝ => Complex.exp (a * v))
      (Complex.exp (a * u) * a) u := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id (u : ℂ)).const_mul a).cexp).comp_ofReal
  have hcancel : Complex.exp (a * u) * w u = g u := by
    dsimp only [w]
    rw [← mul_assoc, ← Complex.exp_add, show a * (u : ℂ) + -a * u = 0 by ring,
      Complex.exp_zero, one_mul]
  unfold probePrimitive
  have heq : Complex.exp (a * u) * a * (∫ v in Iic u, w v) + Complex.exp (a * u) * w u =
      a * (Complex.exp (a * u) * ∫ v in Iic u, w v) + g u := by rw [hcancel]; ring
  exact heq ▸ hE.fun_mul hInt

/-- A zero of the transform makes the left primitive equal to the negative
right primitive. This is the cancellation that lets each tail use its own
one-sided estimate. -/
theorem probePrimitive_eq_negative_right {a : ℂ} {g : ℝ → ℂ}
    (hi : Integrable (fun u : ℝ => Complex.exp (-a * u) * g u))
    (hz : bilateralLaplace g a = 0) (u : ℝ) :
    probePrimitive a g u = -Complex.exp (a * u) *
      ∫ v in Ioi u, Complex.exp (-a * v) * g v := by
  have h := integral_add_compl (measurableSet_Iic (a := u)) hi
  rw [compl_Iic] at h
  change _ + _ = bilateralLaplace g a at h
  rw [hz] at h
  have he := eq_neg_of_add_eq_zero_left h
  unfold probePrimitive
  rw [he, mul_neg, neg_mul]

/-- Once the primitive solves q' = a q + g and the two tilted functions
are integrable, integration by parts gives the exact transform division. -/
theorem bilateralLaplace_mul_sub {a s : ℂ} {q g : ℝ → ℂ}
    (hd : ∀ u, HasDerivAt q (a * q u + g u) u)
    (hq : Integrable (fun u : ℝ => Complex.exp (-s * u) * q u))
    (hg : Integrable (fun u : ℝ => Complex.exp (-s * u) * g u)) :
    (s - a) * bilateralLaplace q s = bilateralLaplace g s := by
  have hderiv (u : ℝ) :
      HasDerivAt (fun v : ℝ => Complex.exp (-s * v) * q v)
        (Complex.exp (-s * u) * g u - (s - a) * (Complex.exp (-s * u) * q u)) u := by
    have hexp : HasDerivAt (fun v : ℝ => Complex.exp (-s * v))
        (Complex.exp (-s * u) * (-s)) u := by
      simpa only [id_eq, mul_one] using
        (((hasDerivAt_id (u : ℂ)).const_mul (-s)).cexp).comp_ofReal
    have heq : Complex.exp (-s * u) * (-s) * q u + Complex.exp (-s * u) * (a * q u + g u) =
        Complex.exp (-s * u) * g u - (s - a) * (Complex.exp (-s * u) * q u) := by ring
    exact heq ▸ hexp.fun_mul (hd u)
  have hG :=
    integral_eq_zero_of_hasDerivAt_of_integrable hderiv (hg.sub (hq.const_mul (s - a))) hq
  rw [integral_sub hg (hq.const_mul (s - a)), integral_const_mul] at hG
  exact (sub_eq_zero.mp hG).symm

/-- The response of the full signed convolution is the product of the
transforms. No separation into positive and negative terms is needed. -/
theorem bilateralLaplace_convolution {q f : ℝ → ℂ} {s : ℂ}
    (hq : Integrable (fun u : ℝ => Complex.exp (-s * u) * q u))
    (hf : Integrable (fun u : ℝ => Complex.exp (-s * u) * f u)) :
    bilateralLaplace (fun x => ∫ u : ℝ, q u * f (x - u)) s =
      bilateralLaplace q s * bilateralLaplace f s := by
  let qₛ := fun u : ℝ => Complex.exp (-s * u) * q u
  let fₛ := fun u : ℝ => Complex.exp (-s * u) * f u
  let L := ContinuousLinearMap.mul ℂ ℂ
  have hpoint (x : ℝ) :
      Complex.exp (-s * x) * (∫ u : ℝ, q u * f (x - u)) = (qₛ ⋆[L] fₛ) x := by
    rw [← integral_const_mul, convolution_def]
    apply integral_congr_ae (ae_of_all _ ?_)
    intro u
    change Complex.exp (-s * x) * (q u * f (x - u)) =
      (Complex.exp (-s * u) * q u) * (Complex.exp (-s * (x - u : ℝ)) * f (x - u))
    rw [show -s * (x : ℂ) = -s * (u : ℂ) + -s * (x - u : ℝ) by push_cast; ring, Complex.exp_add]
    ring
  calc
    _ = ∫ x : ℝ, (qₛ ⋆[L] fₛ) x := by simp only [bilateralLaplace, hpoint]
    _ = _ := integral_convolution L hq hf

#print axioms probePrimitive_eq_negative_right
#print axioms hasDerivAt_probePrimitive
#print axioms bilateralLaplace_mul_sub
#print axioms bilateralLaplace_convolution

end
end RH01
