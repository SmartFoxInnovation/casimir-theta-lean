import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Casimir–theta prime-window argument

The arithmetic input is the conductor-one centered Mangoldt estimate on late
power windows. The analytic input is a positive theta weight, a small signed
average and a dominated probe that detects a right-half zero. The lemmas below
prove the one-sided comparison, the exponent contradiction and reflection.
-/

namespace RH01

open Filter MeasureTheory
open scoped BigOperators

noncomputable section

/-- The centered ramp, in the same normalization as the source's `An.G`. -/
def primeRamp (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    (ArithmeticFunction.vonMangoldt n : ℝ) * max (x / (n : ℝ) - 1) 0) -
    x * (Real.log x - 1 - Real.eulerMascheroniConstant)

/-- The one-sided conductor-one estimate needed from the arithmetic source. -/
def PrimeWindowBound : Prop :=
  ∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ, ∃ Y : ℝ, max 1 Y₀ ≤ Y ∧
    ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (3 / 2 : ℝ) → primeRamp x ≤ x ^ (1 / 2 + η)

/-- Extract the power-window input from family-scale estimates with arbitrarily
small positive exponent increments. The family and its cutoff may depend on ε. -/
theorem primeWindowBound_of_familyWindows {C ε₁ : ℝ} (hε₁ : 0 < ε₁)
    (hfamily : ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ (S : Set ℝ) (x₁ : ℝ),
      (∀ y : ℝ, ∃ Y : ℝ, y ≤ Y ∧
        ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (3 / 2 : ℝ) → x ∈ S) ∧
      (∀ x : ℝ, x₁ ≤ x → x ∈ S → primeRamp x ≤ x ^ (1 / 2 + C * ε))) :
    PrimeWindowBound := by
  intro η hη Y₀
  let ε := min (ε₁ / 2) (η / (|C| + 1))
  have hden : 0 < |C| + 1 := by positivity
  have hε : 0 < ε := lt_min (by linarith) (div_pos hη hden)
  have hsmall : ε < ε₁ := (min_le_left _ _).trans_lt (by linarith)
  have hC : C * ε ≤ η := calc
    C * ε ≤ (|C| + 1) * ε :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hε.le
    _ ≤ η := by
      have h := (le_div_iff₀ hden).mp (min_le_right (ε₁ / 2) (η / (|C| + 1)))
      simpa only [mul_comm] using h
  obtain ⟨S, x₁, hwindows, hestimate⟩ := hfamily ε hε hsmall
  obtain ⟨Y, hY, hmembers⟩ := hwindows (max (max 1 Y₀) x₁)
  have hbase := (le_max_left (max 1 Y₀) x₁).trans hY
  have hone := (le_max_left (1 : ℝ) Y₀).trans hbase
  have hcutoff := (le_max_right (max 1 Y₀) x₁).trans hY
  refine ⟨Y, hbase, fun x hx hupper => ?_⟩
  exact (hestimate x (hcutoff.trans hx) (hmembers x hx hupper)).trans
    (Real.rpow_le_rpow_of_exponent_le (hone.trans hx) (by linarith))

/-- The critically normalized ramp, extended by zero on x < 1. -/
def normalizedRamp (x : ℝ) : ℝ :=
  if 1 ≤ x then primeRamp x / x ^ (1 / 2 : ℝ) else 0

/-- The physical sample at log displacement u from the window center. -/
def sample (Y u : ℝ) : ℝ := Y ^ (5 / 4 : ℝ) * Real.exp (-u)

/-- The part of the positive weight lying outside the power window. -/
def outsideWindow (Y : ℝ) : Set ℝ :=
  {u | Y ≤ sample Y u ∧ sample Y u ≤ Y ^ (3 / 2 : ℝ)}ᶜ

/-- The meromorphic expression for the normalized ramp transform in w. -/
def rampTransform (w : ℂ) : ℂ :=
  (-deriv riemannZeta w / riemannZeta w) / (w * (w - 1)) -
    1 / (w - 1) ^ 2 + (1 + (Real.eulerMascheroniConstant : ℂ)) / (w - 1)

/-- Riemann's ξ with the exact archimedean factor. -/
def xi (w : ℂ) : ℂ := w * (w - 1) * Complex.Gammaℝ w * riemannZeta w / 2

/-- Multiplying the signed ramp transform by ξ cancels the zeta denominator
and keeps both continuum centering terms. This is the algebraic identity used
before shifting the signed theta convolution. -/
theorem xi_mul_rampTransform {w : ℂ} (h₀ : w ≠ 0) (h₁ : w ≠ 1)
    (hz : riemannZeta w ≠ 0) :
    xi w * rampTransform w = Complex.Gammaℝ w / 2 *
      (-deriv riemannZeta w + w * riemannZeta w *
        (1 + (Real.eulerMascheroniConstant : ℂ) - 1 / (w - 1))) := by
  unfold xi rampTransform
  field_simp [h₀, sub_ne_zero.mpr h₁, hz]
  ring

private theorem measurableSet_outsideWindow (Y : ℝ) : MeasurableSet (outsideWindow Y) := by
  have hs : Continuous (sample Y) :=
    continuous_const.mul (Real.continuous_exp.comp continuous_neg)
  exact ((measurableSet_le measurable_const hs.measurable).inter
    (measurableSet_le hs.measurable measurable_const)).compl

/-- The exact estimates needed from the positive theta kernel and divided
residue probe. The signed balance and tail can both be bounded by 1 after
increasing the cutoff. The probe may be complex and depend on the zero. -/
structure ThetaCertificate (b : ℝ) where
  weight : ℝ → ℝ
  probe : ℝ → ℂ
  domination : ℝ
  domination_nonneg : 0 ≤ domination
  weight_nonneg : ∀ u, 0 ≤ weight u
  weight_integrable : Integrable weight
  probe_dom : ∀ u, ‖probe u‖ ≤ domination * weight u
  cutoff : ℝ
  signed_integrable : ∀ Y ≥ max 1 cutoff,
    Integrable (fun u => weight u * normalizedRamp (sample Y u))
  probe_integrable : ∀ Y ≥ max 1 cutoff,
    Integrable (fun u => probe u * (normalizedRamp (sample Y u) : ℂ))
  signed_balance : ∀ Y ≥ max 1 cutoff,
    |∫ u, weight u * normalizedRamp (sample Y u)| ≤ 1
  tail_bound : ∀ Y ≥ max 1 cutoff,
    (∫ u, (outsideWindow Y).indicator
      (fun v => weight v * |normalizedRamp (sample Y v)|) u) ≤ 1
  residue : ℂ
  residue_ne_zero : residue ≠ 0
  frequency : ℝ
  residue_error : ∀ Y ≥ max 1 cutoff,
    ‖(∫ u, probe u * (normalizedRamp (sample Y u) : ℂ)) -
      residue * (Y ^ (5 * b / 4) : ℝ) *
        Complex.exp ((frequency * (5 / 4 * Real.log Y) : ℝ) * Complex.I)‖ ≤ 1

private theorem normalizedRamp_pos_le {b Y x : ℝ} (hb : 0 < b) (hY : 1 ≤ Y)
    (hx : Y ≤ x) (hx' : x ≤ Y ^ (3 / 2 : ℝ))
    (hramp : primeRamp x ≤ x ^ (1 / 2 + b / 2)) :
    max (normalizedRamp x) 0 ≤ Y ^ (3 * b / 4) := by
  have hx1 : 1 ≤ x := hY.trans hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hY0 : 0 ≤ Y := zero_le_one.trans hY
  apply max_le
  · calc
      normalizedRamp x = primeRamp x / x ^ (1 / 2 : ℝ) := if_pos hx1
      _ ≤ x ^ (1 / 2 + b / 2) / x ^ (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_right hramp (Real.rpow_nonneg hx0.le _)
      _ = x ^ (b / 2) := by rw [← Real.rpow_sub hx0]; congr 1; ring
      _ ≤ (Y ^ (3 / 2 : ℝ)) ^ (b / 2) :=
        Real.rpow_le_rpow hx0.le hx' (by positivity)
      _ = Y ^ (3 * b / 4) := by rw [← Real.rpow_mul hY0]; congr 1; ring
  · exact Real.rpow_nonneg hY0 _

private theorem ThetaCertificate.probe_upper {b : ℝ} (t : ThetaCertificate b)
    (hb : 0 < b) {Y : ℝ} (hY : max 1 t.cutoff ≤ Y)
    (hwindow : ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (3 / 2 : ℝ) →
      primeRamp x ≤ x ^ (1 / 2 + b / 2)) :
    ‖∫ u, t.probe u * (normalizedRamp (sample Y u) : ℂ)‖ ≤
      t.domination * (2 * (∫ u, t.weight u) + 3) * Y ^ (3 * b / 4) := by
  let A := Y ^ (3 * b / 4)
  let signed : ℝ → ℝ := fun u => t.weight u * normalizedRamp (sample Y u)
  let tail := (outsideWindow Y).indicator (fun u => |signed u|)
  let pos : ℝ → ℝ := fun u => max (signed u) 0
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hA : 1 ≤ A := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le hY1 (show (0 : ℝ) ≤ 3 * b / 4 by positivity))
  have hsigned : Integrable signed := t.signed_integrable Y hY
  have hpos_eq (u : ℝ) : pos u = t.weight u * max (normalizedRamp (sample Y u)) 0 := by
    simp only [pos, signed, mul_max_of_nonneg _ _ (t.weight_nonneg u), mul_zero]
  have habs_eq (u : ℝ) : |signed u| = t.weight u * |normalizedRamp (sample Y u)| := by
    dsimp only [signed]
    rw [abs_mul, abs_of_nonneg (t.weight_nonneg u)]
  have hpos : Integrable pos := hsigned.sup (integrable_zero ℝ ℝ volume)
  have htail : Integrable tail := hsigned.abs.indicator (measurableSet_outsideWindow Y)
  have htail_le : (∫ u, tail u) ≤ 1 := by
    simpa only [tail, habs_eq] using t.tail_bound Y hY
  have hpos_le : (∫ u, pos u) ≤ (∫ u, t.weight u) * A + 1 := by
    calc
      (∫ u, pos u) ≤ ∫ u, t.weight u * A + tail u := by
        apply integral_mono hpos ((t.weight_integrable.mul_const A).add htail)
        intro u
        change pos u ≤ t.weight u * A + tail u
        by_cases hu : u ∈ outsideWindow Y
        · have hn : 0 ≤ t.weight u * A := mul_nonneg (t.weight_nonneg u) (by linarith)
          have hp : pos u ≤ |signed u| := max_le (le_abs_self _) (abs_nonneg _)
          simp only [tail, Set.indicator_of_mem hu]
          linarith
        · have hinside : Y ≤ sample Y u ∧ sample Y u ≤ Y ^ (3 / 2 : ℝ) := by
            simpa [outsideWindow] using hu
          simp only [tail, Set.indicator_of_notMem hu, add_zero, hpos_eq]
          exact mul_le_mul_of_nonneg_left
            (normalizedRamp_pos_le hb hY1 hinside.1 hinside.2
              (hwindow _ hinside.1 hinside.2)) (t.weight_nonneg u)
      _ = (∫ u, t.weight u) * A + ∫ u, tail u := by
        rw [integral_add (t.weight_integrable.mul_const A) htail, integral_mul_const]
      _ ≤ _ := add_le_add_right htail_le _
  have habs : (∫ u, |signed u|) = 2 * (∫ u, pos u) - ∫ u, signed u := by
    have hpoint (u : ℝ) : |signed u| = 2 * pos u - signed u := by
      dsimp only [pos]
      by_cases h : 0 ≤ signed u
      · rw [abs_of_nonneg h, max_eq_left h]
        ring
      · have h' : signed u ≤ 0 := le_of_not_ge h
        rw [abs_of_nonpos h', max_eq_right h']
        ring
    simp_rw [hpoint]
    rw [integral_sub (hpos.const_mul 2) hsigned, integral_const_mul]
  have hbalance : -1 ≤ ∫ u, signed u := (abs_le.mp (t.signed_balance Y hY)).1
  have hmass : (∫ u, |signed u|) ≤ (2 * (∫ u, t.weight u) + 3) * A := by
    rw [habs]
    nlinarith
  have hprobe := t.probe_integrable Y hY
  calc
    ‖∫ u, t.probe u * (normalizedRamp (sample Y u) : ℂ)‖ ≤
        ∫ u, ‖t.probe u * (normalizedRamp (sample Y u) : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u, t.domination * |signed u| := by
      apply integral_mono hprobe.norm (hsigned.abs.const_mul t.domination)
      intro u
      change ‖t.probe u * (normalizedRamp (sample Y u) : ℂ)‖ ≤ t.domination * |signed u|
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, habs_eq, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (t.probe_dom u) (abs_nonneg _)
    _ = t.domination * (∫ u, |signed u|) := integral_const_mul _ _
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hmass t.domination_nonneg

/-- A right-half pole is incompatible with the centered prime-window bound.
The positive theta mass grows at exponent 5b/4 while the window permits 3b/4. -/
theorem noThetaCertificate_of_primeWindowBound (hwin : PrimeWindowBound) {b : ℝ}
    (hb : 0 < b) (t : ThetaCertificate b) : False := by
  let K := t.domination * (2 * (∫ u, t.weight u) + 3) + 1
  have hresidue : 0 < ‖t.residue‖ := norm_pos_iff.mpr t.residue_ne_zero
  have hpow := tendsto_rpow_atTop (show 0 < b / 2 by positivity)
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.1
    (hpow.eventually_gt_atTop (K / ‖t.residue‖))
  obtain ⟨Y, hY, hwindow⟩ := hwin (b / 2) (by positivity) (max Y₀ t.cutoff)
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYc : t.cutoff ≤ Y :=
    (le_max_right Y₀ t.cutoff).trans ((le_max_right _ _).trans hY)
  have hY0 : 0 < Y := zero_lt_one.trans_le hY1
  have hlarge : K / ‖t.residue‖ < Y ^ (b / 2) :=
    hY₀ Y ((le_max_left Y₀ t.cutoff).trans ((le_max_right _ _).trans hY))
  have hlower : K < ‖t.residue‖ * Y ^ (b / 2) := by
    simpa only [mul_comm] using (div_lt_iff₀ hresidue).mp hlarge
  have hpower : Y ^ (5 * b / 4) = Y ^ (b / 2) * Y ^ (3 * b / 4) := by
    rw [← Real.rpow_add hY0]
    congr 1
    ring
  let V : ℂ := ∫ u, t.probe u * (normalizedRamp (sample Y u) : ℂ)
  let poleTerm : ℂ := t.residue * (Y ^ (5 * b / 4) : ℝ) *
    Complex.exp ((t.frequency * (5 / 4 * Real.log Y) : ℝ) * Complex.I)
  have hpole : ‖poleTerm‖ = ‖t.residue‖ * Y ^ (5 * b / 4) := by
    simp [poleTerm, Complex.norm_exp, Complex.mul_re, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hY0.le _)]
  have htriangle : ‖t.residue‖ * Y ^ (5 * b / 4) ≤ ‖V‖ + 1 := by
    rw [← hpole]
    have herror : ‖V - poleTerm‖ ≤ 1 := t.residue_error Y (max_le hY1 hYc)
    have h := norm_sub_le V (V - poleTerm)
    rw [sub_sub_cancel] at h
    exact h.trans (add_le_add_right herror _)
  have hA : 1 ≤ Y ^ (3 * b / 4) := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le hY1 (show (0 : ℝ) ≤ 3 * b / 4 by positivity))
  have hupper : ‖t.residue‖ * Y ^ (5 * b / 4) ≤ K * Y ^ (3 * b / 4) := calc
    _ ≤ ‖V‖ + 1 := htriangle
    _ ≤ t.domination * (2 * (∫ u, t.weight u) + 3) * Y ^ (3 * b / 4) + 1 :=
      add_le_add_left (t.probe_upper hb (max_le hY1 hYc) hwindow) _
    _ ≤ _ := by
      dsimp [K]
      rw [add_mul, one_mul]
      exact add_le_add_right hA _
  rw [hpower, ← mul_assoc] at hupper
  exact (not_lt_of_ge hupper)
    (mul_lt_mul_of_pos_right hlower (Real.rpow_pos_of_pos hY0 _))

/-- The completed-zeta functional equation reflects any nontrivial left-half
zero to a right-half zero. -/
theorem riemannHypothesis_of_no_right_zero
    (hright : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    RiemannHypothesis := by
  intro s hz htrivial hone
  apply le_antisymm
  · exact le_of_not_gt (fun h => hright s h hone hz)
  · by_contra! hleft
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [riemannZeta_zero] at hz
      norm_num at hz
    have hGamma : Complex.Gammaℝ s ≠ 0 := by
      intro hzero
      obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hzero
      cases n with
      | zero => exact hs0 (by simpa using hn)
      | succ n =>
        apply htrivial
        refine ⟨n, ?_⟩
        push_cast at hn
        linear_combination hn
    have hcompleted : completedRiemannZeta s = 0 := by
      rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hz
      exact hz.resolve_right hGamma
    have hreflect : 1 / 2 < (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hreflect0 : 1 - s ≠ 0 := sub_ne_zero.mpr hone.symm
    have hreflect1 : 1 - s ≠ 1 := by simpa using hs0
    apply hright (1 - s) hreflect hreflect1
    rw [riemannZeta_def_of_ne_zero hreflect0, completedRiemannZeta_one_sub, hcompleted,
      zero_div]

/-- The RH01 bridge to Mathlib's exact statement of RH. The two premises are
the source arithmetic estimate and the analytic theta-probe construction. -/
theorem riemannHypothesis_of_casimir_theta (hwin : PrimeWindowBound)
    (htheta : ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ ≠ 1 → riemannZeta ρ = 0 →
      Nonempty (ThetaCertificate (ρ.re - 1 / 2))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_no_right_zero
  intro ρ hre hone hz
  obtain ⟨t⟩ := htheta ρ hre hone hz
  exact noThetaCertificate_of_primeWindowBound hwin (sub_pos.mpr hre) t

#print axioms primeWindowBound_of_familyWindows
#print axioms riemannHypothesis_of_casimir_theta

end

end RH01
