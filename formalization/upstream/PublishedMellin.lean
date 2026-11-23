import RH01.Detector
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.mellinGchiModOne

/-! The published Mellin formula evaluated at exactly RH01's centered ramp. -/

namespace RH01

open MeasureTheory Set

private theorem conductorOne_eq_ramp (y : ℝ) :
    Deduction.Gchi (1 : DirichletCharacter ℂ 1) y = (primeRamp y : ℂ) := by
  have hχ (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton _)
  have hsub : Finset.Icc 1 ⌊y⌋₊ ⊆ Finset.range (⌊y⌋₊ + 1) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_range]
    omega
  have hsum :
      (∑ n ∈ Finset.range (⌊y⌋₊ + 1),
        (ArithmeticFunction.vonMangoldt n : ℂ) * ((max (y / (n : ℝ) - 1) 0 : ℝ) : ℂ)) =
      (∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℂ) * ((max (y / (n : ℝ) - 1) 0 : ℝ) : ℂ)) := by
    symm
    apply Finset.sum_subset hsub
    intro n hn hnot
    rw [Finset.mem_range] at hn
    rw [Finset.mem_Icc] at hnot
    have hn0 : n = 0 := by omega
    simp [hn0]
  unfold Deduction.Gchi Deduction.ramp primeRamp
  simp only [hχ, mul_one, hsum]
  push_cast
  ring

/-- The exact centered Mellin transform on the initial line. -/
theorem primeRamp_mellin {s : ℂ} (hs : 1 < s.re) :
    (∫ y in Ioi (1 : ℝ), (primeRamp y : ℂ) * (y : ℂ) ^ (-s - 1)) = rampTransform s := by
  simp_rw [← conductorOne_eq_ramp]
  rw [Deduction.mellin_Gchi_modOne _ _ hs]
  have hs₀ : s ≠ 0 := fun h => by norm_num [h] at hs
  have hs₁ : s - 1 ≠ 0 := sub_ne_zero.mpr (fun h => by norm_num [h] at hs)
  unfold rampTransform
  field_simp [hs₀, hs₁, riemannZeta_ne_zero_of_one_lt_re hs]
  ring

#print axioms primeRamp_mellin

theorem rampMellinOn_four : RampMellinOn 4 := by
  intro t
  dsimp only
  apply primeRamp_mellin
  norm_num [Complex.add_re, Complex.mul_re]

theorem riemannHypothesis_of_publishedMellin (hwin : PrimeWindowBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_window_and_rampMellin hwin rampMellinOn_four

#print axioms riemannHypothesis_of_publishedMellin

end RH01
