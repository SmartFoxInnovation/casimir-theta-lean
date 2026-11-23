import RH01.Casimir
import Development.AutomorphicArithmetic.PrimitiveCosets.GzEq
import Development.AutomorphicArithmetic.PrimitiveCosets.LevelGmLeOnFamilyScales

/-! The conductor-one extraction from the published family-scale inequality. -/

namespace RH01

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC
open UpperTheory.Comparison₂

private theorem conductorOne_gm (x : ℝ) : (Level.cyc PChar.one).Gm x = primeRamp x := by
  classical
  have hkept : (Level.cyc PChar.one).KEPT = {PChar.one} := by
    ext ψ
    rw [Finset.mem_singleton]
    constructor
    · intro hψ
      obtain ⟨χ, _, hrep⟩ := (Level.mem_ofSub _ _).mp hψ
      have hχ1 : χ = 1 := DirichletCharacter.level_one χ
      rw [hχ1, PChar.of_one] at hrep
      exact hrep.symm
    · rintro rfl
      exact Level.mem_cyc PChar.one
  rw [Level.Gm, Level.Nt, hkept]
  simp only [Finset.erase_singleton, Finset.sum_empty, add_zero]
  exact (Gz_eq x).1.trans rfl

/-- Use the existing family-window estimate before the upstream zero-exclusion argument. -/
theorem primeWindowBound_of_published_families
    (h : ChebyshevInequalityAtWindowScale (Fam := FamP) (fun Fm => Fm.toFamCore)
      (fun Fm => ChainTied Fm) (3 / 2) (Level.cyc PChar.one)) : PrimeWindowBound := by
  obtain ⟨eD, eL, ε₁, hε₁, hfamily⟩ := h
  apply primeWindowBound_of_familyWindows (C := eD + eL + 7) hε₁
  intro ε hε0 hε
  obtain ⟨Fm, hc, hw, ht⟩ := hfamily ε hε0 hε
  obtain ⟨x₁, hx₁⟩ := level_gm_le_on_family_scales (Level.cyc PChar.one)
    eD eL ε hε0 Fm hc ht
  refine ⟨Fm.toFamCore.Win, x₁, (windows_iff Fm.toFamCore _).mp hw, ?_⟩
  intro x hx hmem
  rw [← conductorOne_gm]
  exact hx₁ x hx hmem

#print axioms primeWindowBound_of_published_families

end RH01
