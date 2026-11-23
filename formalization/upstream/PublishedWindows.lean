import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin
import PublishedWindowArithmetic

/-!
# Source adapter for the conductor-one window estimate

This file targets the pinned Alpöge–Claude source. The only window estimates
used are the family witnesses and the estimate on each family's scales.
-/

namespace RH01

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX
open UpperTheory.Top UpperTheory.Comparison₂

/-- Supply the exact conductor-one family witnesses from the published construction. -/
theorem primeWindowBound_of_topG (h : TopG)
    (hs : HostExW (3 / 2) (GChi PChar.one).req) : PrimeWindowBound := by
  obtain ⟨eD, eL, ε₁, hε₁, hfamily⟩ :=
    h (3 / 2) (GChi PChar.one) (by norm_num) hs (hypV_of_cls PChar.one (3 / 2))
  apply primeWindowBound_of_published_families
  refine ⟨eD, eL, ε₁, hε₁, fun ε hε0 hε => ?_⟩
  obtain ⟨Fm, hc, ht⟩ := hfamily ε hε0 hε
  exact ⟨Fm, eFamC_of_cls PChar.one (3 / 2) Fm hc, hc.1, ht⟩

open GlobalTheory.Fc in
theorem primeWindowBound_of_green_v_win (hG : GlobalTheory.GLq.Green) (hV : VWin)
    (h : Nonempty (HypsAlt (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm)
      DefiniteSideCondition)) : PrimeWindowBound := by
  rcases h with ⟨hw⟩
  exact primeWindowBound_of_topG
    (forall_goal_of_shape_of_hyps _ _ _ _ (shape_closed_link_n_of_green hG) trivial trivial hw)
    (supplyChi PChar.one (hV PChar.one))

theorem primeWindowBound_of_theta_integrals_local_matching
    (P : GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses)
    (F : GlobalTheory.FunPr.ThetaLocalInputs)
    (hA : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    (hX : GlobalTheory.CovTop.CovolumeBoundOfX) (hL : UpperTheory.Zero.LLC.RecTExists)
    (hV : VWin) : PrimeWindowBound :=
  primeWindowBound_of_green_v_win (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters) hV
    (UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound P F hA hM hX hL
      fun cDep => UpperTheory.N.boundAtTwoThree_linked_of_recT P.nLink
        (GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep))

open UpperTheory.LiteratureTheorems in
/-- Arithmetic input extracted from the same row data as the published proof. -/
theorem publishedPrimeWindowBound : PrimeWindowBound := by
  let row := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  let data : OpenLiteratureStatements := ⟨row, UpperTheory.Zero.LLC.recTExists, row⟩
  let hΘ := theta_integrals_agree_and_local_matching_of_literature data
  have hX : GlobalTheory.CovTop.CovolumeBoundOfX :=
    SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt
      (resolution_char_zero_of_literature data) (principalisation_char_zero_of_literature data)
      (poincare_lelong_inv_of_literature data) PositivityTheory.Pf1.HilbertSamuelMoriwaki.hsUse_outright
      PositivityTheory.Pf1.HilbertSamuelMoriwaki.moriwakiBig_outright
      (fargues_exact_of_literature data) (zarhin_statement data) (nef_rr_of_literature data)
      (siegel_toroidal_integral_of_literature data) (toroidal_for_fan_ks_of_literature data)
      (semi_abelian_lie_seminegative_of_literature data) (point_separation_pair_of_literature data)
      (ar_degree_of_literature data) (published_results_arithmetic data)
      (grothendieck_deformation_of_literature data)
  exact primeWindowBound_of_theta_integrals_local_matching
    (published_results_eigen data) (published_results_first data) hΘ.1 hΘ.2 hX
    (local_langlands_gl_recT_exists_of_literature data) (UpperTheory.One.vwin_of_row row)

#print axioms publishedPrimeWindowBound

end RH01
