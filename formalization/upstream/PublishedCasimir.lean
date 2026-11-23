import PublishedWindows
import PublishedMellin
import RH01.PublicationAudit

/-! The conductor-one arithmetic bound followed by the local Casimir–theta detector. -/

namespace RH01

/-- The Casimir–theta proof using the published conductor-one window estimate. -/
theorem casimirRiemannHypothesis : _root_.RiemannHypothesis :=
  riemannHypothesis_of_publishedMellin publishedPrimeWindowBound

#print axioms casimirRiemannHypothesis

set_option maxHeartbeats 0 in
run_cmd do
  PublicationAudit.checkStandardAxioms `RH01.casimirRiemannHypothesis
  PublicationAudit.checkDependencies `RH01.casimirRiemannHypothesis
    [`RH01.publishedPrimeWindowBound, `RH01.primeWindowBound_of_published_families,
      `RH01.riemannHypothesis_of_publishedMellin,
      `RH01.thetaCertificate_of_rampMellin, `RH01.primeRamp_mellin,
      `UpperTheory.One.vwin_of_row, `UpperTheory.Comparison₂.level_gm_le_on_family_scales]
    [`riemannHypothesis, `UpperTheory.Comparison₂.formB, `UpperTheory.FinalTheorems.everyCharacter,
      `UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin,
      `UpperTheory.Lit.every_character_of_theta_integrals_local_matching,
      `UpperTheory.Top.zero_free_all_of_green_v_win, `UpperTheory.Top.zeroFreeAll_of_topG]

end RH01
