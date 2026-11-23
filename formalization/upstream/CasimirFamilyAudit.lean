import PublishedWindowArithmetic
import PublishedMellin
import RH01.PublicationAudit

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC UpperTheory.Comparison₂

namespace RH01

theorem casimir_of_conductor_one_family_windows
    (h : ChebyshevInequalityAtWindowScale (Fam := FamP) (fun Fm => Fm.toFamCore)
      (fun Fm => ChainTied Fm) (3 / 2) (Level.cyc PChar.one)) : _root_.RiemannHypothesis :=
  riemannHypothesis_of_publishedMellin (primeWindowBound_of_published_families h)

#print axioms casimir_of_conductor_one_family_windows

set_option maxHeartbeats 0 in
run_cmd do
  PublicationAudit.checkStandardAxioms `RH01.casimir_of_conductor_one_family_windows
  PublicationAudit.checkDependencies `RH01.casimir_of_conductor_one_family_windows
    [`RH01.primeWindowBound_of_published_families, `UpperTheory.Comparison₂.level_gm_le_on_family_scales,
     `RH01.thetaCertificate_of_rampMellin, `RH01.primeRamp_mellin]
    [`riemannHypothesis, `UpperTheory.Comparison₂.formB]

end RH01
