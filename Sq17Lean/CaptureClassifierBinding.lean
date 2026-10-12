import Sq17Lean.CaptureFamily
import Sq17Lean.RepresentativeCaseData

/-! Exact binding of compact full-roster index 204 (all_orbits case 1442)
to the family selected by the capture geometry bridge. -/
namespace Sq17.CaptureFamily

theorem full_204_roster : Sq17.RepresentativeCaseData.fullCases 204 = sourceRoster := by
  rfl

theorem roster_of_full_204_match (holes : List (Fin 24))
    (h : Sq17.RepresentativeCases.Matches Sq17.RepresentativeCaseData.patterns
      Sq17.RepresentativeCaseData.fullCases holes (.full 204)) :
    sourceRoster.toFinset = holes.toFinsetᶜ := by
  rw [← full_204_roster]
  exact h.2.2

end Sq17.CaptureFamily
#print axioms Sq17.CaptureFamily.full_204_roster
