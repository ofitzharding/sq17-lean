import Sq17Lean.CaptureRunSound
import Sq17Lean.HalfPlaneBranchComposition

/-! Chunked EXCLUDED traces. Boundaries compare actual row geometry, and the
terminal empty owner is checked within the state's own owner count. -/
namespace Sq17.Propagation.HalfPlaneState.BranchComposition

theorem excluded_of_empty (T : Array Entry) (S : HState) (side padding : ℚ)
    (checked : hasEmpty S.length S = true) : Excluded T S side padding := by
  intro p hr _ _
  simp only [hasEmpty, List.any_eq_true, List.mem_range, List.isEmpty_iff] at checked
  obtain ⟨i, hi, he⟩ := checked
  obtain ⟨r, hmem, _⟩ := hr i hi
  rw [he] at hmem
  simp at hmem

theorem excluded_of_sameGeometry (T U : Array Entry) (S E : HState)
    (side padding : ℚ) (checked : sameGeometry T U S E = true)
    (hend : Excluded U E side padding) : Excluded T S side padding := by
  intro p hr hp hf
  obtain ⟨he, hlen⟩ := sameGeometry_sound T U S E checked p hr
  exact hend p he (by simpa only [hlen] using hp) (by simpa only [hlen] using hf)

theorem excluded_of_runToCheck (T : Array Entry) (S E : HState)
    (side padding : ℚ) (steps : List Step) (hT : TableValid T 44)
    (checked : runToCheck T side padding S steps E = true)
    (hend : Excluded T E side padding) : Excluded T S side padding :=
  excluded_of_run T S E side padding steps hT
    (runToCheck_eq T side padding S steps E checked) hend

end Sq17.Propagation.HalfPlaneState.BranchComposition

#print axioms Sq17.Propagation.HalfPlaneState.BranchComposition.excluded_of_empty
#print axioms Sq17.Propagation.HalfPlaneState.BranchComposition.excluded_of_sameGeometry
#print axioms Sq17.Propagation.HalfPlaneState.BranchComposition.excluded_of_runToCheck
