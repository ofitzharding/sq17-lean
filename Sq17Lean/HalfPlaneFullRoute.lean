import Sq17Lean.RepresentativeCaseData
import Sq17Lean.HalfPlaneCases.OrdinaryIndices

/-! Exhaustive routing of full classifier cases. Both finite checks below are
kernel reductions, with no dependency on any ordinary case proof. -/
namespace Sq17.HalfPlaneAssembly
open FiniteOrbitCover RepresentativeCaseData Propagation.HalfPlaneState

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def keysBelow (bound : ℕ) : RepTree → Bool
  | .empty => true
  | .node key _ left right =>
      decide (key < bound) && keysBelow bound left && keysBelow bound right

theorem find_none_of_keysBelow (bound : ℕ) (tree : RepTree)
    (checked : keysBelow bound tree = true) (k : ℕ) (hk : bound ≤ k) :
    tree.find k = none := by
  induction tree with
  | empty => rfl
  | node key row left right il ir =>
    have h : key < bound ∧ keysBelow bound left = true ∧ keysBelow bound right = true := by
      simpa only [keysBelow, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using checked
    have hne : k ≠ key := by omega
    simp only [RepTree.find, ite_eq_right hne]
    split
    · exact il h.2.1
    · exact ir h.2.2

theorem full_roster_keys_bounded : keysBelow 2781 fullRosters = true := by
  decide +kernel

/-- This includes *every* natural index outside the table, not just its successor. -/
theorem fullCases_eq_nil_of_ge (k : ℕ) (hk : 2781 ≤ k) : fullCases k = [] := by
  unfold fullCases
  rw [find_none_of_keysBelow 2781 fullRosters full_roster_keys_bounded k hk]
  rfl

theorem ordinary_indices_eq_filter :
    ordinaryIndices = (List.range 2781).filter
      (fun k => decide (k ≠ 204 ∧ k ≠ 209 ∧ k ≠ 1158 ∧ k ≠ 1161 ∧ k ≠ 1193)) := by
  decide +kernel

theorem full_route_of_lt (k : ℕ) (hk : k < 2781) :
    k ∈ ordinaryIndices ∨ k ∈ [209, 1158, 1161, 1193] ∨ k = 204 := by
  by_cases he : k = 204 ∨ k = 209 ∨ k = 1158 ∨ k = 1161 ∨ k = 1193
  · rcases he with rfl | rfl | rfl | rfl | rfl <;> simp
  · left
    rw [ordinary_indices_eq_filter, List.mem_filter]
    exact ⟨List.mem_range.mpr hk, by simp only [decide_eq_true_eq]; tauto⟩

theorem full_route (k : ℕ) (hk : (fullCases k).length = 17) :
    k ∈ ordinaryIndices ∨ k ∈ [209, 1158, 1161, 1193] ∨ k = 204 := by
  apply full_route_of_lt k
  by_contra hn
  rw [fullCases_eq_nil_of_ge k (by omega)] at hk
  simp at hk

end Sq17.HalfPlaneAssembly

#print axioms Sq17.HalfPlaneAssembly.fullCases_eq_nil_of_ge
#print axioms Sq17.HalfPlaneAssembly.full_route
