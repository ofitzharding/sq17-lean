import Sq17Lean.HalfPlaneFinalAssembly
import Sq17Lean.HalfPlaneTrees.T1528.Dispatch
import Sq17Lean.HalfPlaneTrees.T1531.Dispatch

/-! The checked 1528/1531 dispatchers leave just neighbour 329 and tree 1563.
The two remaining premises are explicit; optimality is still conditional. -/
namespace Sq17.HalfPlaneAssembly

def FullCaseExcluded (k : ℕ) : Prop :=
  ∀ L : ℝ, L < EndpointGeometry.side → ∀ holes : List (Fin 24),
    RepresentativePacking holes L →
    (RepresentativeCaseData.fullCases k).toFinset = holes.toFinsetᶜ → False

theorem neighbours_of_two (neighbour329 : FullCaseExcluded 209)
    (tree1563 : FullCaseExcluded 1193) : NeighbourCasesExcluded := by
  intro k hk L hL holes P hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact neighbour329 L hL holes P hr
  · exact Propagation.HalfPlaneState.T1528.full_dispatch L hL holes P hr
  · exact Propagation.HalfPlaneState.T1531.full_dispatch L hL holes P hr
  · exact tree1563 L hL holes P hr

theorem feasible_iff_of_two (neighbour329 : FullCaseExcluded 209)
    (tree1563 : FullCaseExcluded 1193) (L : ℝ) :
    Feasible L ↔ EndpointGeometry.side ≤ L :=
  feasible_iff_of_neighbours (neighbours_of_two neighbour329 tree1563) L

theorem plainPacking_iff_of_two (neighbour329 : FullCaseExcluded 209)
    (tree1563 : FullCaseExcluded 1193) (L : ℝ) :
    PlainPacking L ↔ EndpointGeometry.side ≤ L :=
  plainPacking_iff_of_neighbours (neighbours_of_two neighbour329 tree1563) L

end Sq17.HalfPlaneAssembly

#print axioms Sq17.HalfPlaneAssembly.plainPacking_iff_of_two
