import Sq17Lean.HalfPlaneLastTwo
import Sq17Lean.Neighbour329.Dispatch

/-! The complete 329 chunk chain is now connected. The only remaining
exclusion premise is tree 1563, classifier index 1193. -/
namespace Sq17.HalfPlaneAssembly

theorem feasible_iff_of_1563 (tree1563 : FullCaseExcluded 1193) (L : ℝ) :
    Feasible L ↔ EndpointGeometry.side ≤ L :=
  feasible_iff_of_two Propagation.HalfPlaneState.Neighbour329.full_dispatch tree1563 L

theorem plainPacking_iff_of_1563 (tree1563 : FullCaseExcluded 1193) (L : ℝ) :
    PlainPacking L ↔ EndpointGeometry.side ≤ L :=
  plainPacking_iff_of_two Propagation.HalfPlaneState.Neighbour329.full_dispatch tree1563 L

end Sq17.HalfPlaneAssembly

#print axioms Sq17.HalfPlaneAssembly.plainPacking_iff_of_1563
