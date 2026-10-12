import Sq17Lean.Neighbour329.Chunk0000Checks
import Sq17Lean.Neighbour329.Seed
import Sq17Lean.HalfPlaneNeighbourDispatch
import Sq17Lean.RepresentativeCaseData
namespace Sq17.Propagation.HalfPlaneState.Neighbour329
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem no_packing_of_excluded (excluded : BranchComposition.Excluded Chunk0000.table Chunk0000.S0 Chunk0000.side Chunk0000.shift) (c u : Fin 17 → ℝ × ℝ)
    (hunit : ∀ i, (u i).1^2+(u i).2^2 = 1)
    (hcenter : ∀ i, c i ∈ CenteredOrbitFrame.shift (-(sigma:ℝ)) '' ExactCells.cell (roster i))
    (hd : ∀ i j, i ≠ j → Disjoint
      (interior (Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2))
      (interior (Sq17.sq (c j).1 (c j).2 (u j).1 (u j).2)))
    (hfit : ∀ i, Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2 ⊆ traceContainer side shift) : False :=
  tree_excluded Chunk0000.table side shift sigma 17 roster Chunk0000.S0
    seed_checked Chunk0000.initial_length excluded c u hunit hcenter hd hfit
theorem roster_eq : (Sq17.RepresentativeCaseData.fullCases 209).toFinset = (List.ofFn roster).toFinset := by decide +kernel
theorem full_dispatch_of_excluded (excluded : BranchComposition.Excluded Chunk0000.table Chunk0000.S0 Chunk0000.side Chunk0000.shift) (L : ℝ) (hL : L < Sq17.EndpointGeometry.side)
    (holes : List (Fin 24)) (P : Sq17.HalfPlaneAssembly.RepresentativePacking holes L)
    (hr : (Sq17.RepresentativeCaseData.fullCases 209).toFinset = holes.toFinsetᶜ) : False :=
  Sq17.HalfPlaneAssembly.neighbour_dispatch_of_case roster (by decide +kernel) side shift sigma
    (by norm_num [side, Chunk0000.side, Sq17.HalfPlaneFrameBounds.captureNeighbour])
    (by norm_num [shift, Chunk0000.shift, Sq17.HalfPlaneFrameBounds.captureNeighbour])
    (by norm_num [sigma, Sq17.HalfPlaneFrameBounds.captureNeighbour])
    (no_packing_of_excluded excluded) L hL holes P (roster_eq.symm.trans hr)
end Sq17.Propagation.HalfPlaneState.Neighbour329
#print axioms Sq17.Propagation.HalfPlaneState.Neighbour329.full_dispatch_of_excluded
