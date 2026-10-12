import Sq17Lean.Neighbour329.Chain
import Sq17Lean.Neighbour329.Binding
namespace Sq17.Propagation.HalfPlaneState.Neighbour329
theorem full_dispatch (L : ℝ) (hL : L < Sq17.EndpointGeometry.side)
    (holes : List (Fin 24)) (P : Sq17.HalfPlaneAssembly.RepresentativePacking holes L)
    (hr : (Sq17.RepresentativeCaseData.fullCases 209).toFinset = holes.toFinsetᶜ) : False :=
  full_dispatch_of_excluded excluded L hL holes P hr
end Sq17.Propagation.HalfPlaneState.Neighbour329
#print axioms Sq17.Propagation.HalfPlaneState.Neighbour329.full_dispatch
