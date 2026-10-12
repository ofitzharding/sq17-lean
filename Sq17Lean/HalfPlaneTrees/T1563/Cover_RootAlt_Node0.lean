import Sq17Lean.HalfPlaneCoverFast
import Sq17Lean.HalfPlaneTrees.T1563.RootAlt
import Sq17Lean.HalfPlaneTrees.T1563.Node0

/-! The root-to-first-node cover, stated on `RootAlt`: the same definitions as
`Root` without its two computed facts, so that this check can run alongside the
root replay instead of after it. `Tree` identifies the two by definitional unfolding. -/
namespace Sq17.Propagation.HalfPlaneState.T1563.Cover_RootAlt_Node0
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem cover : coverCheck RootAlt.table Node0.table RootAlt.E Node0.S0 0 [] none none = true := by
  native_decide

end Sq17.Propagation.HalfPlaneState.T1563.Cover_RootAlt_Node0
