import Sq17Lean.HalfPlaneCoverFast
import Sq17Lean.HalfPlaneTrees.T1563.Root
import Sq17Lean.HalfPlaneTrees.T1563.RootAlt
import Sq17Lean.HalfPlaneTrees.T1563.Node0
import Sq17Lean.HalfPlaneTrees.T1563.Cover_RootAlt_Node0

/-! The root cover, transported from `RootAlt` to `Root`. `RootAlt` repeats the
definitions of `Root` verbatim, without its two computed facts, so that the cover
check could run alongside the root replay. The identifications are by unfolding. -/
namespace Sq17.Propagation.HalfPlaneState.T1563.Cover_Root_Node0
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem table_eq : RootAlt.table = Root.table := rfl
theorem init_eq : RootAlt.initRaw = Root.initRaw := rfl
theorem steps_eq : RootAlt.stepsRaw = Root.stepsRaw := rfl
theorem E_eq : RootAlt.E = Root.E := by
  unfold RootAlt.E Root.E RootAlt.S0 Root.S0 RootAlt.steps Root.steps
  rw [table_eq, init_eq, steps_eq]

theorem cover : coverCheck Root.table Node0.table Root.E Node0.S0 0 [] none none = true := by
  have h := Cover_RootAlt_Node0.cover
  rw [table_eq, E_eq] at h
  exact h

end Sq17.Propagation.HalfPlaneState.T1563.Cover_Root_Node0
