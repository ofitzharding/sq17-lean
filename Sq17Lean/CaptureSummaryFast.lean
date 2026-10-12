import Sq17Lean.HalfPlaneCoverFast

/-! Core-only terminal summary check. A target consists of a closed angle
interval and integer half-planes, all independently checked by implication. -/
namespace Sq17.Propagation.HalfPlaneState.CaptureSummary
open Sq17.Propagation.HalfPlaneInt

structure Target where
  lo : Rat
  hi : Rat
  cons : List IC
  deriving Inhabited

def rowCheck (T : Array Entry) (target : Target) (r : HRow) : Bool :=
  match T[r.e]? with
  | none => true
  | some e => decide (target.lo ≤ e.lo ∧ e.hi ≤ target.hi) &&
      target.cons.all (impliedOK r.cons)

def summaryCheck (T : Array Entry) (S : HState) (targets : Array Target) : Bool :=
  decide (S.length = 17 ∧ targets.size = 17) &&
    (List.range 17).all fun i => (rowsOf S i).all (rowCheck T targets[i]!)

end Sq17.Propagation.HalfPlaneState.CaptureSummary
