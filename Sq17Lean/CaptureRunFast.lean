import Sq17Lean.HalfPlaneFast

/-! Core-only executable acceptance of OPEN segments and exact snapshot links.
No geometric claim is made until CaptureRunSound is applied. -/
namespace Sq17.Propagation.HalfPlaneState

deriving instance DecidableEq for HRow
deriving instance DecidableEq for Entry

def runToCheck (T : Array Entry) (side padding : Rat) (S : HState)
    (steps : List Step) (E : HState) : Bool :=
  match runAll T side padding S steps with
  | some R => decide (R = E)
  | none => false

def rowsSameGeometry (T U : Array Entry) : List HRow → List HRow → Bool
  | [], [] => true
  | r :: rs, s :: ss =>
    decide (r.cons = s.cons ∧ r.box = s.box) &&
    (match T[r.e]?, U[s.e]? with
     | some e, some f => decide (e.lo = f.lo ∧ e.hi = f.hi)
     | _, _ => false) && rowsSameGeometry T U rs ss
  | _, _ => false

def sameGeometry (T U : Array Entry) (S E : HState) : Bool :=
  decide (E.length = S.length) && (List.range S.length).all fun i =>
    rowsSameGeometry T U (rowsOf S i) (rowsOf E i)

end Sq17.Propagation.HalfPlaneState
