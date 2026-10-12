import Sq17Lean.HalfPlaneFast

/-! Executable checkpoint cover check, core Lean only so that it compiles to
native code. Statements about it are proved in `HalfPlaneCover`. -/
namespace Sq17.Propagation.HalfPlaneState
open Sq17.Propagation.HalfPlaneInt

/-- The constraint `c` holds on the whole domain of `cons`: the pair search
bounds its left side by its right side. -/
def impliedOK (cons : List IC) (c : IC) : Bool :=
  match findUpper cons c.a c.b with
  | some (N, d) => decide (N ≤ c.q*d)
  | none => false

/-- The centre domain of row `s` contains the domain of `cons`. -/
def rowContains (cons : List IC) (s : HRow) : Bool :=
  s.cons.all (impliedOK cons)

/-- The closed angle interval `[lo,hi]` is covered, scanning in order, by rows of
the child whose centre domains contain `cons`. Rows that do not help are skipped. -/
def coverRow (U : Array Entry) (cons : List IC) (hi : Rat) : Rat → List HRow → Bool
  | _, [] => false
  | lo, s :: rest =>
    match U[s.e]? with
    | none => coverRow U cons hi lo rest
    | some e =>
      if e.lo ≤ lo ∧ lo ≤ e.hi ∧ rowContains cons s = true then
        decide (hi ≤ e.hi) || coverRow U cons hi e.hi rest
      else coverRow U cons hi lo rest

def clampLo (plo : Rat) (alo : Option Rat) : Rat :=
  match alo with
  | some m => if plo ≤ m then m else plo
  | none => plo

def clampHi (phi : Rat) (ahi : Option Rat) : Rat :=
  match ahi with
  | some m => if m ≤ phi then m else phi
  | none => phi

/-- One parent row, restricted by centre constraints `cut` and by optional angle
bounds, lies in the child's rows: its angle interval is empty, or its centre
domain is empty, or it is covered. -/
def rowCheck (T U : Array Entry) (childRows : List HRow) (cut : List IC)
    (alo ahi : Option Rat) (r : HRow) : Bool :=
  match T[r.e]? with
  | none => true
  | some e =>
    decide (clampHi e.hi ahi < clampLo e.lo alo) || emptyOK (cut ++ r.cons) ||
      coverRow U (cut ++ r.cons) (clampHi e.hi ahi) (clampLo e.lo alo) childRows

/-- Every parent row lies in the child's rows; the split owner's rows are first
restricted by the branch guard. Child boxes must be the computed ones. -/
def coverCheck (T U : Array Entry) (parent child : HState) (owner : Nat) (cut : List IC)
    (alo ahi : Option Rat) : Bool :=
  (List.range parent.length).all fun i =>
    (rowsOf child i).all (fun s => decide (s.box = mkBox s.cons)) &&
    (rowsOf parent i).all fun r =>
      if i = owner then rowCheck T U (rowsOf child i) cut alo ahi r
      else rowCheck T U (rowsOf child i) [] none none r

end Sq17.Propagation.HalfPlaneState
