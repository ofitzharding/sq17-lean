/-! The executable half-plane trace checker.

This module imports nothing beyond the Lean core, so that it can be compiled to
native code and loaded while case files are checked. It contains definitions only.
Every statement about them is proved in `HalfPlaneInt`, `HalfPlaneStateSound`,
`HalfPlaneTable`, `HalfPlaneSeed` and `HalfPlaneCells`. -/
namespace Sq17.Propagation.HalfPlaneInt

def iabs (a : Int) : Int := if 0 ≤ a then a else -a

/-- `|c e + s f| + |c f - s e|` on numerators. -/
def crossNum (C S E F : Int) : Int := iabs (C*E+S*F) + iabs (C*F-S*E)

structure IC where
  a : Int
  b : Int
  q : Int
  deriving DecidableEq, Repr

/-- From two constraints, an upper bound `N/d` for `ta*x+tb*y`. -/
def pairUpper (u v : IC) (ta tb : Int) : Option (Int × Int) :=
  if 0 < u.a*v.b-v.a*u.b ∧ 0 ≤ ta*v.b-v.a*tb ∧ 0 ≤ u.a*tb-ta*u.b then
    some ((ta*v.b-v.a*tb)*u.q+(u.a*tb-ta*u.b)*v.q, u.a*v.b-v.a*u.b)
  else none

def better (p q : Option (Int × Int)) : Option (Int × Int) :=
  match p, q with
  | none, q => q
  | some p, none => some p
  | some (N1, d1), some (N2, d2) => if N1*d2 ≤ N2*d1 then some (N1, d1) else some (N2, d2)

/-- Only one orientation of a pair can have a positive determinant. -/
def pairBoth (u v : IC) (ta tb : Int) : Option (Int × Int) :=
  if 0 < u.a*v.b-v.a*u.b then pairUpper u v ta tb else pairUpper v u ta tb

/-- Smallest bound over the pairs of `u` with each `v` in the list. -/
def scanPairs (u : IC) (ta tb : Int) : List IC → Option (Int × Int)
  | [] => none
  | v :: vs => better (pairBoth u v ta tb) (scanPairs u ta tb vs)

/-- Smallest bound over all ordered pairs of constraints. For a bounded nonempty
domain this is the exact support value, whatever the order of the list. -/
def findUpper : List IC → Int → Int → Option (Int × Int)
  | [], _, _ => none
  | u :: vs, ta, tb => better (scanPairs u ta tb vs) (findUpper vs ta tb)

def gapOK (hi lo : Option (Int × Int)) (L T : Int) : Bool :=
  match hi, lo with
  | some (N1, d1), some (N2, d2) => decide ((N1*d2+N2*d1)*L < T*(d1*d2))
  | _, _ => false

/-- Bounds for the four axis directions `x`, `-x`, `y`, `-y`. -/
structure Box where
  xp : Option (Int × Int)
  xm : Option (Int × Int)
  yp : Option (Int × Int)
  ym : Option (Int × Int)
  deriving DecidableEq

def mkBox (hs : List IC) : Box :=
  ⟨findUpper hs 1 0, findUpper hs (-1) 0, findUpper hs 0 1, findUpper hs 0 (-1)⟩

def selX (bx : Box) (a : Int) : Option (Int × Int) := if 0 ≤ a then bx.xp else bx.xm

def selY (bx : Box) (b : Int) : Option (Int × Int) := if 0 ≤ b then bx.yp else bx.ym

/-- A bound for `a*x+b*y` from the box alone: four multiplications. -/
def boxUpper (bx : Box) (a b : Int) : Option (Int × Int) :=
  match selX bx a, selY bx b with
  | some (N1, d1), some (N2, d2) => some (iabs a * N1 * d2 + iabs b * N2 * d1, d1*d2)
  | _, _ => none

/-- Both strict gaps for one axis. Each gap is tried first with the two boxes and
only then with the exact pair search. -/
def axisOK (S P : List IC) (bS bP : Box) (a b L T : Int) : Bool :=
  (gapOK (boxUpper bP a b) (boxUpper bS (-a) (-b)) L T ||
    gapOK (findUpper P a b) (findUpper S (-a) (-b)) L T) &&
  (gapOK (boxUpper bS a b) (boxUpper bP (-a) (-b)) L T ||
    gapOK (findUpper S a b) (findUpper P (-a) (-b)) L T)

/-- Collision of the two cores for every pair of centres in the two domains. -/
def collide (S P : List IC) (bS bP : Box) (C Sn cd H hd E F ed K kd : Int) : Bool :=
  decide (0<cd ∧ 0<hd ∧ 0<ed ∧ 0<kd ∧ 0<H ∧ 0<C*C+Sn*Sn ∧ 0<K ∧ 0<E*E+F*F) &&
  axisOK S P bS bP C Sn (2*hd*cd*kd*ed)
    (H*(C*C+Sn*Sn)*kd*ed+K*crossNum C Sn E F*hd*cd) &&
  axisOK S P bS bP (-Sn) C (2*hd*cd*kd*ed)
    (H*(C*C+Sn*Sn)*kd*ed+K*crossNum C Sn E F*hd*cd) &&
  axisOK S P bS bP E F (2*hd*cd*kd*ed)
    (H*crossNum C Sn E F*kd*ed+K*(E*E+F*F)*hd*cd) &&
  axisOK S P bS bP (-F) E (2*hd*cd*kd*ed)
    (H*crossNum C Sn E F*kd*ed+K*(E*E+F*F)*hd*cd)

end Sq17.Propagation.HalfPlaneInt

namespace Sq17.Propagation.HalfPlaneState
open Sq17.Propagation.HalfPlaneInt

/-- Half of `max 1 span`. -/
def halfSpan (span : Rat) : Rat := (if 1 ≤ span then span else 1) / 2

/-- Certified data of one angle row: the closed angle interval, an inscribed core
`(C/cd, S/cd, H/hd)` and a lower bound `span` for the wall support. -/
structure Entry where
  lo : Rat
  hi : Rat
  C : Int
  S : Int
  cd : Int
  H : Int
  hd : Int
  span : Rat

/-- A live row. `box` caches axis bounds of the centre domain; rows are always
built by `mkRow`, and the region of a row requires the box to hold. -/
structure HRow where
  cons : List IC
  box : Box
  e : Nat

def mkRow (cons : List IC) (e : Nat) : HRow := ⟨cons, mkBox cons, e⟩

abbrev HState := List (List HRow)

def rowsOf (S : HState) (i : Nat) : List HRow := S.getD i []

/-- Replace the row at position `k` of owner `i` by the given rows. -/
def splice (S : HState) (i k : Nat) (new : List HRow) : HState :=
  S.set i ((rowsOf S i).take k ++ new ++ (rowsOf S i).drop (k+1))

/-- Drop the constraints whose bit is set in `m` (lowest bit first). -/
def dropBits : List IC → Nat → List IC
  | [], _ => []
  | c :: cs, m => if m % 2 = 1 then dropBits cs (m/2) else c :: dropBits cs (m/2)

/-- The removed piece collides with every live row of the partner. -/
def collideRows (T : Array Entry) (cons : List IC) (bx : Box) (es : Entry)
    (rows : List HRow) : Bool :=
  rows.all fun t =>
    match T[t.e]? with
    | some et =>
      collide cons t.cons bx t.box es.C es.S es.cd es.H es.hd et.C et.S et.cd et.H et.hd
    | none => false

/-- An axis-parallel constraint implied by the legal centre box of a wall row. -/
def wallOK (span side shift : Rat) (c : IC) : Bool :=
  decide (c.b = 0 ∧ c.a < 0 ∧ (c.a:Rat)*(halfSpan span-shift) ≤ c.q) ||
  decide (c.b = 0 ∧ 0 < c.a ∧ (c.a:Rat)*(side+shift-halfSpan span) ≤ c.q) ||
  decide (c.a = 0 ∧ c.b < 0 ∧ (c.b:Rat)*(halfSpan span-shift) ≤ c.q) ||
  decide (c.a = 0 ∧ 0 < c.b ∧ (c.b:Rat)*(side+shift-halfSpan span) ≤ c.q)

/-- The domain is empty: some constraint is violated by every point allowed by
the others, with the bound found by the same pair search. -/
def emptyOK (cons : List IC) : Bool :=
  cons.any fun c =>
    match findUpper cons (-c.a) (-c.b) with
    | some (N, d) => decide (N < -c.q*d)
    | none => false

inductive Step where
  /-- Cut row `k` of owner `i` against partner `j`, keeping `keep`. -/
  | cut (i k j : Nat) (keep : IC) (m : Nat)
  /-- Delete row `k` of owner `i`: it collides with every row of `j`. -/
  | kill (i k j : Nat)
  /-- Add wall constraints to row `k` of owner `i`. -/
  | wall (i k : Nat) (w : List IC) (m : Nat)
  /-- Split the angle interval of row `k` of owner `i` into entries `e1`, `e2`. -/
  | split (i k e1 e2 : Nat)
  /-- Delete row `k` of owner `i`: its centre domain is empty. -/
  | dead (i k : Nat)

def Step.run (T : Array Entry) (side shift : Rat) (S : HState) : Step → Option HState
  | .cut i k j keep m =>
    match (rowsOf S i)[k]? with
    | none => none
    | some r =>
      match T[r.e]? with
      | none => none
      | some es =>
        if i ≠ j ∧ j < S.length ∧
            collideRows T (⟨-keep.a, -keep.b, -keep.q⟩ :: r.cons)
              (mkBox (⟨-keep.a, -keep.b, -keep.q⟩ :: r.cons)) es (rowsOf S j) = true then
          some (splice S i k [mkRow (dropBits (keep :: r.cons) m) r.e])
        else none
  | .kill i k j =>
    match (rowsOf S i)[k]? with
    | none => none
    | some r =>
      match T[r.e]? with
      | none => none
      | some es =>
        if i ≠ j ∧ j < S.length ∧ collideRows T r.cons r.box es (rowsOf S j) = true then
          some (splice S i k [])
        else none
  | .wall i k w m =>
    match (rowsOf S i)[k]? with
    | none => none
    | some r =>
      match T[r.e]? with
      | none => none
      | some es =>
        if w.all (wallOK es.span side shift) = true then
          some (splice S i k [mkRow (dropBits (w ++ r.cons) m) r.e])
        else none
  | .split i k e1 e2 =>
    match (rowsOf S i)[k]? with
    | none => none
    | some r =>
      match T[r.e]?, T[e1]?, T[e2]? with
      | some a, some a1, some a2 =>
        if a1.lo ≤ a.lo ∧ a2.lo ≤ a1.hi ∧ a.hi ≤ a2.hi then
          some (splice S i k [⟨r.cons, r.box, e1⟩, ⟨r.cons, r.box, e2⟩])
        else none
      | _, _, _ => none
  | .dead i k =>
    match (rowsOf S i)[k]? with
    | none => none
    | some r => if emptyOK r.cons = true then some (splice S i k []) else none

def runAll (T : Array Entry) (side shift : Rat) : HState → List Step → Option HState
  | S, [] => some S
  | S, st :: rest =>
    match st.run T side shift S with
    | some S' => runAll T side shift S' rest
    | none => none

/-- Some owner below `n` has no live row. -/
def hasEmpty (n : Nat) (S : HState) : Bool :=
  (List.range n).any fun i => (rowsOf S i).isEmpty

/-- Diagnostic only: the number of steps accepted before the first failure. -/
def accepted (T : Array Entry) (side shift : Rat) : HState → List Step → Nat → Nat
  | _, [], n => n
  | S, st :: rest, n =>
    match st.run T side shift S with
    | some S' => accepted T side shift S' rest (n+1)
    | none => n

def excludes (T : Array Entry) (side shift : Rat) (n : Nat) (S : HState) (steps : List Step) : Bool :=
  match runAll T side shift S steps with
  | some S' => hasEmpty n S'
  | none => false

def parseInts (s : String) : Array Int := ((s.splitOn " ").filterMap String.toInt?).toArray

def getICs (a : Array Int) (pos n : Nat) : List IC :=
  (List.range n).map fun t => ⟨a[pos+3*t]!, a[pos+3*t+1]!, a[pos+3*t+2]!⟩

/-- Records: `1 i k j a b q m` cut, `2 i k j` kill, `3 i k m n (a b q)*n` wall,
`4 i k e1 e2` split, `5 i k` dead. -/
def decodeSteps : Nat → Array Int → Nat → List Step → List Step
  | 0, _, _, acc => acc.reverse
  | fuel+1, a, pos, acc =>
    if pos ≥ a.size then acc.reverse else
    let tag := a[pos]!
    if tag = 1 then
      decodeSteps fuel a (pos+8) (.cut a[pos+1]!.toNat a[pos+2]!.toNat a[pos+3]!.toNat
        ⟨a[pos+4]!, a[pos+5]!, a[pos+6]!⟩ a[pos+7]!.toNat :: acc)
    else if tag = 2 then
      decodeSteps fuel a (pos+4) (.kill a[pos+1]!.toNat a[pos+2]!.toNat a[pos+3]!.toNat :: acc)
    else if tag = 3 then
      let n := a[pos+4]!.toNat
      decodeSteps fuel a (pos+5+3*n) (.wall a[pos+1]!.toNat a[pos+2]!.toNat
        (getICs a (pos+5) n) a[pos+3]!.toNat :: acc)
    else if tag = 4 then
      decodeSteps fuel a (pos+5) (.split a[pos+1]!.toNat a[pos+2]!.toNat a[pos+3]!.toNat
        a[pos+4]!.toNat :: acc)
    else if tag = 5 then
      decodeSteps fuel a (pos+3) (.dead a[pos+1]!.toNat a[pos+2]!.toNat :: acc)
    else acc.reverse

/-- Initial rows: `owner e n (a b q)*n`, appended to the owner's list in order. -/
def decodeInit : Nat → Array Int → Nat → HState → HState
  | 0, _, _, S => S
  | fuel+1, a, pos, S =>
    if pos ≥ a.size then S else
    let i := a[pos]!.toNat
    let n := a[pos+2]!.toNat
    decodeInit fuel a (pos+3+3*n)
      (S.set i (rowsOf S i ++ [mkRow (getICs a (pos+3) n) a[pos+1]!.toNat]))

end Sq17.Propagation.HalfPlaneState
