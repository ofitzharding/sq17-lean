import Sq17Lean.CaptureRunFast

/-! Core-only proposed angle-table checker, isolated from frozen modules.
`CaptureTableSound` must connect these definitions to the geometric certificates.
No soundness claim is made by this definitions-only module. -/
namespace Sq17.Propagation.HalfPlaneState.CaptureTableFast

structure Bounds where
  cosLo : Rat
  cosHi : Rat
  sinLo : Rat
  sinHi : Rat

structure Endpoint where
  dLo : Rat
  dHi : Rat
  xLo : Rat
  xHi : Rat

def absQ (x : Rat) : Rat := if 0 ≤ x then x else -x

def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

def power (x : Rat) : Nat → Rat
  | 0 => 1
  | n+1 => power x n * x

def coeff : Nat → Rat × Rat
  | 0 => (1, 0)
  | n+1 => (-(coeff n).2, (coeff n).1)

/-- Sum over indices strictly below `count`; a successor proof identifies this
with the existing finite Taylor sum. -/
def taylorSum (x : Rat) : Nat → Rat × Rat
  | 0 => (0, 0)
  | n+1 =>
    let old := taylorSum x n
    let term := power x n / (factorial n : Rat)
    (old.1 + (coeff n).1 * term, old.2 + (coeff n).2 * term)

def remainder (n : Nat) (x : Rat) : Rat :=
  power (absQ x) (n+1) / (factorial (n+1) : Rat)

def trigCheck (n : Nat) (x : Rat) (b : Bounds) : Bool :=
  let cs := taylorSum x (n+1)
  let r := remainder n x
  decide (b.cosLo ≤ cs.1-r ∧ cs.1+r ≤ b.cosHi ∧
    b.sinLo ≤ cs.2-r ∧ cs.2+r ≤ b.sinHi)

def endpoint (c s : Rat) (b : Bounds) : Endpoint where
  dLo := min (c*b.cosLo) (c*b.cosHi) + min (s*b.sinLo) (s*b.sinHi)
  dHi := max (c*b.cosLo) (c*b.cosHi) + max (s*b.sinLo) (s*b.sinHi)
  xLo := min (c*b.sinLo) (c*b.sinHi) + min ((-s)*b.cosLo) ((-s)*b.cosHi)
  xHi := max (c*b.sinLo) (c*b.sinHi) + max ((-s)*b.cosLo) ((-s)*b.cosHi)

def endpointCheck (h : Rat) (b : Endpoint) : Bool :=
  decide (0 ≤ h ∧ 0 < b.dLo ∧ b.dLo ≤ b.dHi ∧ b.xLo ≤ b.xHi ∧
    max (absQ b.xLo) (absQ b.xHi) ≤ b.dLo ∧
    h * (b.dHi + max (absQ b.xLo) (absQ b.xHi)) ≤ 1)

def wallDir (e : Entry) : Rat × Rat :=
  if 0 ≤ e.lo then (1, 1) else if e.hi ≤ 0 then (1, -1) else (0, 0)

/-- Each endpoint Taylor check is evaluated once, then shared by core and wall
conditions. The existing table checker evaluates it twice. -/
def entryCheck (n : Nat) (e : Entry) (b : Bounds × Bounds) : Bool :=
  let c := (e.C : Rat)/e.cd
  let s := (e.S : Rat)/e.cd
  let h := (e.H : Rat)/e.hd
  let d := wallDir e
  trigCheck n e.lo b.1 && trigCheck n e.hi b.2 &&
    decide (0 ≤ e.hi-e.lo ∧ e.hi-e.lo ≤ 1) &&
    endpointCheck h (endpoint c s b.1) && endpointCheck h (endpoint c s b.2) &&
    decide (absQ d.1 ≤ 1 ∧ absQ d.2 ≤ 1 ∧ 0 ≤ e.span ∧ e.lo ≤ e.hi ∧
      e.hi-e.lo ≤ 1 ∧ e.span ≤ (endpoint d.1 d.2 b.1).dLo ∧
      e.span ≤ (endpoint d.1 d.2 b.2).dLo)

/-- Full-entry equality permits reuse of previous soundness certificates. -/
def inheritedCheck (old current : Array Entry) (ids : Array Nat) : Bool :=
  decide (ids.size ≤ current.size) && (List.range ids.size).all fun k =>
    match ids[k]?, current[k]? with
    | some i, some e =>
      match old[i]? with
      | some f => decide (e = f)
      | none => false
    | _, _ => false

/-- Bounds contains only the suffix's fresh entries, starting at offset zero. -/
def freshCheck (n : Nat) (T : Array Entry) (offset : Nat)
    (B : Array (Bounds × Bounds)) : Bool :=
  decide (offset ≤ T.size) && (List.range (T.size-offset)).all fun j =>
    match T[offset+j]?, B[j]? with
    | some e, some b => entryCheck n e b
    | _, _ => false

/-- Compact rational payload decoding; all data remains checked downstream. -/
def ratioAt (a : Array Int) (i : Nat) : Rat := (a[i]! : Rat) / (a[i+1]! : Rat)

def decodeEntries : Nat → Array Int → Nat → Array Entry → Array Entry
  | 0, _, _, out => out
  | fuel+1, a, p, out =>
    if p+11 > a.size then out else
      decodeEntries fuel a (p+11) (out.push
        ⟨ratioAt a p, ratioAt a (p+2), a[p+4]!, a[p+5]!, a[p+6]!,
         a[p+7]!, a[p+8]!, ratioAt a (p+9)⟩)

def boundsAt (a : Array Int) (p : Nat) : Bounds :=
  ⟨ratioAt a p, ratioAt a (p+2), ratioAt a (p+4), ratioAt a (p+6)⟩

def decodeBounds : Nat → Array Int → Nat → Array (Bounds × Bounds) → Array (Bounds × Bounds)
  | 0, _, _, out => out
  | fuel+1, a, p, out =>
    if p+16 > a.size then out else
      decodeBounds fuel a (p+16) (out.push (boundsAt a p, boundsAt a (p+8)))

end Sq17.Propagation.HalfPlaneState.CaptureTableFast
