import Sq17Lean.CoreSeparationGeometry
import Sq17Lean.PropagationCoreCheck
import Sq17Lean.PropagationRational
import Mathlib.Analysis.Convex.Hull

/-! Linear-sized rational support certificates for polygon-pair collision.
Each of four axes scans each vertex list once. Strict margins preserve legal
boundary contact. Untrusted interval endpoints must pass every vertex check. -/
namespace Sq17.Propagation

structure SupportInterval where
  sourceLo : ℚ
  sourceHi : ℚ
  partnerLo : ℚ
  partnerHi : ℚ
  deriving DecidableEq, Repr

def coreSupportAxes (c s e f : ℚ) : Fin 4 → ℚ × ℚ :=
  ![(c,s),(-s,c),(e,f),(-f,e)]
def coreSupportThresholds (c s h e f k : ℚ) : Fin 4 → ℚ :=
  let D := |c*e+s*f|+|c*f-s*e|
  let A := (h*(c^2+s^2)+k*D)/2
  let B := (h*D+k*(e^2+f^2))/2
  ![A,A,B,B]

def projectionIntervalCheck (V W : List (ℚ × ℚ)) (a b t : ℚ)
    (r : SupportInterval) : Bool :=
  V.all (fun v => decide (r.sourceLo ≤ a*v.1+b*v.2 ∧ a*v.1+b*v.2 ≤ r.sourceHi)) &&
  W.all (fun v => decide (r.partnerLo ≤ a*v.1+b*v.2 ∧ a*v.1+b*v.2 ≤ r.partnerHi)) &&
  decide (r.partnerHi-r.sourceLo < t ∧ r.sourceHi-r.partnerLo < t)

def rationalSupportCollision (V W : List (ℚ × ℚ)) (c s h e f k : ℚ)
    (bounds : Fin 4 → SupportInterval) : Bool :=
  decide (0 < h ∧ 0 < c^2+s^2 ∧ 0 < k ∧ 0 < e^2+f^2) &&
  (List.finRange 4).all (fun i => projectionIntervalCheck V W
    (coreSupportAxes c s e f i).1 (coreSupportAxes c s e f i).2
    (coreSupportThresholds c s h e f k i) (bounds i))

/-- Closed linear projection bounds extend from vertices to their full hull. -/
theorem projection_bounds_hull (V : List (ℚ × ℚ)) (a b lo hi : ℚ)
    (hv : ∀ v ∈ V, lo ≤ a*v.1+b*v.2 ∧ a*v.1+b*v.2 ≤ hi)
    (x : ℝ × ℝ) (hx : x ∈ convexHull ℝ (realPoint '' {p | p ∈ V})) :
    (lo : ℝ) ≤ (a : ℝ)*x.1+(b : ℝ)*x.2 ∧
      (a : ℝ)*x.1+(b : ℝ)*x.2 ≤ (hi : ℝ) := by
  have hc : Convex ℝ {x : ℝ × ℝ | (lo : ℝ) ≤ (a : ℝ)*x.1+(b : ℝ)*x.2 ∧
      (a : ℝ)*x.1+(b : ℝ)*x.2 ≤ (hi : ℝ)} := by
    intro x hx y hy α β hα hβ hsum
    change (lo : ℝ) ≤ (a : ℝ)*(α*x.1+β*y.1)+(b : ℝ)*(α*x.2+β*y.2) ∧
      (a : ℝ)*(α*x.1+β*y.1)+(b : ℝ)*(α*x.2+β*y.2) ≤ (hi : ℝ)
    have he : (a : ℝ)*(α*x.1+β*y.1)+(b : ℝ)*(α*x.2+β*y.2) =
        α*((a : ℝ)*x.1+(b : ℝ)*x.2)+β*((a : ℝ)*y.1+(b : ℝ)*y.2) := by ring
    rw [he]
    constructor
    · have ht := add_le_add (mul_le_mul_of_nonneg_left hx.1 hα)
        (mul_le_mul_of_nonneg_left hy.1 hβ)
      simpa only [← add_mul,hsum,one_mul] using ht
    · have ht := add_le_add (mul_le_mul_of_nonneg_left hx.2 hα)
        (mul_le_mul_of_nonneg_left hy.2 hβ)
      simpa only [← add_mul,hsum,one_mul] using ht
  apply convexHull_min (t := {x : ℝ × ℝ | _}) ?_ hc hx
  rintro _ ⟨v,hv',rfl⟩
  change (lo : ℝ) ≤ (a : ℝ)*(v.1 : ℝ)+(b : ℝ)*(v.2 : ℝ) ∧
    (a : ℝ)*(v.1 : ℝ)+(b : ℝ)*(v.2 : ℝ) ≤ (hi : ℝ)
  exact_mod_cast hv v hv'

theorem projectionIntervalCheck_sound (V W : List (ℚ × ℚ)) (a b t : ℚ)
    (r : SupportInterval) (h : projectionIntervalCheck V W a b t r = true)
    (x y : ℝ × ℝ) (hx : x ∈ convexHull ℝ (realPoint '' {p | p ∈ V}))
    (hy : y ∈ convexHull ℝ (realPoint '' {p | p ∈ W})) :
    |(a : ℝ)*(y.1-x.1)+(b : ℝ)*(y.2-x.2)| < (t : ℝ) := by
  have hh : (∀ v ∈ V, r.sourceLo ≤ a*v.1+b*v.2 ∧ a*v.1+b*v.2 ≤ r.sourceHi) ∧
      (∀ v ∈ W, r.partnerLo ≤ a*v.1+b*v.2 ∧ a*v.1+b*v.2 ≤ r.partnerHi) ∧
      r.partnerHi-r.sourceLo < t ∧ r.sourceHi-r.partnerLo < t := by
    simpa only [projectionIntervalCheck,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,
      and_assoc] using h
  have hs := projection_bounds_hull V a b r.sourceLo r.sourceHi hh.1 x hx
  have hp := projection_bounds_hull W a b r.partnerLo r.partnerHi hh.2.1 y hy
  have ht : (r.partnerHi : ℝ)-(r.sourceLo : ℝ) < (t : ℝ) ∧
      (r.sourceHi : ℝ)-(r.partnerLo : ℝ) < (t : ℝ) := by exact_mod_cast hh.2.2
  apply abs_lt.mpr
  constructor <;> linarith

/-- A linear number of exact vertex bounds rules out disjoint core interiors. -/
theorem rationalSupportCollision_cores (V W : List (ℚ × ℚ)) (c s h e f k : ℚ)
    (bounds : Fin 4 → SupportInterval)
    (hc : rationalSupportCollision V W c s h e f k bounds = true)
    (x y : ℝ × ℝ) (hx : x ∈ convexHull ℝ (realPoint '' {p | p ∈ V}))
    (hy : y ∈ convexHull ℝ (realPoint '' {p | p ∈ W})) :
    ¬ Disjoint (interior (core x.1 x.2 c s h))
      (interior (core y.1 y.2 e f k)) := by
  have hpQ : 0 < h ∧ 0 < c^2+s^2 ∧ 0 < k ∧ 0 < e^2+f^2 := by
    simpa only [decide_eq_true_eq] using (Bool.and_eq_true_iff.mp hc).1
  have hp : (0 : ℝ) < h ∧ 0 < (c : ℝ)^2+(s : ℝ)^2 ∧
      0 < (k : ℝ) ∧ 0 < (e : ℝ)^2+(f : ℝ)^2 := by exact_mod_cast hpQ
  have ha (i : Fin 4) := projectionIntervalCheck_sound V W
    (coreSupportAxes c s e f i).1 (coreSupportAxes c s e f i).2
    (coreSupportThresholds c s h e f k i) (bounds i)
    ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).2) i (by simp)) x y hx hy
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  dsimp [coreSupportAxes,coreSupportThresholds] at h0 h1 h2 h3
  push_cast at h0 h1 h2 h3
  intro hdis
  have hs := CoreSAT.core_disjoint_axis x y c s h e f k
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 hdis
  have he1 : -(s : ℝ)*(y.1-x.1)+(c : ℝ)*(y.2-x.2) =
      (c : ℝ)*(y.2-x.2)-(s : ℝ)*(y.1-x.1) := by ring
  have he3 : -(f : ℝ)*(y.1-x.1)+(e : ℝ)*(y.2-x.2) =
      (e : ℝ)*(y.2-x.2)-(f : ℝ)*(y.1-x.1) := by ring
  rw [he1] at h1
  rw [he3] at h3
  rcases hs with hs|hs|hs|hs <;> linarith

/-- Checked core rows and support intervals exclude every pair of actual
unit squares over the two polygon hulls and their complete closed angle rows. -/
theorem rationalSupportCollision_sound (V W : List (ℚ × ℚ))
    (r t : CoreRowCertificate) (nr nt : ℕ) (bounds : Fin 4 → SupportInterval)
    (hr : r.check nr = true) (ht : t.check nt = true)
    (hc : rationalSupportCollision V W r.c r.s r.side t.c t.s t.side bounds = true)
    (x y : ℝ × ℝ) (hx : x ∈ convexHull ℝ (realPoint '' {p | p ∈ V}))
    (hy : y ∈ convexHull ℝ (realPoint '' {p | p ∈ W}))
    (θ φ : ℝ) (hθ : θ ∈ Set.Icc (r.lo : ℝ) (r.hi : ℝ))
    (hφ : φ ∈ Set.Icc (t.lo : ℝ) (t.hi : ℝ)) :
    ¬ Disjoint (interior (Sq17.sq x.1 x.2 (Real.cos θ) (Real.sin θ)))
      (interior (Sq17.sq y.1 y.2 (Real.cos φ) (Real.sin φ))) := by
  intro hdis
  apply rationalSupportCollision_cores V W r.c r.s r.side t.c t.s t.side bounds hc x y hx hy
  exact hdis.mono (interior_mono (r.check_sound nr hr x.1 x.2 θ hθ))
    (interior_mono (t.check_sound nt ht y.1 y.2 φ hφ))

end Sq17.Propagation
#print axioms Sq17.Propagation.projection_bounds_hull
#print axioms Sq17.Propagation.projectionIntervalCheck_sound

#print axioms Sq17.Propagation.rationalSupportCollision_sound
