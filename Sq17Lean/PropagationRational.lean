import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring
import Sq17Lean.PropagationInvariant

/-! An executable rational half-plane test with a theorem over real geometry.
This is one kernel component, not yet the complete trace checker. -/
namespace Sq17.Propagation

def rationalHalfPlane (V : List (ℚ × ℚ)) (a b threshold : ℚ) : Bool :=
  V.all fun p => decide (threshold < a * p.1 + b * p.2)

def realPoint (p : ℚ × ℚ) : ℝ × ℝ := (p.1, p.2)

def dotMap (a b : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun p := a * p.1 + b * p.2
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' r x := by simp; ring

/-- Acceptance of the executable rational test certifies a strict inequality
at every real point in the convex hull of the rational vertices. -/
theorem rationalHalfPlane_sound (V : List (ℚ × ℚ)) (a b threshold : ℚ)
    (h : rationalHalfPlane V a b threshold = true) :
    ∀ x ∈ convexHull ℝ (realPoint '' {p | p ∈ V}),
      (threshold : ℝ) < (a : ℝ) * x.1 + (b : ℝ) * x.2 := by
  apply strict_linear_on_hull (dotMap a b)
  intro x hx
  rcases hx with ⟨p, hp, rfl⟩
  have hall : ∀ p ∈ V, threshold < a * p.1 + b * p.2 := by
    simpa only [rationalHalfPlane, List.all_eq_true, decide_eq_true_eq] using h
  have hq := hall p hp
  change (threshold : ℝ) < (a : ℝ) * (p.1 : ℝ) + (b : ℝ) * (p.2 : ℝ)
  exact_mod_cast hq

end Sq17.Propagation

#print axioms Sq17.Propagation.rationalHalfPlane_sound
