import Mathlib.Tactic.FinCases
import Sq17Lean.PropagationClipHull

/-! Small rational witnesses for membership in a polygon's convex hull. -/
namespace Sq17.Propagation

structure HullTriangleWitness where
  u : ℚ × ℚ
  v : ℚ × ℚ
  w : ℚ × ℚ
  alpha : ℚ
  beta : ℚ
  gamma : ℚ

def triangleHullCheck (vertices : List (ℚ × ℚ)) (p : ℚ × ℚ)
    (t : HullTriangleWitness) : Bool := decide
  (t.u ∈ vertices ∧ t.v ∈ vertices ∧ t.w ∈ vertices ∧
   0 ≤ t.alpha ∧ 0 ≤ t.beta ∧ 0 ≤ t.gamma ∧
   t.alpha+t.beta+t.gamma = 1 ∧
   t.alpha*t.u.1+t.beta*t.v.1+t.gamma*t.w.1 = p.1 ∧
   t.alpha*t.u.2+t.beta*t.v.2+t.gamma*t.w.2 = p.2)

theorem triangleHullCheck_sound (vertices : List (ℚ × ℚ)) (p : ℚ × ℚ)
    (t : HullTriangleWitness) (hc : triangleHullCheck vertices p t = true) :
    realPoint p ∈ convexHull ℝ (realPoint '' {v | v ∈ vertices}) := by
  simp only [triangleHullCheck, decide_eq_true_eq] at hc
  rcases hc with ⟨hu,hv,hw,ha,hb,hg,hm,hx,hy⟩
  have ha' : 0 ≤ (t.alpha : ℝ) := by exact_mod_cast ha
  have hb' : 0 ≤ (t.beta : ℝ) := by exact_mod_cast hb
  have hg' : 0 ≤ (t.gamma : ℝ) := by exact_mod_cast hg
  have hm' : (t.alpha : ℝ)+t.beta+t.gamma = 1 := by exact_mod_cast hm
  have hx' : (t.alpha : ℝ)*(t.u.1 : ℝ)+t.beta*(t.v.1 : ℝ)+t.gamma*(t.w.1 : ℝ)
      = (p.1 : ℝ) := by exact_mod_cast hx
  have hy' : (t.alpha : ℝ)*(t.u.2 : ℝ)+t.beta*(t.v.2 : ℝ)+t.gamma*(t.w.2 : ℝ)
      = (p.2 : ℝ) := by exact_mod_cast hy
  apply mem_convexHull_of_exists_fintype
    (![t.alpha, t.beta, t.gamma] : Fin 3 → ℝ)
    (![realPoint t.u, realPoint t.v, realPoint t.w] : Fin 3 → ℝ × ℝ)
  · intro i
    fin_cases i <;> simp [ha',hb',hg']
  · simpa [Fin.sum_univ_succ, add_assoc] using hm'
  · intro i
    fin_cases i
    · exact ⟨t.u,hu,rfl⟩
    · exact ⟨t.v,hv,rfl⟩
    · exact ⟨t.w,hw,rfl⟩
  · ext
    · simpa [Fin.sum_univ_succ, realPoint, add_assoc] using hx'
    · simpa [Fin.sum_univ_succ, realPoint, add_assoc] using hy'

/-- Checking each source point gives containment of the entire source hull. -/
theorem triangleHullCheck_list_sound (source target : List (ℚ × ℚ))
    (witness : (ℚ × ℚ) → HullTriangleWitness)
    (hc : source.all (fun p => triangleHullCheck target p (witness p)) = true) :
    convexHull ℝ (realPoint '' {v | v ∈ source}) ⊆
      convexHull ℝ (realPoint '' {v | v ∈ target}) := by
  apply convexHull_min
  · rintro _ ⟨p,hp,rfl⟩
    exact triangleHullCheck_sound target p (witness p) ((List.all_eq_true.mp hc) p hp)
  · exact convex_convexHull ℝ _

end Sq17.Propagation

#print axioms Sq17.Propagation.triangleHullCheck_sound
#print axioms Sq17.Propagation.triangleHullCheck_list_sound
