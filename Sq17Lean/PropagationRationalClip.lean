import Sq17Lean.PropagationHalfplaneCover

/-! Executable rational coverage certificates for strict polygon cuts. -/
namespace Sq17.Propagation

def rationalCutPoint (a b : ℚ) (u v : ℚ × ℚ) : ℚ × ℚ :=
  ((b*u.1-a*v.1)/(b-a), (b*u.2-a*v.2)/(b-a))

/-- Every retained vertex and every crossing pair must occur in the candidate
list. The list may contain additional points, which must also pass overlap. -/
def rationalClipCheck (before candidates : List (ℚ × ℚ)) (a b q : ℚ) : Bool :=
  before.all (fun u => decide (a*u.1+b*u.2 ≤ q → u ∈ candidates)) &&
  before.all (fun u => before.all (fun v => decide
    (a*u.1+b*u.2 ≤ q ∧ q < a*v.1+b*v.2 →
      rationalCutPoint (a*u.1+b*u.2-q) (a*v.1+b*v.2-q) u v ∈ candidates)))

theorem realPoint_rationalCutPoint (a b : ℚ) (u v : ℚ × ℚ) :
    realPoint (rationalCutPoint a b u v) = cutPoint (a : ℝ) (b : ℝ)
      (realPoint u) (realPoint v) := by
  ext <;> simp [realPoint, rationalCutPoint, cutPoint]

/-- Acceptance covers every real center strictly on the removed side,
including centers in the interior rather than just source vertices. -/
theorem rationalClipCheck_sound_closed (before candidates : List (ℚ × ℚ)) (a b q : ℚ)
    (hc : rationalClipCheck before candidates a b q = true)
    (x : ℝ × ℝ)
    (hx : x ∈ convexHull ℝ (realPoint '' {v | v ∈ before}))
    (hcut : (a : ℝ)*x.1+(b : ℝ)*x.2 ≤ (q : ℝ)) :
    x ∈ convexHull ℝ (realPoint '' {v | v ∈ candidates}) := by
  simp only [rationalClipCheck, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hc
  have hh := closed_halfplane_hull_coverage (realPoint '' {v | v ∈ before})
    (dotMap a b) q x hx hcut
  apply convexHull_mono (s := clipCandidates (realPoint '' {v | v ∈ before})
    (dotMap a b) q) ?_ hh
  intro y hy
  rcases hy with ⟨⟨u, hu, rfl⟩, hret⟩ | ⟨u, ⟨ur, hur, rfl⟩, v, ⟨vr, hvr, rfl⟩,
    hret, hout, rfl⟩
  · have hq : a*u.1+b*u.2 ≤ q := by
      change (a : ℝ)*(u.1 : ℝ)+(b : ℝ)*(u.2 : ℝ) ≤ (q : ℝ) at hret
      exact_mod_cast hret
    exact ⟨u, hc.1 u hu hq, rfl⟩
  · have hi : a*ur.1+b*ur.2 ≤ q := by
      change (a : ℝ)*(ur.1 : ℝ)+(b : ℝ)*(ur.2 : ℝ) ≤ (q : ℝ) at hret
      exact_mod_cast hret
    have ho : q < a*vr.1+b*vr.2 := by
      change (q : ℝ) < (a : ℝ)*(vr.1 : ℝ)+(b : ℝ)*(vr.2 : ℝ) at hout
      exact_mod_cast hout
    refine ⟨rationalCutPoint (a*ur.1+b*ur.2-q) (a*vr.1+b*vr.2-q) ur vr,
      hc.2 ur hur vr hvr ⟨hi,ho⟩, ?_⟩
    rw [realPoint_rationalCutPoint]
    simp [dotMap, realPoint]

/-- Strict removal is covered by the same closed candidate certificate. -/
theorem rationalClipCheck_sound (before candidates : List (ℚ × ℚ)) (a b q : ℚ)
    (hc : rationalClipCheck before candidates a b q = true)
    (x : ℝ × ℝ)
    (hx : x ∈ convexHull ℝ (realPoint '' {v | v ∈ before}))
    (hcut : (a : ℝ)*x.1+(b : ℝ)*x.2 < (q : ℝ)) :
    x ∈ convexHull ℝ (realPoint '' {v | v ∈ candidates}) :=
  rationalClipCheck_sound_closed before candidates a b q hc x hx hcut.le

end Sq17.Propagation

#print axioms Sq17.Propagation.rationalClipCheck_sound_closed
#print axioms Sq17.Propagation.rationalClipCheck_sound
