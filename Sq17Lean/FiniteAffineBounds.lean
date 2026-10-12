import Sq17Lean.PropagationState

/-! Finite affine inequalities extend from rational polygon vertices to every
point in their real convex hull. Closed inequalities retain boundary poses. -/
namespace Sq17.Propagation

theorem affineHull_bounds (V : List (ℚ × ℚ)) (A B C lo hi : ℝ)
    (hv : ∀ v ∈ V, lo ≤ A*(v.1:ℝ)+B*(v.2:ℝ)+C ∧
      A*(v.1:ℝ)+B*(v.2:ℝ)+C ≤ hi)
    (p : ℝ × ℝ) (hp : p ∈ convexHull ℝ (realPoint '' {v | v ∈ V})) :
    lo ≤ A*p.1+B*p.2+C ∧ A*p.1+B*p.2+C ≤ hi := by
  have hc : Convex ℝ {p : ℝ × ℝ | lo ≤ A*p.1+B*p.2+C ∧
      A*p.1+B*p.2+C ≤ hi} := by
    intro x hx y hy a b ha hb hab
    change lo ≤ A*(a*x.1+b*y.1)+B*(a*x.2+b*y.2)+C ∧
      A*(a*x.1+b*y.1)+B*(a*x.2+b*y.2)+C ≤ hi
    have he : A*(a*x.1+b*y.1)+B*(a*x.2+b*y.2)+C =
        a*(A*x.1+B*x.2+C)+b*(A*y.1+B*y.2+C) := by
      linear_combination -C*hab
    rw [he]
    constructor
    · calc
        lo = a*lo+b*lo := by rw [← add_mul,hab,one_mul]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx.1 ha)
          (mul_le_mul_of_nonneg_left hy.1 hb)
    · calc
        _ ≤ a*hi+b*hi := add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
          (mul_le_mul_of_nonneg_left hy.2 hb)
        _ = hi := by rw [← add_mul,hab,one_mul]
  apply convexHull_min (t := {p : ℝ × ℝ | _}) ?_ hc hp
  rintro _ ⟨v,hv',rfl⟩
  exact hv v hv'

def affineVertexCheck (V : List (ℚ × ℚ)) (A B C lo hi : ℚ) : Bool :=
  V.all fun v => decide (lo ≤ A*v.1+B*v.2+C ∧ A*v.1+B*v.2+C ≤ hi)

theorem affineVertexCheck_sound (V : List (ℚ × ℚ)) (A B C lo hi : ℚ)
    (hc : affineVertexCheck V A B C lo hi = true)
    (p : ℝ × ℝ) (hp : p ∈ convexHull ℝ (realPoint '' {v | v ∈ V})) :
    (lo:ℝ) ≤ (A:ℝ)*p.1+(B:ℝ)*p.2+C ∧
      (A:ℝ)*p.1+(B:ℝ)*p.2+C ≤ (hi:ℝ) := by
  apply affineHull_bounds V A B C lo hi ?_ p hp
  intro v hv
  have h := of_decide_eq_true ((List.all_eq_true.mp hc) v hv)
  exact ⟨by exact_mod_cast h.1,by exact_mod_cast h.2⟩

/-- A rational projection can be checked once for all vertices, while the
root-dependent normal and constant are certified separately. -/
theorem affine_approx_bounds (A B C a b ex ey M lo hi clo chi : ℝ)
    (p : ℝ × ℝ) (hM : 0 ≤ M)
    (hx : |p.1| ≤ M) (hy : |p.2| ≤ M)
    (hA : |A-a| ≤ ex) (hB : |B-b| ≤ ey)
    (hproj : lo ≤ a*p.1+b*p.2 ∧ a*p.1+b*p.2 ≤ hi)
    (hC : clo ≤ C ∧ C ≤ chi) :
    lo+clo-(ex+ey)*M ≤ A*p.1+B*p.2+C ∧
    A*p.1+B*p.2+C ≤ hi+chi+(ex+ey)*M := by
  have ex0 : 0 ≤ ex := (abs_nonneg _).trans hA
  have ey0 : 0 ≤ ey := (abs_nonneg _).trans hB
  have h1 : |(A-a)*p.1| ≤ ex*M := by
    rw [abs_mul]
    exact mul_le_mul hA hx (abs_nonneg _) ex0
  have h2 : |(B-b)*p.2| ≤ ey*M := by
    rw [abs_mul]
    exact mul_le_mul hB hy (abs_nonneg _) ey0
  have hsum := (abs_add_le ((A-a)*p.1) ((B-b)*p.2)).trans (add_le_add h1 h2)
  obtain ⟨hl,hu⟩ := abs_le.mp hsum
  constructor <;> nlinarith [hproj.1,hproj.2,hC.1,hC.2]

end Sq17.Propagation
#print axioms Sq17.Propagation.affineHull_bounds
#print axioms Sq17.Propagation.affineVertexCheck_sound
#print axioms Sq17.Propagation.affine_approx_bounds
