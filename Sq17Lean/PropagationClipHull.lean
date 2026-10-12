import Mathlib.Tactic.FieldSimp
import Sq17Lean.PropagationClip
import Mathlib.Analysis.Convex.Combination

/-! Coverage of a half-plane cut by retained vertices and all crossing pairs.
The construction does not depend on cyclic vertex ordering. -/
namespace Sq17.Propagation
open scoped BigOperators

/-- Algebra behind the finite clipping certificate, for one coordinate. -/
theorem clip_weight_reconstruction {I J : Type*} [Fintype I] [Fintype J]
    (α a u : I → ℝ) (β b v : J → ℝ) (A B : ℝ)
    (hA : A = ∑ i, α i * (-a i)) (hB : B = ∑ j, β j * b j)
    (hA0 : A ≠ 0) (hab : ∀ i j, b j - a i ≠ 0) :
    (∑ i, α i * (1-B/A) * u i) +
      (∑ i, ∑ j, (α i * β j * (b j-a i)/A) *
        ((b j*u i-a i*v j)/(b j-a i))) =
      (∑ i, α i*u i) + ∑ j, β j*v j := by
  have term (i : I) (j : J) :
      (α i * β j * (b j-a i)/A) * ((b j*u i-a i*v j)/(b j-a i)) =
        (α i*u i/A)*(β j*b j) + (α i*(-a i))*(β j*v j/A) := by
    field_simp [hA0, hab i j]
    <;> ring
  simp_rw [term, Finset.sum_add_distrib]
  have mixed : (∑ i, ∑ j, (α i*(-a i))*(β j*v j/A)) = ∑ j, β j*v j := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← hA]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  rw [mixed]
  simp_rw [← Finset.mul_sum, ← hB]
  have left : (∑ i, α i*(1-B/A)*u i) + (∑ i, α i*u i/A*B) =
      ∑ i, α i*u i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
    <;> ring
  linarith

end Sq17.Propagation

#print axioms Sq17.Propagation.clip_weight_reconstruction
