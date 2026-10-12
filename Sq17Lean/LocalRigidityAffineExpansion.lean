import Sq17Lean.LocalRigidityResidual

namespace Sq17.LocalRigidity
open scoped BigOperators

theorem scalar_affine_product {Params : Type*} [Fintype Params]
    (z μ b : Params → ℝ) (lam a : ℝ) :
    (lam + ∑ k, z k*μ k)*(a + ∑ k, z k*b k) =
      lam*a + (∑ k, z k*(μ k*a+lam*b k)) +
        ∑ k, ∑ l, (z k*z l)*(μ k*b l) := by
  have h1 : lam*(∑ k, z k*b k) = ∑ k, z k*(lam*b k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have h2 : (∑ k, z k*μ k)*a = ∑ k, z k*(μ k*a) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have h3 : (∑ k, z k*μ k)*(∑ l, z l*b l) =
      ∑ k, ∑ l, (z k*z l)*(μ k*b l) := by
    rw [Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  calc
    _ = lam*a + lam*(∑ k, z k*b k) + (∑ k, z k*μ k)*a +
        (∑ k, z k*μ k)*(∑ l, z l*b l) := by ring
    _ = _ := by
      rw [h1,h2,h3]
      simp only [mul_add,Finset.sum_add_distrib]
      ring

/-- The actual affine-weight/matrix pairing is exactly the quadratic
coefficient expansion used by the finite residual checker. -/
theorem affine_weight_matrix_expansion {Rows Params : Type*}
    [Fintype Rows] [Fintype Params]
    (z : Params → ℝ) (lam a : Rows → ℝ) (μ B : Params → Rows → ℝ) (d : ℝ) :
    (∑ i, (lam i + ∑ k, z k*μ k i)*(a i + ∑ k, z k*B k i)) + d =
      ((∑ i, lam i*a i)+d) +
      (∑ k, z k*((∑ i, μ k i*a i)+(∑ i, lam i*B k i))) +
      ∑ k, ∑ l, (z k*z l)*(∑ i, μ k i*B l i) := by
  simp_rw [scalar_affine_product]
  simp only [Finset.sum_add_distrib]
  have h1 : (∑ i, ∑ k, z k*(μ k i*a i+lam i*B k i)) =
      ∑ k, z k*((∑ i, μ k i*a i)+(∑ i, lam i*B k i)) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum,Finset.sum_add_distrib,mul_add]
  have h2 : (∑ i, ∑ k, ∑ l, (z k*z l)*(μ k i*B l i)) =
      ∑ k, ∑ l, (z k*z l)*(∑ i, μ k i*B l i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [h1,h2]
  ring

end Sq17.LocalRigidity
#print axioms Sq17.LocalRigidity.affine_weight_matrix_expansion
