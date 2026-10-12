import Sq17Lean.LocalRigidityBox

namespace Sq17.LocalRigidity
open scoped BigOperators

/-- Coefficientwise quadratic box bounds imply the uniform L1 residual
bound consumed by the weighted dual theorem. -/
theorem quadratic_residual_bound {Params Cols : Type*}
    [Fintype Params] [Fintype Cols]
    (z H : Params → ℝ) (a : Cols → ℝ)
    (b : Params → Cols → ℝ) (c : Params → Params → Cols → ℝ)
    (ε : ℝ) (hz : ∀ k, |z k| ≤ H k)
    (hbudget : (∑ j, |a j|) + (∑ k, H k * (∑ j, |b k j|)) +
      (∑ k, ∑ l, (H k * H l) * (∑ j, |c k l j|)) ≤ ε) :
    (∑ j, |a j + (∑ k, z k * b k j) +
      ∑ k, ∑ l, (z k * z l) * c k l j|) ≤ ε := by
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    quadratic_box_abs z H (fun k => b k j) (a j) (fun k l => c k l j) hz)
  have he₁ : (∑ j, ∑ k, H k * |b k j|) = ∑ k, H k * (∑ j, |b k j|) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  have he₂ : (∑ j, ∑ k, ∑ l, (H k * H l) * |c k l j|) =
      ∑ k, ∑ l, (H k * H l) * (∑ j, |c k l j|) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  simp only [Finset.sum_add_distrib] at hb
  rw [he₁, he₂] at hb
  exact hb.trans hbudget

end Sq17.LocalRigidity
#print axioms Sq17.LocalRigidity.quadratic_residual_bound
