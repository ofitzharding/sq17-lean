import Sq17Lean.LocalRigidityDual

/-! Finite box bounds for affine dual weights and quadratic residuals.
The input inequalities are explicit arithmetic obligations; no particular
geometric matrix or inherited certificate is asserted to satisfy them. -/
namespace Sq17.LocalRigidity
open scoped BigOperators

theorem box_pairing_abs {ι : Type*} [Fintype ι]
    (z H v : ι → ℝ) (hz : ∀ k, |z k| ≤ H k) :
    |∑ k, z k * v k| ≤ ∑ k, H k * |v k| := by
  calc
    |∑ k, z k * v k| ≤ ∑ k, |z k * v k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |z k| * |v k| := by simp_rw [abs_mul]
    _ ≤ ∑ k, H k * |v k| := Finset.sum_le_sum
      (fun k _ => mul_le_mul_of_nonneg_right (hz k) (abs_nonneg _))

/-- The minimum of an affine weight on a centered box is bounded by the
sum of the absolute coefficient contributions. -/
theorem affine_weight_nonnegative {ι : Type*} [Fintype ι]
    (z H μ : ι → ℝ) (lam : ℝ) (hz : ∀ k, |z k| ≤ H k)
    (hlam : ∑ k, H k * |μ k| ≤ lam) : 0 ≤ lam + ∑ k, z k * μ k := by
  have hb := box_pairing_abs z H μ hz
  have hl := neg_abs_le (∑ k, z k * μ k)
  linarith

/-- An affine combination of row curvature bounds has a certified uniform
upper bound on the whole box, not just at sampled points. -/
theorem affine_curvature_mass {Params Rows : Type*} [Fintype Params] [Fintype Rows]
    (z H : Params → ℝ) (lam K : Rows → ℝ) (μ : Params → Rows → ℝ) (M : ℝ)
    (hz : ∀ k, |z k| ≤ H k)
    (hM : (∑ i, lam i * K i) + ∑ k, H k * |∑ i, μ k i * K i| ≤ M) :
    ∑ i, (lam i + ∑ k, z k * μ k i) * K i ≤ M := by
  have hb := box_pairing_abs z H (fun k => ∑ i, μ k i * K i) hz
  have he : (∑ i, (lam i + ∑ k, z k * μ k i) * K i) =
      (∑ i, lam i * K i) + ∑ k, z k * (∑ i, μ k i * K i) := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul,
      Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  rw [he]
  have hl := le_abs_self (∑ k, z k * (∑ i, μ k i * K i))
  linarith

/-- A scalar quadratic polynomial admits the coefficientwise centered-box
bound used by the local dual certificate. -/
theorem quadratic_box_abs {ι : Type*} [Fintype ι]
    (z H b : ι → ℝ) (a : ℝ) (c : ι → ι → ℝ)
    (hz : ∀ k, |z k| ≤ H k) :
    |a + (∑ k, z k * b k) + ∑ k, ∑ l, (z k * z l) * c k l| ≤
      |a| + (∑ k, H k * |b k|) + ∑ k, ∑ l, (H k * H l) * |c k l| := by
  have hH : ∀ k, 0 ≤ H k := fun k => (abs_nonneg _).trans (hz k)
  have hprod : ∀ p : ι × ι, |z p.1 * z p.2| ≤ H p.1 * H p.2 := by
    intro p
    rw [abs_mul]
    exact mul_le_mul (hz p.1) (hz p.2) (abs_nonneg _) (hH _)
  have hb := box_pairing_abs z H b hz
  have hc := box_pairing_abs (fun p : ι × ι => z p.1 * z p.2)
    (fun p : ι × ι => H p.1 * H p.2) (fun p : ι × ι => c p.1 p.2) hprod
  simp only [Fintype.sum_prod_type] at hc
  have h1 := abs_add_le a (∑ k, z k * b k)
  have h2 := abs_add_le (a + ∑ k, z k * b k)
    (∑ k, ∑ l, (z k * z l) * c k l)
  linarith

end Sq17.LocalRigidity
#print axioms Sq17.LocalRigidity.affine_weight_nonnegative
#print axioms Sq17.LocalRigidity.affine_curvature_mass
#print axioms Sq17.LocalRigidity.quadratic_box_abs
