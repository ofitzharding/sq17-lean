import Sq17Lean.LocalRigidityWeightCheck

namespace Sq17.LocalRigidity
open scoped BigOperators

/-- A certificate with row coefficients at least one also bounds the mass
for any nonnegative universal curvature constant. The coarser bound avoids
rechecking the same affine weights when using a simpler Taylor estimate. -/
theorem universal_curvature_mass {Rows : Type*} [Fintype Rows]
    (weights K : Rows → ℝ) (κ M : ℝ)
    (hw : ∀ i, 0 ≤ weights i) (hK : ∀ i, 1 ≤ K i)
    (hκ : 0 ≤ κ) (hmass : ∑ i, weights i * K i ≤ M) :
    ∑ i, weights i * κ ≤ κ * M := by
  have hsum : (∑ i, weights i) ≤ M := by
    calc
      (∑ i, weights i) ≤ ∑ i, weights i * K i :=
        Finset.sum_le_sum (fun i _ => by nlinarith [hw i, hK i])
      _ ≤ M := hmass
  rw [← Finset.sum_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left hsum hκ

end Sq17.LocalRigidity
#print axioms Sq17.LocalRigidity.universal_curvature_mass
