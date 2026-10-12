import Mathlib.Tactic
import Mathlib.Basic.Real.Basic

/-! The saturation step in the independent small-radius local rigidity proof.
The geometric inequalities and dual certificates are external to this module. -/
namespace Sq17.LocalRigidity

/-- A strict dual/curvature budget forces the normalized perturbation to vanish. -/
theorem saturation_zero (τ r ε M : ℝ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hM : 0 ≤ M)
    (hbudget : M < 2 * (r - ε * r))
    (hnecessary : τ * r ≤ ε * τ * r + τ^2 * M / 2) : τ = 0 := by
  by_contra hne
  have hτ : 0 < τ := lt_of_le_of_ne hτ0 (Ne.symm hne)
  have hgap : 0 < r - ε * r - M / 2 := by linarith
  have hstrict := mul_pos hτ hgap
  have hquad : 0 ≤ τ * M * (1 - τ) :=
    mul_nonneg (mul_nonneg hτ0 hM) (by linarith)
  nlinarith

end Sq17.LocalRigidity

#print axioms Sq17.LocalRigidity.saturation_zero
