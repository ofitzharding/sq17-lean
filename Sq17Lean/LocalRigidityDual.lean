import Sq17Lean.LocalRigidityRatio
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! The dual implication used by local rigidity. Matrix rows and their
geometric lower bounds are explicit inputs. No contact geometry is assumed
by a hidden axiom, and no finite certificate is declared accepted here. -/
namespace Sq17.LocalRigidity
open scoped BigOperators

/-- The elementary L1/L-infinity pairing estimate, over any finite index set. -/
theorem dual_pairing_bound {ι : Type*} [Fintype ι]
    (v h : ι → ℝ) (q ε : ℝ) (hq : 0 ≤ q)
    (hh : ∀ j, |h j| ≤ q) (hv : ∑ j, |v j| ≤ ε) :
    ∑ j, v j * h j ≤ ε * q := by
  calc
    ∑ j, v j * h j ≤ ∑ j, |v j * h j| :=
      Finset.sum_le_sum (fun j _ => le_abs_self _)
    _ = ∑ j, |v j| * |h j| := by simp_rw [abs_mul]
    _ ≤ ∑ j, |v j| * q :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hh j) (abs_nonneg _))
    _ = (∑ j, |v j|) * q := (Finset.sum_mul ..).symm
    _ ≤ ε * q := mul_le_mul_of_nonneg_right hv hq

/-- A nonnegative dual combines necessary rows, and its residual is bounded
in L1. This derives the linear-functional inequality needed for saturation. -/
theorem weighted_dual_bound {Rows Cols : Type*} [Fintype Rows] [Fintype Cols]
    (A : Rows → Cols → ℝ) (weights K : Rows → ℝ) (d h : Cols → ℝ)
    (q ε M t : ℝ) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hw : ∀ i, 0 ≤ weights i)
    (hh : ∀ j, |h j| ≤ q)
    (hrows : ∀ i, -t * K i ≤ ∑ j, A i j * h j)
    (hmass : ∑ i, weights i * K i ≤ M)
    (hresidual : ∑ j, |(∑ i, weights i * A i j) + d j| ≤ ε) :
    ∑ j, d j * h j ≤ ε * q + t * M := by
  have hb := dual_pairing_bound (fun j => (∑ i, weights i * A i j) + d j)
    h q ε hq hh hresidual
  have heq : (∑ j, ((∑ i, weights i * A i j) + d j) * h j) =
      (∑ i, weights i * (∑ j, A i j * h j)) + ∑ j, d j * h j := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul,
      Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  have hlo : -t * (∑ i, weights i * K i) ≤
      ∑ i, weights i * (∑ j, A i j * h j) := by
    calc
      -t * (∑ i, weights i * K i) = ∑ i, weights i * (-t * K i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i, weights i * (∑ j, A i j * h j) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hrows i) (hw i))
  have hm := mul_le_mul_of_nonneg_left hmass ht
  rw [heq] at hb
  nlinarith

/-- A saturated coordinate (or other linear functional) cannot be nonzero
when its checked dual budget is strict. Unlike `saturation_zero`, the necessary
scalar inequality is derived from the complete finite row/dual premises. -/
theorem weighted_dual_saturation {Rows Cols : Type*} [Fintype Rows] [Fintype Cols]
    (A : Rows → Cols → ℝ) (weights K : Rows → ℝ) (d h : Cols → ℝ)
    (τ r ε M : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hw : ∀ i, 0 ≤ weights i) (hh : ∀ j, |h j| ≤ τ * r)
    (hrows : ∀ i, -(τ ^ 2 * r ^ 2 / 2) * K i ≤ ∑ j, A i j * h j)
    (hmass : ∑ i, weights i * K i ≤ M)
    (hresidual : ∑ j, |(∑ i, weights i * A i j) + d j| ≤ ε)
    (hsaturated : ∑ j, d j * h j = τ * r)
    (hbudget : r ^ 2 * M < 2 * (r - ε * r)) : τ = 0 := by
  have h := weighted_dual_bound A weights K d h (τ*r) ε M (τ^2*r^2/2)
    (mul_nonneg hτ0 hr) (by positivity) hw hh hrows hmass hresidual
  rw [hsaturated] at h
  apply saturation_zero τ r ε (r^2*M) hτ0 hτ1 (mul_nonneg (sq_nonneg _) hM) hbudget
  nlinarith

end Sq17.LocalRigidity
#print axioms Sq17.LocalRigidity.dual_pairing_bound
#print axioms Sq17.LocalRigidity.weighted_dual_bound
#print axioms Sq17.LocalRigidity.weighted_dual_saturation
