import Sq17Lean.LocalRigidityDual
import Mathlib.Data.Finset.Max

namespace Sq17.LocalRigidity
open scoped BigOperators

noncomputable def maxCoordinate (h : Fin 45 → ℝ) : Fin 45 :=
  Classical.choose (Finset.exists_max_image Finset.univ (fun j => |h j|) Finset.univ_nonempty)

noncomputable def maxAbs (h : Fin 45 → ℝ) : ℝ := |h (maxCoordinate h)|

theorem le_maxAbs (h : Fin 45 → ℝ) (j : Fin 45) : |h j| ≤ maxAbs h :=
  (Classical.choose_spec (Finset.exists_max_image Finset.univ (fun j => |h j|)
    Finset.univ_nonempty)).2 j (Finset.mem_univ j)

def signedCoordinate (j : Fin 45) (s : ℝ) (k : Fin 45) : ℝ := if k = j then s else 0

/-- Finite coordinate maximization closes the local dual argument without a
separate scale parameter or a supplied saturated-coordinate hypothesis. -/
theorem all_zero_of_signed_duals (A : Fin 52 → Fin 45 → ℝ) (h : Fin 45 → ℝ)
    (hlocal : ∀ j, |h j| ≤ (1/10000000 : ℝ))
    (hrows : ∀ i, -50*(maxAbs h)^2 ≤ ∑ j, A i j*h j)
    (hduals : ∀ j s, s = 1 ∨ s = -1 → ∃ weights : Fin 52 → ℝ,
      (∀ i, 0 ≤ weights i) ∧ (∑ i, weights i*100) ≤ 1200000 ∧
      (∑ k, |(∑ i, weights i*A i k)+signedCoordinate j s k|) ≤ 1/4) :
    ∀ j, h j = 0 := by
  classical
  let j := maxCoordinate h
  let s : ℝ := if 0 ≤ h j then 1 else -1
  have hs : s = 1 ∨ s = -1 := by dsimp [s]; split_ifs <;> simp
  obtain ⟨weights,hw,hm,hr⟩ := hduals j s hs
  have hq : 0 ≤ maxAbs h := abs_nonneg _
  have hqr : maxAbs h ≤ (1/10000000 : ℝ) := hlocal j
  have hsat : (∑ k, signedCoordinate j s k*h k) = maxAbs h := by
    simp only [signedCoordinate,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    dsimp [s,maxAbs,j]
    split_ifs with hpos
    · simp [abs_of_nonneg hpos]
    · simp [abs_of_neg (lt_of_not_ge hpos)]
  have hn := weighted_dual_bound A weights (fun _ => 100) (signedCoordinate j s) h
    (maxAbs h) (1/4) 1200000 ((maxAbs h)^2/2) hq (by positivity) hw
    (le_maxAbs h) (fun i => by nlinarith [hrows i]) hm hr
  rw [hsat] at hn
  have hqzero : maxAbs h = 0 := by
    have hsq := mul_le_mul_of_nonneg_left hqr hq
    nlinarith
  intro k
  have hk := le_maxAbs h k
  rw [hqzero] at hk
  exact abs_eq_zero.mp (le_antisymm hk (abs_nonneg _))

end Sq17.LocalRigidity
#print axioms Sq17.LocalRigidity.all_zero_of_signed_duals
