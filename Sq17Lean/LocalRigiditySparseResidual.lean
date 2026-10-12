import Sq17Lean.LocalRigidityResidualCheck

namespace Sq17.LocalRigidity
open scoped BigOperators
open Sq17.RationalExpression

abbrev LocalMatrixSupport := Fin 4 → Fin 45 → Finset (Fin 52)

def sparseDot (B : LocalIntervalMatrix) (S : LocalMatrixSupport)
    (k : Fin 4) (q : Fin 52 → ℚ) (j : Fin 45) : Interval :=
  ⟨∑ i ∈ S k j, (intervalScale (q i) (B k i j)).lo,
   ∑ i ∈ S k j, (intervalScale (q i) (B k i j)).hi⟩

theorem sparseDot_sound (B : LocalIntervalMatrix) (M : LocalRealMatrix)
    (S : LocalMatrixSupport) (hM : ∀ k i j, (B k i j).Holds (M k i j))
    (hS : ∀ k j i, i ∉ S k j → B k i j = ⟨0,0⟩)
    (k : Fin 4) (q : Fin 52 → ℚ) (j : Fin 45) :
    (sparseDot B S k q j).Holds (∑ i, (q i : ℝ)*M k i j) := by
  have he : (∑ i ∈ S k j, (q i : ℝ)*M k i j) = ∑ i, (q i : ℝ)*M k i j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hz := hM k i j
    rw [hS k j i hi] at hz
    simp only [Interval.Holds, Rat.cast_zero] at hz
    have hz' : M k i j = 0 := le_antisymm hz.2 hz.1
    rw [hz',mul_zero]
  rw [← he]
  constructor
  · change ((∑ i ∈ S k j, (intervalScale (q i) (B k i j)).lo : ℚ) : ℝ) ≤ _
    push_cast
    exact Finset.sum_le_sum (fun i _ => (intervalScale_sound _ _ _ (hM k i j)).1)
  · change _ ≤ ((∑ i ∈ S k j, (intervalScale (q i) (B k i j)).hi : ℚ) : ℝ)
    push_cast
    exact Finset.sum_le_sum (fun i _ => (intervalScale_sound _ _ _ (hM k i j)).2)

def sparseCenterDot (B : LocalIntervalMatrix) (S : LocalMatrixSupport)
    (q : Fin 52 → ℚ) (mid : Fin 3 → ℚ) (j : Fin 45) : Interval :=
  (sparseDot B S 0 q j).add (intervalDot mid (fun k => sparseDot B S k.succ q j))

theorem sparseCenterDot_sound (B : LocalIntervalMatrix) (M : LocalRealMatrix)
    (S : LocalMatrixSupport) (hM : ∀ k i j, (B k i j).Holds (M k i j))
    (hS : ∀ k j i, i ∉ S k j → B k i j = ⟨0,0⟩)
    (q : Fin 52 → ℚ) (mid : Fin 3 → ℚ) (j : Fin 45) :
    (sparseCenterDot B S q mid j).Holds (∑ i, (q i : ℝ)*centerReal M mid i j) := by
  have he : (∑ i, (q i : ℝ)*centerReal M mid i j) =
      (∑ i, (q i : ℝ)*M 0 i j)+∑ k, (mid k : ℝ)*(∑ i, (q i : ℝ)*M k.succ i j) := by
    simp only [centerReal,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  exact Interval.add_sound _ _ _ _ (sparseDot_sound B M S hM hS 0 q j)
    (intervalDot_sound mid _ _ (fun k => sparseDot_sound B M S hM hS k.succ q j))

def sparseConstant (B : LocalIntervalMatrix) (S : LocalMatrixSupport)
    (c : AffineWeightCertificate 52 3) (mid : Fin 3 → ℚ) (target : Fin 45 → ℚ)
    (j : Fin 45) : Interval :=
  (sparseCenterDot B S c.base mid j).add ⟨target j,target j⟩

def sparseLinear (B : LocalIntervalMatrix) (S : LocalMatrixSupport)
    (c : AffineWeightCertificate 52 3) (mid : Fin 3 → ℚ) (k : Fin 3) (j : Fin 45) : Interval :=
  (sparseCenterDot B S (c.slope k) mid j).add (sparseDot B S k.succ c.base j)

def sparseQuadratic (B : LocalIntervalMatrix) (S : LocalMatrixSupport)
    (c : AffineWeightCertificate 52 3) (k l : Fin 3) (j : Fin 45) : Interval :=
  sparseDot B S l.succ (c.slope k) j

def sparseResidualCheck (B : LocalIntervalMatrix) (S : LocalMatrixSupport)
    (c : AffineWeightCertificate 52 3) (mid : Fin 3 → ℚ) (target : Fin 45 → ℚ) : Bool :=
  decide (residualIntervalBudget c.half (sparseConstant B S c mid target)
    (sparseLinear B S c mid) (sparseQuadratic B S c) ≤ 1/4)

theorem sparseResidualCheck_weighted (B : LocalIntervalMatrix) (M : LocalRealMatrix)
    (S : LocalMatrixSupport) (hM : ∀ k i j, (B k i j).Holds (M k i j))
    (hS : ∀ k j i, i ∉ S k j → B k i j = ⟨0,0⟩)
    (c : AffineWeightCertificate 52 3) (mid : Fin 3 → ℚ)
    (target : Fin 45 → ℚ) (hc : sparseResidualCheck B S c mid target = true)
    (z : Fin 3 → ℝ) (hz : ∀ k, |z k| ≤ (c.half k : ℝ)) :
    (∑ j, |(∑ i, dualWeights c z i *
      matrixFamily M (fun k => (mid k : ℝ)+z k) i j) + (target j : ℝ)|) ≤ (1/4 : ℝ) := by
  have he (j : Fin 45) : (∑ i, dualWeights c z i *
      matrixFamily M (fun k => (mid k : ℝ)+z k) i j) + (target j : ℝ) =
      constantReal M c mid target j + (∑ k, z k*linearReal M c mid k j) +
      ∑ k, ∑ l, (z k*z l)*quadraticReal M c k l j := by
    simp only [dualWeights,matrixFamily_centered,constantReal,linearReal,quadraticReal]
    exact affine_weight_matrix_expansion z (fun i => (c.base i : ℝ))
      (fun i => centerReal M mid i j) (fun k i => (c.slope k i : ℝ))
      (fun k i => M k.succ i j) (target j : ℝ)
  simp_rw [he]
  have hrat : ((1/4 : ℚ) : ℝ) = 1/4 := by norm_num
  rw [← hrat]
  apply residualIntervalBudget_sound c.half
    (sparseConstant B S c mid target) (sparseLinear B S c mid)
    (sparseQuadratic B S c) z (constantReal M c mid target)
    (linearReal M c mid) (quadraticReal M c) (1/4) hz
  · intro j
    exact Interval.add_sound _ _ _ _
      (sparseCenterDot_sound B M S hM hS c.base mid j) ⟨le_rfl,le_rfl⟩
  · intro k j
    exact Interval.add_sound _ _ _ _
      (sparseCenterDot_sound B M S hM hS (c.slope k) mid j)
      (sparseDot_sound B M S hM hS k.succ c.base j)
  · intro k l j
    exact sparseDot_sound B M S hM hS l.succ (c.slope k) j
  · exact of_decide_eq_true hc

end Sq17.LocalRigidity
#print axioms Sq17.LocalRigidity.sparseResidualCheck_weighted
