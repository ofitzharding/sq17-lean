import Sq17Lean.LocalRigidityIntervalSum
import Sq17Lean.LocalRigidityWeightCheck
import Sq17Lean.LocalRigidityAffineExpansion

namespace Sq17.LocalRigidity
open scoped BigOperators
open Sq17.RationalExpression

abbrev LocalIntervalMatrix := Fin 4 → Fin 52 → Fin 45 → Interval
abbrev LocalRealMatrix := Fin 4 → Fin 52 → Fin 45 → ℝ

def centerIntervals (M : LocalIntervalMatrix) (mid : Fin 3 → ℚ) (i : Fin 52) (j : Fin 45) : Interval :=
  (M 0 i j).add (intervalDot mid (fun k => M k.succ i j))

noncomputable def centerReal (M : LocalRealMatrix) (mid : Fin 3 → ℚ) (i : Fin 52) (j : Fin 45) : ℝ :=
  M 0 i j + ∑ k, (mid k : ℝ)*M k.succ i j

def constantIntervals (M : LocalIntervalMatrix) (c : AffineWeightCertificate 52 3)
    (mid : Fin 3 → ℚ) (target : Fin 45 → ℚ) (j : Fin 45) : Interval :=
  (intervalDot c.base (fun i => centerIntervals M mid i j)).add ⟨target j,target j⟩

def linearIntervals (M : LocalIntervalMatrix) (c : AffineWeightCertificate 52 3)
    (mid : Fin 3 → ℚ) (k : Fin 3) (j : Fin 45) : Interval :=
  (intervalDot (c.slope k) (fun i => centerIntervals M mid i j)).add
    (intervalDot c.base (fun i => M k.succ i j))

def quadraticIntervals (M : LocalIntervalMatrix) (c : AffineWeightCertificate 52 3)
    (k l : Fin 3) (j : Fin 45) : Interval :=
  intervalDot (c.slope k) (fun i => M l.succ i j)

def localResidualCheck (M : LocalIntervalMatrix) (c : AffineWeightCertificate 52 3)
    (mid : Fin 3 → ℚ) (target : Fin 45 → ℚ) : Bool :=
  decide (residualIntervalBudget c.half (constantIntervals M c mid target)
    (linearIntervals M c mid) (quadraticIntervals M c) ≤ 1/4)

noncomputable def constantReal (M : LocalRealMatrix) (c : AffineWeightCertificate 52 3)
    (mid : Fin 3 → ℚ) (target : Fin 45 → ℚ) (j : Fin 45) : ℝ :=
  (∑ i, (c.base i : ℝ)*centerReal M mid i j) + (target j : ℝ)

noncomputable def linearReal (M : LocalRealMatrix) (c : AffineWeightCertificate 52 3)
    (mid : Fin 3 → ℚ) (k : Fin 3) (j : Fin 45) : ℝ :=
  (∑ i, (c.slope k i : ℝ)*centerReal M mid i j) +
    ∑ i, (c.base i : ℝ)*M k.succ i j

noncomputable def quadraticReal (M : LocalRealMatrix) (c : AffineWeightCertificate 52 3)
    (k l : Fin 3) (j : Fin 45) : ℝ :=
  ∑ i, (c.slope k i : ℝ)*M l.succ i j

theorem centerIntervals_sound (B : LocalIntervalMatrix) (M : LocalRealMatrix)
    (hM : ∀ k i j, (B k i j).Holds (M k i j))
    (mid : Fin 3 → ℚ) (i : Fin 52) (j : Fin 45) :
    (centerIntervals B mid i j).Holds (centerReal M mid i j) :=
  Interval.add_sound _ _ _ _ (hM 0 i j)
    (intervalDot_sound mid _ _ (fun k => hM k.succ i j))

/-- A checked rational coefficient budget gives the real quadratic residual
bound for every centered slider point in its box. -/
theorem localResidualCheck_sound (B : LocalIntervalMatrix) (M : LocalRealMatrix)
    (hM : ∀ k i j, (B k i j).Holds (M k i j))
    (c : AffineWeightCertificate 52 3) (mid : Fin 3 → ℚ)
    (target : Fin 45 → ℚ) (hc : localResidualCheck B c mid target = true)
    (z : Fin 3 → ℝ) (hz : ∀ k, |z k| ≤ (c.half k : ℝ)) :
    (∑ j, |constantReal M c mid target j + (∑ k, z k*linearReal M c mid k j) +
      ∑ k, ∑ l, (z k*z l)*quadraticReal M c k l j|) ≤ (1/4 : ℝ) := by
  have hcenter := centerIntervals_sound B M hM mid
  have hrat : ((1/4 : ℚ) : ℝ) = 1/4 := by norm_num
  rw [← hrat]
  apply residualIntervalBudget_sound c.half
    (constantIntervals B c mid target) (linearIntervals B c mid)
    (quadraticIntervals B c) z (constantReal M c mid target)
    (linearReal M c mid) (quadraticReal M c) (1/4) hz
  · intro j
    exact Interval.add_sound _ _ _ _
      (intervalDot_sound c.base _ _ (fun i => hcenter i j)) ⟨le_rfl,le_rfl⟩
  · intro k j
    exact Interval.add_sound _ _ _ _
      (intervalDot_sound (c.slope k) _ _ (fun i => hcenter i j))
      (intervalDot_sound c.base _ _ (fun i => hM k.succ i j))
  · intro k l j
    exact intervalDot_sound (c.slope k) _ _ (fun i => hM l.succ i j)
  · exact of_decide_eq_true hc

noncomputable def matrixFamily (M : LocalRealMatrix) (w : Fin 3 → ℝ)
    (i : Fin 52) (j : Fin 45) : ℝ := M 0 i j + ∑ k, w k*M k.succ i j

noncomputable def dualWeights (c : AffineWeightCertificate 52 3)
    (z : Fin 3 → ℝ) (i : Fin 52) : ℝ := (c.base i : ℝ) + ∑ k, z k*(c.slope k i : ℝ)

theorem matrixFamily_centered (M : LocalRealMatrix) (mid : Fin 3 → ℚ)
    (z : Fin 3 → ℝ) (i : Fin 52) (j : Fin 45) :
    matrixFamily M (fun k => (mid k : ℝ)+z k) i j =
      centerReal M mid i j + ∑ k, z k*M k.succ i j := by
  simp only [matrixFamily,centerReal,add_mul,Finset.sum_add_distrib]
  ring

/-- The checker bounds the actual affine-weight/matrix residual, after the
finite algebraic coefficient expansion has been proved generically. -/
theorem localResidualCheck_weighted (B : LocalIntervalMatrix) (M : LocalRealMatrix)
    (hM : ∀ k i j, (B k i j).Holds (M k i j))
    (c : AffineWeightCertificate 52 3) (mid : Fin 3 → ℚ)
    (target : Fin 45 → ℚ) (hc : localResidualCheck B c mid target = true)
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
  exact localResidualCheck_sound B M hM c mid target hc z hz

end Sq17.LocalRigidity
#print axioms Sq17.LocalRigidity.localResidualCheck_sound
#print axioms Sq17.LocalRigidity.localResidualCheck_weighted
