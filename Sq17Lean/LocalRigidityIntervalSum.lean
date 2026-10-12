import Sq17Lean.RationalExpression
import Sq17Lean.LocalRigidityResidual

namespace Sq17.LocalRigidity
open scoped BigOperators
open Sq17.RationalExpression

def intervalSum {ι : Type*} [Fintype ι] (f : ι → Interval) : Interval :=
  ⟨∑ i, (f i).lo, ∑ i, (f i).hi⟩

theorem intervalSum_sound {ι : Type*} [Fintype ι]
    (f : ι → Interval) (v : ι → ℝ) (hv : ∀ i, (f i).Holds (v i)) :
    (intervalSum f).Holds (∑ i, v i) := by
  constructor
  · change ((∑ i, (f i).lo : ℚ) : ℝ) ≤ _
    push_cast
    exact Finset.sum_le_sum (fun i _ => (hv i).1)
  · change _ ≤ ((∑ i, (f i).hi : ℚ) : ℝ)
    push_cast
    exact Finset.sum_le_sum (fun i _ => (hv i).2)

def intervalScale (q : ℚ) (i : Interval) : Interval :=
  (⟨q,q⟩ : Interval).mul i

theorem intervalScale_sound (q : ℚ) (i : Interval) (x : ℝ) (hx : i.Holds x) :
    (intervalScale q i).Holds ((q : ℝ)*x) :=
  Interval.mul_sound _ _ _ _ ⟨le_rfl,le_rfl⟩ hx

def intervalAbsBound (i : Interval) : ℚ := max |i.lo| |i.hi|

theorem intervalAbsBound_sound (i : Interval) (x : ℝ) (hx : i.Holds x) :
    |x| ≤ (intervalAbsBound i : ℝ) := (Interval.abs_sound i x hx).2

def intervalDot {ι : Type*} [Fintype ι]
    (q : ι → ℚ) (v : ι → Interval) : Interval :=
  intervalSum (fun i => intervalScale (q i) (v i))

theorem intervalDot_sound {ι : Type*} [Fintype ι]
    (q : ι → ℚ) (v : ι → Interval) (x : ι → ℝ)
    (hx : ∀ i, (v i).Holds (x i)) :
    (intervalDot q v).Holds (∑ i, (q i : ℝ)*x i) :=
  intervalSum_sound _ _ (fun i => intervalScale_sound _ _ _ (hx i))

def residualIntervalBudget {Params Cols : Type*} [Fintype Params] [Fintype Cols]
    (H : Params → ℚ) (a : Cols → Interval) (b : Params → Cols → Interval)
    (c : Params → Params → Cols → Interval) : ℚ :=
  (∑ j, intervalAbsBound (a j)) + (∑ k, H k * (∑ j, intervalAbsBound (b k j))) +
    ∑ k, ∑ l, (H k * H l) * (∑ j, intervalAbsBound (c k l j))

theorem residualIntervalBudget_sound {Params Cols : Type*}
    [Fintype Params] [Fintype Cols]
    (H : Params → ℚ) (aB : Cols → Interval) (bB : Params → Cols → Interval)
    (cB : Params → Params → Cols → Interval)
    (z : Params → ℝ) (a : Cols → ℝ) (b : Params → Cols → ℝ)
    (c : Params → Params → Cols → ℝ) (ε : ℚ)
    (hz : ∀ k, |z k| ≤ (H k : ℝ))
    (ha : ∀ j, (aB j).Holds (a j))
    (hb : ∀ k j, (bB k j).Holds (b k j))
    (hc : ∀ k l j, (cB k l j).Holds (c k l j))
    (hcheck : residualIntervalBudget H aB bB cB ≤ ε) :
    (∑ j, |a j + (∑ k, z k*b k j) + ∑ k, ∑ l, (z k*z l)*c k l j|) ≤ (ε : ℝ) := by
  have hH : ∀ k, (0 : ℝ) ≤ H k := fun k => (abs_nonneg _).trans (hz k)
  apply quadratic_residual_bound z (fun k => (H k : ℝ)) a b c (ε : ℝ) hz
  have hbound : ((∑ j, |a j|) + (∑ k, (H k : ℝ)*(∑ j, |b k j|)) +
      (∑ k, ∑ l, ((H k : ℝ)*H l)*(∑ j, |c k l j|))) ≤
      (residualIntervalBudget H aB bB cB : ℝ) := by
    unfold residualIntervalBudget
    push_cast
    gcongr <;> first
    | exact hH _
    | exact mul_nonneg (hH _) (hH _)
    | exact intervalAbsBound_sound _ _ (ha _)
    | exact intervalAbsBound_sound _ _ (hb _ _)
    | exact intervalAbsBound_sound _ _ (hc _ _ _)
  exact hbound.trans (by exact_mod_cast hcheck)

end Sq17.LocalRigidity
#print axioms Sq17.LocalRigidity.intervalSum_sound
