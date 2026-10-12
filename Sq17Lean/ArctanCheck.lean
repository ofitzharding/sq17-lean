import Sq17Lean.RationalExpression
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecificLimits.Normed

/-! A finite rational arctangent enclosure checker, justified by the
alternating-series remainder estimate. No numerical transcendental oracle
or pre-existing enclosure is assumed. -/
namespace Sq17.ArctanCheck
open scoped BigOperators
open Sq17.RationalExpression

noncomputable def term (x : ℝ) (n : ℕ) : ℝ := x^(2*n+1)/(2*n+1)
noncomputable def partialSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1:ℝ)^k*x^(2*k+1)/(2*k+1)

theorem term_antitone (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : Antitone (term x) := by
  intro i j hij
  have hp := pow_le_pow_of_le_one hx0 hx1 (show 2*i+1 ≤ 2*j+1 by omega)
  have hd : (2*i+1:ℝ) ≤ 2*j+1 := by
    have hreal : (i:ℝ) ≤ j := by exact_mod_cast hij
    linarith
  have hi : (0:ℝ) < 2*i+1 := by positivity
  have hj : (0:ℝ) < 2*j+1 := by positivity
  unfold term
  calc
    x^(2*j+1)/(2*j+1) ≤ x^(2*i+1)/(2*j+1) := div_le_div_of_nonneg_right hp hj.le
    _ ≤ x^(2*i+1)/(2*i+1) := (div_le_div_iff₀ hj hi).2
      (mul_le_mul_of_nonneg_left hd (pow_nonneg hx0 _))

theorem term_summable (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) : Summable (term x) := by
  apply Summable.of_nonneg_of_le (fun n => div_nonneg (pow_nonneg hx0 _) (by positivity))
    (fun n => ?_) (summable_geometric_of_lt_one hx0 hx1)
  have hp := pow_le_pow_of_le_one hx0 hx1.le (show n ≤ 2*n+1 by omega)
  have hd : (1:ℝ) ≤ 2*n+1 := by
    have hn : (0:ℝ) ≤ n := by positivity
    linarith
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*n+1)).2
  nlinarith [mul_nonneg (pow_nonneg hx0 n) (sub_nonneg.mpr hd)]

theorem partial_error (n : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    |Real.arctan x-partialSum n x| ≤ term x n := by
  have hs : HasSum (fun k => (-1:ℝ)^k*term x k) (Real.arctan x) := by
    simpa only [term,mul_div_assoc,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] using
      (Real.hasSum_arctan (x := x) (by simpa only [Real.norm_eq_abs,abs_of_nonneg hx0] using hx1))
  have hb := alternating_series_error_bound (term x) (term_antitone x hx0 hx1.le)
    (term_summable x hx0 hx1) n
  rw [hs.tsum_eq] at hb
  simpa only [partialSum,term,mul_div_assoc] using hb

def partialQ (n : ℕ) (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range n, (-1:ℚ)^k*x^(2*k+1)/(2*k+1)
def errorQ (n : ℕ) (x : ℚ) : ℚ := x^(2*n+1)/(2*n+1)

@[simp] theorem partialQ_cast (n : ℕ) (x : ℚ) : (partialQ n x : ℝ) = partialSum n (x:ℝ) := by
  unfold partialQ partialSum
  push_cast <;> rfl

@[simp] theorem errorQ_cast (n : ℕ) (x : ℚ) : (errorQ n x : ℝ) = term (x:ℝ) n := by
  unfold errorQ term
  push_cast <;> rfl

structure Certificate where
  terms : ℕ
  input : Interval
  output : Interval
  deriving DecidableEq

def Certificate.check (C : Certificate) : Bool := decide
  (0 ≤ C.input.lo ∧ C.input.lo ≤ C.input.hi ∧ C.input.hi < 1 ∧
    C.output.lo ≤ partialQ C.terms C.input.lo-errorQ C.terms C.input.lo ∧
    partialQ C.terms C.input.hi+errorQ C.terms C.input.hi ≤ C.output.hi)

theorem Certificate.check_sound (C : Certificate) (x : ℝ)
    (hx : C.input.Holds x) (hc : C.check = true) : C.output.Holds (Real.arctan x) := by
  obtain ⟨h0,hord,h1,hlo,hhi⟩ := of_decide_eq_true hc
  have hr0 : (0:ℝ) ≤ C.input.lo := by exact_mod_cast h0
  have hrord : (C.input.lo:ℝ) ≤ C.input.hi := by exact_mod_cast hord
  have hr1 : (C.input.hi:ℝ) < 1 := by exact_mod_cast h1
  have hl := partial_error C.terms C.input.lo hr0 (hrord.trans_lt hr1)
  have hu := partial_error C.terms C.input.hi (hr0.trans hrord) hr1
  have hlo' : (C.output.lo:ℝ) ≤ ((partialQ C.terms C.input.lo-errorQ C.terms C.input.lo:ℚ):ℝ) := by
    exact_mod_cast hlo
  have hhi' : ((partialQ C.terms C.input.hi+errorQ C.terms C.input.hi:ℚ):ℝ) ≤ C.output.hi := by
    exact_mod_cast hhi
  simp only [Rat.cast_sub,Rat.cast_add,partialQ_cast,errorQ_cast] at hlo' hhi'
  have hmlo := Real.arctan_le_arctan_iff.mpr hx.1
  have hmhi := Real.arctan_le_arctan_iff.mpr hx.2
  have hll := (abs_le.mp hl).1
  have huu := (abs_le.mp hu).2
  constructor <;> linarith

end Sq17.ArctanCheck
#print axioms Sq17.ArctanCheck.partial_error
#print axioms Sq17.ArctanCheck.Certificate.check_sound
