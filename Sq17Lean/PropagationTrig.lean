import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Rational Taylor polynomials and rigorous sine/cosine remainder bounds.
These are the mathematical enclosures behind the trace kernel's degree-44
calculation. Reported dyadic bounds are treated as untrusted data and checked
against these polynomials; correctness of the Python generator is not assumed. -/
namespace Sq17.Propagation

def trigCoeff : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n+1 => (-(trigCoeff n).2, (trigCoeff n).1)

def cosTaylor (n : ℕ) (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range (n+1), (trigCoeff k).1 * x^k / (k.factorial : ℚ)

def sinTaylor (n : ℕ) (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range (n+1), (trigCoeff k).2 * x^k / (k.factorial : ℚ)

theorem trigCoeff_sound (n : ℕ) :
    ((trigCoeff n).1 : ℝ) = iteratedDeriv n Real.cos 0 ∧
    ((trigCoeff n).2 : ℝ) = iteratedDeriv n Real.sin 0 := by
  induction n with
  | zero => simp [trigCoeff]
  | succ n ih =>
    simp only [trigCoeff, Rat.cast_neg, Real.iteratedDeriv_add_one_cos,
      Real.iteratedDeriv_add_one_sin, Pi.neg_apply]
    exact ⟨congrArg Neg.neg ih.2, ih.1⟩

theorem cosTaylor_eq (n : ℕ) (x : ℚ) (hx : (x : ℝ) ≠ 0) :
    (cosTaylor n x : ℝ) =
      taylorWithinEval Real.cos n (Set.uIcc 0 (x : ℝ)) 0 x := by
  rw [taylor_within_apply]
  unfold cosTaylor
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (Ne.symm hx))
    Real.contDiff_cos.contDiffAt Set.left_mem_uIcc, ← (trigCoeff_sound k).1]
  simp only [sub_zero, smul_eq_mul]
  ring

theorem sinTaylor_eq (n : ℕ) (x : ℚ) (hx : (x : ℝ) ≠ 0) :
    (sinTaylor n x : ℝ) =
      taylorWithinEval Real.sin n (Set.uIcc 0 (x : ℝ)) 0 x := by
  rw [taylor_within_apply]
  unfold sinTaylor
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (Ne.symm hx))
    Real.contDiff_sin.contDiffAt Set.left_mem_uIcc, ← (trigCoeff_sound k).2]
  simp only [sub_zero, smul_eq_mul]
  ring

theorem taylor_remainder_abs (f : ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hf : ContDiff ℝ (n+1) f) (hd : ∀ y, |iteratedDeriv (n+1) f y| ≤ 1) :
    |f x - taylorWithinEval f n (Set.uIcc 0 x) 0 x| ≤
      |x|^(n+1) / ((n+1).factorial : ℝ) := by
  by_cases hx : x = 0
  · subst x
    simp
  obtain ⟨y, _, hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (Ne.symm hx) hf.contDiffOn
  rw [hy, sub_zero, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  exact div_le_div_of_nonneg_right
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (hd y) (by positivity : 0 ≤ |x|^(n+1)))
    (by positivity)

theorem cosTaylor_error (n : ℕ) (x : ℚ) :
    |Real.cos (x : ℝ) - (cosTaylor n x : ℝ)| ≤
      |(x : ℝ)|^(n+1) / ((n+1).factorial : ℝ) := by
  by_cases hx : (x : ℝ) = 0
  · have hxq : x = 0 := by exact_mod_cast hx
    subst x
    simp [cosTaylor, Finset.sum_range_succ', trigCoeff]
  rw [cosTaylor_eq n x hx]
  exact taylor_remainder_abs Real.cos n x Real.contDiff_cos
    (Real.abs_iteratedDeriv_cos_le_one (n+1))

theorem sinTaylor_error (n : ℕ) (x : ℚ) :
    |Real.sin (x : ℝ) - (sinTaylor n x : ℝ)| ≤
      |(x : ℝ)|^(n+1) / ((n+1).factorial : ℝ) := by
  by_cases hx : (x : ℝ) = 0
  · have hxq : x = 0 := by exact_mod_cast hx
    subst x
    simp [sinTaylor, Finset.sum_range_succ', trigCoeff]
  rw [sinTaylor_eq n x hx]
  exact taylor_remainder_abs Real.sin n x Real.contDiff_sin
    (Real.abs_iteratedDeriv_sin_le_one (n+1))

def trigRemainder (n : ℕ) (x : ℚ) : ℚ := |x|^(n+1) / ((n+1).factorial : ℚ)

/-- A finite rational check around the Taylor polynomial certifies an
enclosure of the transcendental value. Degree 44 matches the trace kernel. -/
def rationalCosEnclosure (n : ℕ) (x lo hi : ℚ) : Bool :=
  decide (lo ≤ cosTaylor n x - trigRemainder n x ∧
    cosTaylor n x + trigRemainder n x ≤ hi)

def rationalSinEnclosure (n : ℕ) (x lo hi : ℚ) : Bool :=
  decide (lo ≤ sinTaylor n x - trigRemainder n x ∧
    sinTaylor n x + trigRemainder n x ≤ hi)

theorem rationalCosEnclosure_sound (n : ℕ) (x lo hi : ℚ)
    (hc : rationalCosEnclosure n x lo hi = true) :
    (lo : ℝ) ≤ Real.cos (x : ℝ) ∧ Real.cos (x : ℝ) ≤ hi := by
  have hq : lo ≤ cosTaylor n x - trigRemainder n x ∧
      cosTaylor n x + trigRemainder n x ≤ hi := by
    simpa only [rationalCosEnclosure, decide_eq_true_eq] using hc
  have hr : (lo : ℝ) ≤ (cosTaylor n x : ℝ) - (trigRemainder n x : ℝ) ∧
      (cosTaylor n x : ℝ) + (trigRemainder n x : ℝ) ≤ hi := by exact_mod_cast hq
  have he := abs_le.mp (cosTaylor_error n x)
  have rem : (trigRemainder n x : ℝ) = |(x : ℝ)|^(n+1) / ((n+1).factorial : ℝ) := by
    simp [trigRemainder]
  rw [rem] at hr
  constructor <;> linarith only [hr.1, hr.2, he.1, he.2]

theorem rationalSinEnclosure_sound (n : ℕ) (x lo hi : ℚ)
    (hc : rationalSinEnclosure n x lo hi = true) :
    (lo : ℝ) ≤ Real.sin (x : ℝ) ∧ Real.sin (x : ℝ) ≤ hi := by
  have hq : lo ≤ sinTaylor n x - trigRemainder n x ∧
      sinTaylor n x + trigRemainder n x ≤ hi := by
    simpa only [rationalSinEnclosure, decide_eq_true_eq] using hc
  have hr : (lo : ℝ) ≤ (sinTaylor n x : ℝ) - (trigRemainder n x : ℝ) ∧
      (sinTaylor n x : ℝ) + (trigRemainder n x : ℝ) ≤ hi := by exact_mod_cast hq
  have he := abs_le.mp (sinTaylor_error n x)
  have rem : (trigRemainder n x : ℝ) = |(x : ℝ)|^(n+1) / ((n+1).factorial : ℝ) := by
    simp [trigRemainder]
  rw [rem] at hr
  constructor <;> linarith only [hr.1, hr.2, he.1, he.2]

end Sq17.Propagation

#print axioms Sq17.Propagation.cosTaylor_error
#print axioms Sq17.Propagation.sinTaylor_error
#print axioms Sq17.Propagation.rationalCosEnclosure_sound
#print axioms Sq17.Propagation.rationalSinEnclosure_sound
