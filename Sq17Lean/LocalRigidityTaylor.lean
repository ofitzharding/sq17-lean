import Sq17Lean.LocalRigidityDual
import Mathlib.Analysis.Calculus.Taylor

/-! A genuine second-derivative bound along the perturbation segment implies
its necessary linearized constraint, with the exact factor 1/2. Deriving the
rotation-gap derivative bound remains a separate geometric obligation. -/
namespace Sq17.LocalRigidity

/-- First-order Taylor's theorem on [0,1], in a form suited to local contact
constraints. The function may be any globally C2 real function. -/
theorem segment_taylor_upper (f : ℝ → ℝ) (K : ℝ)
    (hf : ContDiff ℝ 2 f)
    (hsecond : ∀ t ∈ Set.Ioo (0 : ℝ) 1, iteratedDeriv 2 f t ≤ K) :
    f 1 ≤ f 0 + deriv f 0 + K / 2 := by
  have hn : (0 : ℝ) ≠ 1 := by norm_num
  obtain ⟨t, ht, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := f) (x₀ := 0) (x := 1) (n := 1) hn hf.contDiffOn
  have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by simpa using ht
  have hd : derivWithin f (Set.uIcc (0 : ℝ) 1) 0 = deriv f 0 := by
    apply (hf.differentiable (by norm_num)).differentiableAt.derivWithin
    exact (uniqueDiffOn_uIcc hn) 0 (by simp)
  have hd' : derivWithin f (Set.Icc (0 : ℝ) 1) 0 = deriv f 0 := by
    simpa using hd
  have hp : taylorWithinEval f 1 (Set.uIcc (0 : ℝ) 1) 0 1 = f 0 + deriv f 0 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, taylorWithinEval_succ]
    simp [iteratedDerivWithin_one, hd']
  rw [hp] at he
  norm_num at he
  have hb := hsecond t ht'
  linarith

/-- Tightness at the base, feasibility at the endpoint, and a C2 curvature
bound give the necessary linearized row inequality. -/
theorem segment_linear_lower (f : ℝ → ℝ) (K q : ℝ)
    (hf : ContDiff ℝ 2 f) (hbase : f 0 = 0) (hfeasible : 0 ≤ f 1)
    (hsecond : ∀ t ∈ Set.Ioo (0 : ℝ) 1, |iteratedDeriv 2 f t| ≤ K*q^2) :
    -(K*q^2/2) ≤ deriv f 0 := by
  have ht := segment_taylor_upper f (K*q^2) hf
    (fun t ht => (le_abs_self _).trans (hsecond t ht))
  rw [hbase] at ht
  linarith

end Sq17.LocalRigidity
#print axioms Sq17.LocalRigidity.segment_taylor_upper
#print axioms Sq17.LocalRigidity.segment_linear_lower
