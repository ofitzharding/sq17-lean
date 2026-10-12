import Sq17Lean.LocalRigidityTaylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Actual second derivatives for a rotating normal against an affine centre
and a rotating corner. The uniform constant is chosen for the captured radius,
not to optimize the largest possible neighbourhood. -/
namespace Sq17.LocalRigidity

noncomputable def trigAffine (α ω A B C D t : ℝ) : ℝ :=
  (A+t*C)*Real.cos (α+t*ω)+(B+t*D)*Real.sin (α+t*ω)

noncomputable def trigAffineFirst (α ω A B C D t : ℝ) : ℝ :=
  C*Real.cos (α+t*ω)+D*Real.sin (α+t*ω)+
    ω*((B+t*D)*Real.cos (α+t*ω)-(A+t*C)*Real.sin (α+t*ω))

noncomputable def trigAffineSecond (α ω A B C D t : ℝ) : ℝ :=
  -(ω^2)*trigAffine α ω A B C D t+
    2*ω*(-C*Real.sin (α+t*ω)+D*Real.cos (α+t*ω))

theorem trigAffine_hasDerivAt (α ω A B C D t : ℝ) :
    HasDerivAt (trigAffine α ω A B C D) (trigAffineFirst α ω A B C D t) t := by
  have hp : HasDerivAt (fun t : ℝ => α+t*ω) ω t := by
    simpa using ((hasDerivAt_id t).mul_const ω).const_add α
  have hA : HasDerivAt (fun t : ℝ => A+t*C) C t := by
    simpa using ((hasDerivAt_id t).mul_const C).const_add A
  have hB : HasDerivAt (fun t : ℝ => B+t*D) D t := by
    simpa using ((hasDerivAt_id t).mul_const D).const_add B
  convert (hA.mul hp.cos).add (hB.mul hp.sin) using 1 <;>
    (try funext z) <;> simp only [trigAffine,trigAffineFirst,Pi.add_apply,Pi.mul_apply,Pi.sub_apply] <;> ring

theorem trigAffineFirst_hasDerivAt (α ω A B C D t : ℝ) :
    HasDerivAt (trigAffineFirst α ω A B C D) (trigAffineSecond α ω A B C D t) t := by
  have hp : HasDerivAt (fun t : ℝ => α+t*ω) ω t := by
    simpa using ((hasDerivAt_id t).mul_const ω).const_add α
  have hA : HasDerivAt (fun t : ℝ => A+t*C) C t := by
    simpa using ((hasDerivAt_id t).mul_const C).const_add A
  have hB : HasDerivAt (fun t : ℝ => B+t*D) D t := by
    simpa using ((hasDerivAt_id t).mul_const D).const_add B
  convert ((hp.cos.const_mul C).add (hp.sin.const_mul D)).add
    (((hB.mul hp.cos).sub (hA.mul hp.sin)).const_mul ω) using 1 <;>
    (try funext z) <;> simp only [trigAffine,trigAffineFirst,trigAffineSecond,Pi.add_apply,Pi.mul_apply,Pi.sub_apply] <;> ring

theorem trigAffine_iteratedDeriv (α ω A B C D : ℝ) :
    iteratedDeriv 2 (trigAffine α ω A B C D) = trigAffineSecond α ω A B C D := by
  have hd : deriv (trigAffine α ω A B C D) = trigAffineFirst α ω A B C D :=
    funext (fun t => (trigAffine_hasDerivAt α ω A B C D t).deriv)
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  rw [hd]
  exact funext (fun t => (trigAffineFirst_hasDerivAt α ω A B C D t).deriv)

private theorem abs_trig_combo (A B t : ℝ) :
    |A*Real.cos t+B*Real.sin t| ≤ |A|+|B| := by
  calc
    _ ≤ |A*Real.cos t|+|B*Real.sin t| := abs_add_le _ _
    _ = |A| *|Real.cos t|+|B| *|Real.sin t| := by rw [abs_mul,abs_mul]
    _ ≤ |A|+|B| := by
      have hc := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one t) (abs_nonneg A)
      have hs := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one t) (abs_nonneg B)
      nlinarith

theorem trigAffine_second_bound (α ω A B C D t : ℝ) :
    |trigAffineSecond α ω A B C D t| ≤
      ω^2*(|A+t*C|+|B+t*D|)+2*|ω| *(|C|+|D|) := by
  have hfirst := abs_trig_combo (A+t*C) (B+t*D) (α+t*ω)
  have hcross : |-C*Real.sin (α+t*ω)+D*Real.cos (α+t*ω)| ≤ |C|+|D| := by
    have h := abs_trig_combo D (-C) (α+t*ω)
    simpa only [add_comm,abs_neg] using h
  have hm1 := mul_le_mul_of_nonneg_left hfirst (sq_nonneg ω)
  have hm2 := mul_le_mul_of_nonneg_left hcross (show 0 ≤ 2*|ω| by positivity)
  calc
    _ ≤ |-(ω^2)*trigAffine α ω A B C D t|+
        |2*ω*(-C*Real.sin (α+t*ω)+D*Real.cos (α+t*ω))| := abs_add_le _ _
    _ = ω^2*|trigAffine α ω A B C D t|+
        2*|ω| *|-C*Real.sin (α+t*ω)+D*Real.cos (α+t*ω)| := by
      rw [abs_mul,abs_mul,abs_mul,abs_neg,abs_of_nonneg (sq_nonneg ω)]
      norm_num
    _ ≤ _ := by dsimp [trigAffine] at *; linarith

#print axioms trigAffine_iteratedDeriv
#print axioms trigAffine_second_bound
end Sq17.LocalRigidity
