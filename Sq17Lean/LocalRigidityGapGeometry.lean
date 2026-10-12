import Sq17Lean.LocalRigidityGapCurvature

/-! The smooth gap in the curvature proof is exactly a rotating edge normal
against the displacement to an actual rotating square corner. -/
namespace Sq17.LocalRigidity

noncomputable def rotatingCornerGap (α ω A B C D β ν e f t : ℝ) : ℝ :=
  Real.cos (α+t*ω)*
    (A+t*C-(e*Real.cos (β+t*ν)-f*Real.sin (β+t*ν)))+
  Real.sin (α+t*ω)*
    (B+t*D-(e*Real.sin (β+t*ν)+f*Real.cos (β+t*ν)))-1/2

theorem rotatingCornerGap_eq (α ω A B C D β ν e f : ℝ) :
    rotatingCornerGap α ω A B C D β ν e f =
      rotatingGap α ω A B C D (β-α) (ν-ω) (-e) f := by
  funext t
  have hp : β-α+t*(ν-ω) = (β+t*ν)-(α+t*ω) := by ring
  dsimp [rotatingCornerGap,rotatingGap,trigAffine]
  rw [hp,Real.cos_sub,Real.sin_sub]
  ring

/-- Its first derivative is precisely a translation row plus one angular
coefficient for the normal owner and one for the corner owner. -/
theorem rotatingCornerGap_deriv_zero (α ω A B C D β ν e f : ℝ) :
    deriv (rotatingCornerGap α ω A B C D β ν e f) 0 =
      C*Real.cos α+D*Real.sin α+
      ω*(-A*Real.sin α+B*Real.cos α-(e*Real.sin (β-α)+f*Real.cos (β-α)))+
      ν*(e*Real.sin (β-α)+f*Real.cos (β-α)) := by
  rw [rotatingCornerGap_eq]
  have h := (((trigAffine_hasDerivAt α ω A B C D 0).add
    (trigAffine_hasDerivAt (β-α) (ν-ω) (-e) f 0 0 0)).sub_const (1/2)).deriv
  change deriv (rotatingGap α ω A B C D (β-α) (ν-ω) (-e) f) 0 = _ at h
  rw [h]
  simp only [trigAffineFirst,zero_mul,add_zero,sub_zero]
  ring

/-- Every choice of a square corner has coefficients of absolute sum one. -/
theorem square_corner_coeff_bound (e f : ℝ)
    (he : |e| ≤ 1/2) (hf : |f| ≤ 1/2) : |-e|+|f| ≤ 1 := by
  rw [abs_neg]; linarith

/-- The curvature bound now applies directly to the rotating-corner gap,
using the angular speed of each square separately. -/
theorem rotatingCornerGap_curvature (α ω A B C D β ν e f t q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/2) (ht : |t| ≤ 1)
    (hω : |ω| ≤ q) (hν : |ν| ≤ q)
    (hA : |A| ≤ 10) (hB : |B| ≤ 10)
    (hC : |C| ≤ 2*q) (hD : |D| ≤ 2*q)
    (he : |e| ≤ 1/2) (hf : |f| ≤ 1/2) :
    |iteratedDeriv 2 (rotatingCornerGap α ω A B C D β ν e f) t| ≤ 100*q^2 := by
  rw [rotatingCornerGap_eq]
  apply rotatingGap_curvature α ω A B C D (β-α) (ν-ω) (-e) f t q hq0 hq ht hω
    (by have h := abs_sub_le ν 0 ω; simp only [sub_zero,zero_sub,abs_neg] at h; linarith) hA hB hC hD
    (square_corner_coeff_bound e f he hf)

/-- Necessary first-order inequality for an explicit moving square corner. -/
theorem rotatingCornerGap_linear_lower (α ω A B C D β ν e f q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/2) (hω : |ω| ≤ q) (hν : |ν| ≤ q)
    (hA : |A| ≤ 10) (hB : |B| ≤ 10)
    (hC : |C| ≤ 2*q) (hD : |D| ≤ 2*q)
    (he : |e| ≤ 1/2) (hf : |f| ≤ 1/2)
    (hbase : rotatingCornerGap α ω A B C D β ν e f 0 = 0)
    (hfeasible : 0 ≤ rotatingCornerGap α ω A B C D β ν e f 1) :
    -(100*q^2/2) ≤ deriv (rotatingCornerGap α ω A B C D β ν e f) 0 := by
  rw [rotatingCornerGap_eq] at hbase hfeasible ⊢
  exact rotatingGap_linear_lower α ω A B C D (β-α) (ν-ω) (-e) f q hq0 hq hω
    (by have h := abs_sub_le ν 0 ω; simp only [sub_zero,zero_sub,abs_neg] at h; linarith) hA hB hC hD
    (square_corner_coeff_bound e f he hf) hbase hfeasible

#print axioms rotatingCornerGap_eq
#print axioms rotatingCornerGap_deriv_zero
#print axioms rotatingCornerGap_curvature
#print axioms rotatingCornerGap_linear_lower
end Sq17.LocalRigidity
