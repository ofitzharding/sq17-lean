import Sq17Lean.LocalRigidityCornerFeasibility

/-! Wall constraints give genuine smooth corner inequalities, with their
linearized rows derived from the same proved rotating-corner formula. -/
namespace Sq17.LocalRigidity
open Sq17.WallCapacity

/-- A fitted square satisfies every wall-corner constraint. -/
theorem fitted_wall_corner (cx cy ux uy a b W e f : ℝ)
    (hu : ux^2+uy^2=1) (he : |e| ≤ 1/2) (hf : |f| ≤ 1/2)
    (hfit : Sq17.sq cx cy ux uy ⊆ {z | a*z.1+b*z.2 ≤ W}) :
    0 ≤ W-a*(cx+(e*ux-f*uy))-b*(cy+(e*uy+f*ux)) := by
  obtain ⟨z,hz,hs⟩ := squareSupport_attained cx cy ux uy a b hu
  have h := hfit hz
  have hc := corner_le_support ux uy a b e f he hf
  change a*z.1+b*z.2 ≤ W at h
  nlinarith only [h,hs,hc]

noncomputable def movingWallGap (α W X Y C D β ν e f t : ℝ) : ℝ :=
  W-Real.cos α*(X+t*C+(e*Real.cos (β+t*ν)-f*Real.sin (β+t*ν)))-
    Real.sin α*(Y+t*D+(e*Real.sin (β+t*ν)+f*Real.cos (β+t*ν)))

theorem movingWallGap_eq (α W X Y C D β ν e f : ℝ) :
    movingWallGap α W X Y C D β ν e f =
      rotatingCornerGap α 0 ((W+1/2)*Real.cos α-X) ((W+1/2)*Real.sin α-Y)
        (-C) (-D) β ν e f := by
  funext t
  have hu := Real.cos_sq_add_sin_sq α
  dsimp [movingWallGap,rotatingCornerGap]
  simp only [mul_zero,add_zero]
  calc
    _ = (W+1/2)*(Real.cos α^2+Real.sin α^2)-1/2-
        Real.cos α*(X+t*C+(e*Real.cos (β+t*ν)-f*Real.sin (β+t*ν)))-
        Real.sin α*(Y+t*D+(e*Real.sin (β+t*ν)+f*Real.cos (β+t*ν))) := by rw [hu];ring
    _ = _ := by ring

theorem movingWallGap_deriv_zero (α W X Y C D β ν e f : ℝ) :
    deriv (movingWallGap α W X Y C D β ν e f) 0 =
      -C*Real.cos α-D*Real.sin α+ν*(e*Real.sin (β-α)+f*Real.cos (β-α)) := by
  rw [movingWallGap_eq,rotatingCornerGap_deriv_zero]
  ring

private theorem wall_reference_bound (W X u : ℝ)
    (hW : |W| ≤ 19/4) (hX : |X| ≤ 19/4) (hu : |u| ≤ 1) :
    |(W+1/2)*u-X| ≤ 10 := by
  have h1 := abs_add_le W (1/2 : ℝ)
  norm_num at h1
  have h2 := mul_le_mul_of_nonneg_left hu (abs_nonneg (W+1/2))
  have h3 := abs_sub_le ((W+1/2)*u) 0 X
  simp only [sub_zero,zero_sub,abs_neg,abs_mul] at h3
  nlinarith

/-- Wall rows need no assumed curvature bound either. -/
theorem movingWallGap_linear_lower (α W X Y C D β ν e f q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/2) (hν : |ν| ≤ q)
    (hW : |W| ≤ 19/4) (hX : |X| ≤ 19/4) (hY : |Y| ≤ 19/4)
    (hC : |C| ≤ q) (hD : |D| ≤ q) (he : |e| ≤ 1/2) (hf : |f| ≤ 1/2)
    (hbase : movingWallGap α W X Y C D β ν e f 0 = 0)
    (hfeasible : 0 ≤ movingWallGap α W X Y C D β ν e f 1) :
    -(100*q^2/2) ≤ deriv (movingWallGap α W X Y C D β ν e f) 0 := by
  rw [movingWallGap_eq] at hbase hfeasible ⊢
  apply rotatingCornerGap_linear_lower α 0 _ _ (-C) (-D) β ν e f q
    hq0 hq (by simpa using hq0) hν
    (wall_reference_bound W X (Real.cos α) hW hX (Real.abs_cos_le_one α))
    (wall_reference_bound W Y (Real.sin α) hW hY (Real.abs_sin_le_one α))
    (by rw [abs_neg];linarith) (by rw [abs_neg];linarith) he hf hbase hfeasible

#print axioms fitted_wall_corner
#print axioms movingWallGap_deriv_zero
#print axioms movingWallGap_linear_lower
end Sq17.LocalRigidity
