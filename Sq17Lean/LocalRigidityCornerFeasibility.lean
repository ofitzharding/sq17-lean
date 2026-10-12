import Sq17Lean.LocalRigidityGapGeometry
import Sq17Lean.SquareSeparationGeometry

/-! Support separation implies feasibility of each smooth corner constraint.
This connects the finite-axis theorem to the Taylor contact rows. -/
namespace Sq17.LocalRigidity
open Sq17.WallCapacity

theorem corner_le_support (vx vy a b e f : ℝ)
    (he : |e| ≤ 1/2) (hf : |f| ≤ 1/2) :
    a*(e*vx-f*vy)+b*(e*vy+f*vx) ≤ squareSupport vx vy a b := by
  have bound (k z : ℝ) (hz : |z| ≤ 1/2) : z*k ≤ |k|/2 := by
    have h := mul_le_mul_of_nonneg_left hz (abs_nonneg k)
    have hz' := le_abs_self (z*k)
    rw [abs_mul] at hz'
    nlinarith
  have h1 := bound (a*vx+b*vy) e he
  have h2 := bound (b*vx-a*vy) f hf
  dsimp [squareSupport]
  nlinarith only [h1,h2]

/-- Every point with local corner coefficients in [-1/2,1/2] satisfies the
necessary signed corner inequality whenever the support gap separates. -/
theorem support_gap_corner_feasible (ux uy vx vy a b X Y e f : ℝ)
    (hu : ux^2+uy^2=1) (hn : a^2+b^2=1)
    (he : |e| ≤ 1/2) (hf : |f| ≤ 1/2)
    (hgap : squareSupport ux uy a b+squareSupport vx vy a b ≤ a*X+b*Y) :
    0 ≤ a*(X-(e*vx-f*vy))+b*(Y-(e*vy+f*vx))-1/2 := by
  have hu' := squareSupport_ge_half ux uy a b hu hn
  have hv' := corner_le_support vx vy a b e f he hf
  nlinarith only [hu',hv',hgap]

/-- Feasibility for the precise rotating formula used in the derivative
and curvature lemmas; the selected separator still appears explicitly. -/
theorem rotatingCornerGap_feasible (α ω A B C D β ν e f t ux uy : ℝ)
    (hu : ux^2+uy^2=1) (he : |e| ≤ 1/2) (hf : |f| ≤ 1/2)
    (hgap : squareSupport ux uy (Real.cos (α+t*ω)) (Real.sin (α+t*ω))+
      squareSupport (Real.cos (β+t*ν)) (Real.sin (β+t*ν))
        (Real.cos (α+t*ω)) (Real.sin (α+t*ω)) ≤
      Real.cos (α+t*ω)*(A+t*C)+Real.sin (α+t*ω)*(B+t*D)) :
    0 ≤ rotatingCornerGap α ω A B C D β ν e f t := by
  exact support_gap_corner_feasible ux uy (Real.cos (β+t*ν)) (Real.sin (β+t*ν))
    (Real.cos (α+t*ω)) (Real.sin (α+t*ω)) (A+t*C) (B+t*D) e f hu
    (Real.cos_sq_add_sin_sq _) he hf hgap

#print axioms corner_le_support
#print axioms support_gap_corner_feasible
#print axioms rotatingCornerGap_feasible
end Sq17.LocalRigidity
