import Sq17Lean.LocalChartCoordinates
import Sq17Lean.WallSquareSupport

namespace Sq17.LocalPerturbation
open Sq17.EndpointGeometry Sq17.WallCapacity
noncomputable section

/-- Bounds directly expressed in the original square poses, as needed by
the capture certificates. The free square6 has no chart constraints. -/
structure CoordinateBounds (P : Fin 17 → ℝ × ℝ) (θ : Fin 17 → ℝ) (r : ℝ) : Prop where
  angles : ∀ i, i ≠ 5 → |θ i-baseAngle i| ≤ r
  fifthY : |(displacement P 4).2| ≤ r
  eleventh : |transverse P 10| ≤ r
  thirteenth : |transverse P 12| ≤ r
  regular : ∀ i, i ≠ 4 → i ≠ 5 → i ≠ 10 → i ≠ 12 →
    |(displacement P i).1| ≤ r ∧ |(displacement P i).2| ≤ r

theorem encode_bounded (P : Fin 17 → ℝ × ℝ) (θ : Fin 17 → ℝ) (r : ℝ)
    (hb : CoordinateBounds P θ r) : ∀ j, |encode P θ j| ≤ r := by
  intro j
  fin_cases j <;> norm_num only [encode,Matrix.cons_val_zero,Matrix.cons_val_succ]
  all_goals first
    | exact hb.angles _ (by decide)
    | exact hb.fifthY
    | exact hb.eleventh
    | exact hb.thirteenth
    | exact (hb.regular _ (by decide) (by decide) (by decide) (by decide)).1
    | exact (hb.regular _ (by decide) (by decide) (by decide) (by decide)).2

/-- The lower slider bound a≥0 follows from actual right-wall feasibility,
even when the captured numerical row has a small amount of wall slack. -/
theorem sliderA_nonnegative_of_fit (P : Fin 17 → ℝ × ℝ) (θ : Fin 17 → ℝ)
    (hfit : ∀ p ∈ Sq17.sq (P 4).1 (P 4).2 (Real.cos (θ 4)) (Real.sin (θ 4)),
      p.1 ≤ side) : 0 ≤ sliderA P := by
  obtain ⟨p,hp,he⟩ := squareSupport_attained (P 4).1 (P 4).2
    (Real.cos (θ 4)) (Real.sin (θ 4)) 1 0 (Real.cos_sq_add_sin_sq _)
  have hhalf := squareSupport_ge_half (Real.cos (θ 4)) (Real.sin (θ 4)) 1 0
    (Real.cos_sq_add_sin_sq _) (by norm_num)
  have hbound := hfit p hp
  norm_num at he
  simp only [sliderA,displacement,Prod.fst_sub]
  norm_num [EndpointGeometry.centres]
  linarith

#print axioms encode_bounded
#print axioms sliderA_nonnegative_of_fit
end
end Sq17.LocalPerturbation
