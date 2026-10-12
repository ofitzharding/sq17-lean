import Sq17Lean.LocalGeometricWallFeasibility

namespace Sq17.LocalPerturbation
open Sq17.EndpointGeometry
set_option maxHeartbeats 2000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def wallCorners : Fin 25 → Fin 17 × Fin 4 × Bool × Bool := ![(0,0,false,true),(0,0,false,false),(0,2,false,false),(0,2,true,false),(1,2,false,false),(1,2,true,false),(2,0,false,true),(2,0,false,false),(3,0,false,true),(3,0,false,false),(3,3,true,true),(3,3,false,true),(4,2,false,false),(4,2,true,false),(6,1,true,false),(6,1,true,true),(7,1,true,false),(7,1,true,true),(7,3,true,true),(7,3,false,true),(8,0,false,true),(14,3,true,true),(14,3,false,true),(16,1,true,false),(16,1,true,true)]
theorem wallCorners_tight (a b z : ℝ) (r : Fin 25) :
    wallCornerBase a b z (wallCorners r).1 (wallCorners r).2.1
      (wallCorners r).2.2.1 (wallCorners r).2.2.2 = 0 := by
  fin_cases r
  · change wallCornerBase a b z 0 0 false true = 0
    have he : wallCornerBase a b z 0 0 false true = LocalSlider.wallGap a b z 0 0 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_1_0]
  · change wallCornerBase a b z 0 0 false false = 0
    have he : wallCornerBase a b z 0 0 false false = LocalSlider.wallGap a b z 0 0 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_1_0]
  · change wallCornerBase a b z 0 2 false false = 0
    have he : wallCornerBase a b z 0 2 false false = LocalSlider.wallGap a b z 0 2 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_1_2]
  · change wallCornerBase a b z 0 2 true false = 0
    have he : wallCornerBase a b z 0 2 true false = LocalSlider.wallGap a b z 0 2 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_1_2]
  · change wallCornerBase a b z 1 2 false false = 0
    have he : wallCornerBase a b z 1 2 false false = LocalSlider.wallGap a b z 1 2 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_2_2]
  · change wallCornerBase a b z 1 2 true false = 0
    have he : wallCornerBase a b z 1 2 true false = LocalSlider.wallGap a b z 1 2 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_2_2]
  · change wallCornerBase a b z 2 0 false true = 0
    have he : wallCornerBase a b z 2 0 false true = LocalSlider.wallGap a b z 2 0 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_3_0]
  · change wallCornerBase a b z 2 0 false false = 0
    have he : wallCornerBase a b z 2 0 false false = LocalSlider.wallGap a b z 2 0 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_3_0]
  · change wallCornerBase a b z 3 0 false true = 0
    have he : wallCornerBase a b z 3 0 false true = LocalSlider.wallGap a b z 3 0 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_4_0]
  · change wallCornerBase a b z 3 0 false false = 0
    have he : wallCornerBase a b z 3 0 false false = LocalSlider.wallGap a b z 3 0 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_4_0]
  · change wallCornerBase a b z 3 3 true true = 0
    have he : wallCornerBase a b z 3 3 true true = LocalSlider.wallGap a b z 3 3 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_4_3]
  · change wallCornerBase a b z 3 3 false true = 0
    have he : wallCornerBase a b z 3 3 false true = LocalSlider.wallGap a b z 3 3 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_4_3]
  · change wallCornerBase a b z 4 2 false false = 0
    have he : wallCornerBase a b z 4 2 false false = LocalSlider.wallGap a b z 4 2 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_5_2]
  · change wallCornerBase a b z 4 2 true false = 0
    have he : wallCornerBase a b z 4 2 true false = LocalSlider.wallGap a b z 4 2 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_5_2]
  · change wallCornerBase a b z 6 1 true false = 0
    have he : wallCornerBase a b z 6 1 true false = LocalSlider.wallGap a b z 6 1 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_7_1]
  · change wallCornerBase a b z 6 1 true true = 0
    have he : wallCornerBase a b z 6 1 true true = LocalSlider.wallGap a b z 6 1 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_7_1]
  · change wallCornerBase a b z 7 1 true false = 0
    have he : wallCornerBase a b z 7 1 true false = LocalSlider.wallGap a b z 7 1 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_8_1]
  · change wallCornerBase a b z 7 1 true true = 0
    have he : wallCornerBase a b z 7 1 true true = LocalSlider.wallGap a b z 7 1 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_8_1]
  · change wallCornerBase a b z 7 3 true true = 0
    have he : wallCornerBase a b z 7 3 true true = LocalSlider.wallGap a b z 7 3 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_8_3]
  · change wallCornerBase a b z 7 3 false true = 0
    have he : wallCornerBase a b z 7 3 false true = LocalSlider.wallGap a b z 7 3 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_8_3]
  · change wallCornerBase a b z 8 0 false true = 0
    have he : wallCornerBase a b z 8 0 false true = LocalSlider.wallGap a b z 8 0 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_9_0]
  · change wallCornerBase a b z 14 3 true true = 0
    have he : wallCornerBase a b z 14 3 true true = LocalSlider.wallGap a b z 14 3 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_15_3]
  · change wallCornerBase a b z 14 3 false true = 0
    have he : wallCornerBase a b z 14 3 false true = LocalSlider.wallGap a b z 14 3 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_15_3]
  · change wallCornerBase a b z 16 1 true false = 0
    have he : wallCornerBase a b z 16 1 true false = LocalSlider.wallGap a b z 16 1 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_17_1]
  · change wallCornerBase a b z 16 1 true true = 0
    have he : wallCornerBase a b z 16 1 true true = LocalSlider.wallGap a b z 16 1 := by
      norm_num [wallCornerBase,LocalSlider.wallGap,wallNormal,wallThreshold,LocalSlider.cornerSign,EndpointGeometry.directions,directionKind,supportTable]
      <;> ring
    rw [he,LocalSlider.wall_contact_17_1]
theorem wallRow_certificate_eq (a b z : ℝ) (h : Fin 45 → ℝ) (r : Fin 25) :
    wallRow h (wallCorners r).1 (wallCorners r).2.1
      (wallAngularWeight (wallCorners r).1 (wallCorners r).2.1
        (wallCorners r).2.2.1 (wallCorners r).2.2.2) =
      geometricRows a b z h (r.castLE (by decide : 25 ≤ 52)) := by
  fin_cases r <;> norm_num [wallCorners,wallAngularWeight,wallNormal,
    EndpointGeometry.directions,LocalSlider.cornerSign,geometricRows,wallRow] <;> ring
  all_goals simp

theorem first25_rows_lower {a b z q : ℝ} {h : Fin 45 → ℝ}
    (hbox : LocalSlider.sliderBox a b z) (hq0 : 0 ≤ q) (hq : q ≤ 1/2)
    (hh : ∀ k, |h k| ≤ q) (hfit : FitsEndpoint a b z h) (r : Fin 25) :
    -(100*q^2/2) ≤ geometricRows a b z h (r.castLE (by decide : 25 ≤ 52)) := by
  rw [← wallRow_certificate_eq]
  exact wallRow_lower hbox hq0 hq hh hfit _ _ _ _ (wallCorners_tight a b z r)

end Sq17.LocalPerturbation
#print axioms Sq17.LocalPerturbation.first25_rows_lower
