import Sq17Lean.LocalGeometricRows
import Sq17Lean.LocalSliderDistances
import Sq17Lean.LocalRigidityWallRows

namespace Sq17.LocalPerturbation
open Sq17.EndpointGeometry Sq17.WallCapacity Sq17.LocalRigidity
noncomputable section

/-- Every square of the actual perturbation fits in the endpoint container. -/
def FitsEndpoint (a b z : ℝ) (h : Fin 45 → ℝ) : Prop := ∀ i,
  Sq17.sq (centres a b z h i).1 (centres a b z h i).2
    (directions h i).1 (directions h i).2 ⊆
      {p | 0 ≤ p.1 ∧ p.1 ≤ side ∧ 0 ≤ p.2 ∧ p.2 ≤ side}

def wallAngle : Fin 4 → ℝ := ![Real.pi,0,-(Real.pi/2),Real.pi/2]
def wallNormal : Fin 4 → ℝ × ℝ := ![(-1,0),(1,0),(0,-1),(0,1)]
def wallThreshold : Fin 4 → ℝ := ![0,side,0,side]

theorem wallAngle_normal (w : Fin 4) :
    (Real.cos (wallAngle w),Real.sin (wallAngle w)) = wallNormal w := by
  fin_cases w <;> norm_num [wallAngle,wallNormal]

theorem slider_centres_wall_bounds {a b z : ℝ} (hbox : LocalSlider.sliderBox a b z)
    (i : Fin 17) :
    |(LocalSlider.centres a b z i).1| ≤ 19/4 ∧
    |(LocalSlider.centres a b z i).2| ≤ 19/4 := by
  have hs := squareSupport_ge_half (EndpointGeometry.directions i).1
    (EndpointGeometry.directions i).2 1 0 (EndpointGeometry.directions_unit i) (by norm_num)
  have he := square_support_table i 0
  change squareSupport (EndpointGeometry.directions i).1
    (EndpointGeometry.directions i).2 1 0 = supportTable (directionKind i) 0 at he
  rw [he] at hs
  have hx0 := all_wall_gaps i 0
  have hx1 := all_wall_gaps i 1
  have hy0 := all_wall_gaps i 2
  have hy1 := all_wall_gaps i 3
  norm_num [EndpointGeometry.wallGap] at hx0 hx1 hy0 hy1
  have hoff := LocalSlider.offset_bounds hbox i
  have hside := EndpointIntervals.side_bounds.2
  norm_num at hside
  have ho0 := abs_le.mp hoff.1
  have ho1 := abs_le.mp hoff.2
  simp only [LocalSlider.centres,Prod.fst_add,Prod.snd_add]
  constructor <;> rw [abs_le] <;> constructor <;> linarith

theorem wallThreshold_bound (w : Fin 4) : |wallThreshold w| ≤ 19/4 := by
  have hside := EndpointIntervals.side_bounds
  have hp := side_positive
  fin_cases w <;> norm_num [wallThreshold,abs_of_pos hp] <;> linarith [hside.2]

def wallCornerBase (a b z : ℝ) (i : Fin 17) (w : Fin 4) (se sf : Bool) : ℝ :=
  let p := LocalSlider.centres a b z i
  let v := EndpointGeometry.directions i
  let n := wallNormal w
  wallThreshold w-n.1*(p.1+(LocalSlider.cornerSign se*v.1-LocalSlider.cornerSign sf*v.2))-
    n.2*(p.2+(LocalSlider.cornerSign se*v.2+LocalSlider.cornerSign sf*v.1))

def wallAngularWeight (i : Fin 17) (w : Fin 4) (se sf : Bool) : ℝ :=
  let v := EndpointGeometry.directions i
  let n := wallNormal w
  n.1*(LocalSlider.cornerSign se*v.2+LocalSlider.cornerSign sf*v.1)-
    n.2*(LocalSlider.cornerSign se*v.1-LocalSlider.cornerSign sf*v.2)

def wallMovingGap (a b z : ℝ) (h : Fin 45 → ℝ) (i : Fin 17)
    (w : Fin 4) (se sf : Bool) : ℝ → ℝ :=
  movingWallGap (wallAngle w) (wallThreshold w)
    (LocalSlider.centres a b z i).1 (LocalSlider.centres a b z i).2
    (translation h i).1 (translation h i).2 (baseAngle i) (angular h i)
    (LocalSlider.cornerSign se) (LocalSlider.cornerSign sf)

theorem wallMovingGap_zero (a b z : ℝ) (h : Fin 45 → ℝ) (i : Fin 17)
    (w : Fin 4) (se sf : Bool) :
    wallMovingGap a b z h i w se sf 0 = wallCornerBase a b z i w se sf := by
  have hn1 := congrArg Prod.fst (wallAngle_normal w)
  have hn2 := congrArg Prod.snd (wallAngle_normal w)
  have hv1 := congrArg Prod.fst (baseAngle_direction i)
  have hv2 := congrArg Prod.snd (baseAngle_direction i)
  simp only [Prod.fst,Prod.snd] at hn1 hn2 hv1 hv2
  simp [wallMovingGap,movingWallGap,wallCornerBase,hn1,hn2,hv1,hv2]

theorem wallMovingGap_derivative (a b z : ℝ) (h : Fin 45 → ℝ) (i : Fin 17)
    (w : Fin 4) (se sf : Bool) :
    deriv (wallMovingGap a b z h i w se sf) 0 = wallRow h i w (wallAngularWeight i w se sf) := by
  have hn1 := congrArg Prod.fst (wallAngle_normal w)
  have hn2 := congrArg Prod.snd (wallAngle_normal w)
  have hv1 := congrArg Prod.fst (baseAngle_direction i)
  have hv2 := congrArg Prod.snd (baseAngle_direction i)
  simp only [Prod.fst,Prod.snd] at hn1 hn2 hv1 hv2
  rw [wallMovingGap,movingWallGap_deriv_zero]
  simp only [Real.sin_sub,Real.cos_sub,hn1,hn2,hv1,hv2]
  fin_cases w <;> norm_num [wallAngularWeight,wallNormal,wallRow] <;> ring

theorem wallMovingGap_feasible {a b z : ℝ} {h : Fin 45 → ℝ}
    (hfit : FitsEndpoint a b z h) (i : Fin 17) (w : Fin 4) (se sf : Bool) :
    0 ≤ wallMovingGap a b z h i w se sf 1 := by
  have hf : Sq17.sq (centres a b z h i).1 (centres a b z h i).2
      (directions h i).1 (directions h i).2 ⊆
      {p | (wallNormal w).1*p.1+(wallNormal w).2*p.2 ≤ wallThreshold w} := by
    intro p hp
    have hc := hfit i hp
    fin_cases w <;> norm_num [wallNormal,wallThreshold] <;> linarith [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]
  have hb := fitted_wall_corner (centres a b z h i).1 (centres a b z h i).2
    (directions h i).1 (directions h i).2 (wallNormal w).1 (wallNormal w).2
    (wallThreshold w) (LocalSlider.cornerSign se) (LocalSlider.cornerSign sf)
    (directions_unit h i) (LocalSlider.cornerSign_bounds se) (LocalSlider.cornerSign_bounds sf) hf
  have hn1 := congrArg Prod.fst (wallAngle_normal w)
  have hn2 := congrArg Prod.snd (wallAngle_normal w)
  simp only [Prod.fst,Prod.snd] at hn1 hn2
  simpa [wallMovingGap,movingWallGap,centres,directions,hn1,hn2] using hb

theorem wallRow_lower {a b z q : ℝ} {h : Fin 45 → ℝ}
    (hbox : LocalSlider.sliderBox a b z) (hq0 : 0 ≤ q) (hq : q ≤ 1/2)
    (hh : ∀ k, |h k| ≤ q) (hfit : FitsEndpoint a b z h)
    (i : Fin 17) (w : Fin 4) (se sf : Bool)
    (htight : wallCornerBase a b z i w se sf = 0) :
    -(100*q^2/2) ≤ wallRow h i w (wallAngularWeight i w se sf) := by
  have hp := slider_centres_wall_bounds hbox i
  have htr := translation_bounds h q hq0 hh i
  have hb := movingWallGap_linear_lower (wallAngle w) (wallThreshold w)
    (LocalSlider.centres a b z i).1 (LocalSlider.centres a b z i).2
    (translation h i).1 (translation h i).2 (baseAngle i) (angular h i)
    (LocalSlider.cornerSign se) (LocalSlider.cornerSign sf) q hq0 hq
    (angular_bounds h q hq0 hh i) (wallThreshold_bound w) hp.1 hp.2 htr.1 htr.2
    (LocalSlider.cornerSign_bounds se) (LocalSlider.cornerSign_bounds sf)
    (by change wallMovingGap a b z h i w se sf 0 = 0; rw [wallMovingGap_zero,htight])
    (wallMovingGap_feasible hfit i w se sf)
  change -(100*q^2/2) ≤ deriv (wallMovingGap a b z h i w se sf) 0 at hb
  rwa [wallMovingGap_derivative] at hb

end
end Sq17.LocalPerturbation
#print axioms Sq17.LocalPerturbation.wallRow_lower
