import Sq17Lean.LocalPerturbationCoordinates

/-! Exact inverse of the local coordinate chart on the sixteen constrained
squares. The omitted square6 is not reconstructed or assigned a fake pose. -/
namespace Sq17.LocalPerturbation
open Sq17.EndpointGeometry
noncomputable section

def displacement (P : Fin 17 → ℝ × ℝ) (i : Fin 17) : ℝ × ℝ :=
  P i-EndpointGeometry.centres i

def sliderA (P : Fin 17 → ℝ × ℝ) : ℝ := -(displacement P 4).1
def sliderB (P : Fin 17 → ℝ × ℝ) : ℝ := s*(displacement P 10).1-c*(displacement P 10).2
def sliderZ (P : Fin 17 → ℝ × ℝ) : ℝ := -s*(displacement P 12).1+c*(displacement P 12).2
def transverse (P : Fin 17 → ℝ × ℝ) (i : Fin 17) : ℝ :=
  c*(displacement P i).1+s*(displacement P i).2

def encode (P : Fin 17 → ℝ × ℝ) (θ : Fin 17 → ℝ) : Fin 45 → ℝ := ![
  (displacement P 0).1,(displacement P 0).2,θ 0-baseAngle 0,
  (displacement P 1).1,(displacement P 1).2,θ 1-baseAngle 1,
  (displacement P 2).1,(displacement P 2).2,θ 2-baseAngle 2,
  (displacement P 3).1,(displacement P 3).2,θ 3-baseAngle 3,
  (displacement P 4).2,θ 4-baseAngle 4,
  (displacement P 6).1,(displacement P 6).2,θ 6-baseAngle 6,
  (displacement P 7).1,(displacement P 7).2,θ 7-baseAngle 7,
  (displacement P 8).1,(displacement P 8).2,θ 8-baseAngle 8,
  (displacement P 9).1,(displacement P 9).2,θ 9-baseAngle 9,
  transverse P 10,θ 10-baseAngle 10,
  (displacement P 11).1,(displacement P 11).2,θ 11-baseAngle 11,
  transverse P 12,θ 12-baseAngle 12,
  (displacement P 13).1,(displacement P 13).2,θ 13-baseAngle 13,
  (displacement P 14).1,(displacement P 14).2,θ 14-baseAngle 14,
  (displacement P 15).1,(displacement P 15).2,θ 15-baseAngle 15,
  (displacement P 16).1,(displacement P 16).2,θ 16-baseAngle 16]

private theorem basis_x (x y : ℝ) : s*(s*x-c*y)+c*(c*x+s*y)=x := by
  linear_combination x*cs_unit

private theorem basis_y (x y : ℝ) : -c*(s*x-c*y)+s*(c*x+s*y)=y := by
  linear_combination y*cs_unit

theorem centres_encode (P : Fin 17 → ℝ × ℝ) (θ : Fin 17 → ℝ)
    (i : Fin 17) (hi : i ≠ 5) :
    centres (sliderA P) (sliderB P) (sliderZ P) (encode P θ) i = P i := by
  fin_cases i <;> try contradiction
  all_goals
    ext <;> simp [centres,translation,encode,LocalSlider.centres,LocalSlider.offset,
      sliderA,sliderB,sliderZ,transverse,displacement]
    <;> ring_nf
  all_goals nlinarith [cs_unit,
    congrArg (fun v : ℝ => v*(P 10).1) cs_unit,
    congrArg (fun v : ℝ => v*(P 10).2) cs_unit,
    congrArg (fun v : ℝ => v*(EndpointGeometry.centres 10).1) cs_unit,
    congrArg (fun v : ℝ => v*(EndpointGeometry.centres 10).2) cs_unit,
    congrArg (fun v : ℝ => v*(P 12).1) cs_unit,
    congrArg (fun v : ℝ => v*(P 12).2) cs_unit,
    congrArg (fun v : ℝ => v*(EndpointGeometry.centres 12).1) cs_unit,
    congrArg (fun v : ℝ => v*(EndpointGeometry.centres 12).2) cs_unit]

theorem angular_encode (P : Fin 17 → ℝ × ℝ) (θ : Fin 17 → ℝ)
    (i : Fin 17) (hi : i ≠ 5) : angular (encode P θ) i = θ i-baseAngle i := by
  fin_cases i <;> simp_all [angular,encode]

theorem directions_encode (P : Fin 17 → ℝ × ℝ) (θ : Fin 17 → ℝ)
    (i : Fin 17) (hi : i ≠ 5) :
    directions (encode P θ) i = (Real.cos (θ i),Real.sin (θ i)) := by
  simp [directions,angular_encode P θ i hi]

#print axioms centres_encode
#print axioms directions_encode
end
end Sq17.LocalPerturbation
