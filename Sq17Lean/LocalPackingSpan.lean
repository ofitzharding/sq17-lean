import Sq17Lean.LocalPerturbationCoordinates

/-! The rigid local family has the full endpoint width, independently of
the three slider positions or the chosen container translation. -/
namespace Sq17.LocalPerturbation
open Sq17.EndpointGeometry
noncomputable section

def motionSquare (a b z : ℝ) (h : Fin 45 → ℝ) (i : Fin 17) : Set (ℝ × ℝ) :=
  Sq17.sq (centres a b z h i).1 (centres a b z h i).2
    (directions h i).1 (directions h i).2

theorem zero_motion_left (a b z : ℝ) :
    (0,(1:ℝ)/2) ∈ motionSquare a b z (fun _ => 0) 0 := by
  simp only [motionSquare,centres_zero,directions_zero]
  norm_num [LocalSlider.centres,LocalSlider.offset,EndpointGeometry.centres,
    EndpointGeometry.directions,Sq17.sq]

theorem zero_motion_right (a b z : ℝ) :
    (side,(3:ℝ)/2) ∈ motionSquare a b z (fun _ => 0) 6 := by
  simp only [motionSquare,centres_zero,directions_zero]
  norm_num [LocalSlider.centres,LocalSlider.offset,EndpointGeometry.centres,
    EndpointGeometry.directions,Sq17.sq]

/-- Vanishing transverse/rotational perturbations force width at least the
exact endpoint, even in a horizontally translated container. Only squares
1 and 7 are needed; no condition on the omitted square6 is involved. -/
theorem side_le_of_zero_motion (a b z : ℝ) (h : Fin 45 → ℝ)
    (hh : ∀ j, h j = 0) (lower L : ℝ)
    (hfit : ∀ i, ∀ p ∈ motionSquare a b z h i, lower ≤ p.1 ∧ p.1 ≤ lower+L) :
    side ≤ L := by
  have he : h = fun _ => 0 := funext hh
  subst h
  have hl := (hfit 0 _ (zero_motion_left a b z)).1
  have hr := (hfit 6 _ (zero_motion_right a b z)).2
  change lower ≤ 0 at hl
  change side ≤ lower+L at hr
  linarith

#print axioms side_le_of_zero_motion
end
end Sq17.LocalPerturbation
