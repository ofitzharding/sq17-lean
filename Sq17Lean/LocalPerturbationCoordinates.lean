import Sq17Lean.LocalSliderGeometry
import Sq17Lean.EndpointAngles

/-! The exact45 nonslider perturbation coordinates used by the local matrix.
Square6 (index5) is omitted: it appears in none of the local constraints.
No feasibility is asserted for the artificial motion of that omitted owner. -/
namespace Sq17.LocalPerturbation
open Sq17.EndpointGeometry
noncomputable section

/-- Coordinates ordered exactly as the checked local matrix: owners in source
order, translation coordinates followed by the angular coordinate. Owners5,11,
and13 retain only their transverse translation after absorbing their slider. -/
def translation (h : Fin 45 → ℝ) : Fin 17 → ℝ × ℝ := ![
  (h 0,h 1),(h 3,h 4),(h 6,h 7),(h 9,h 10),(0,h 12),(0,0),
  (h 14,h 15),(h 17,h 18),(h 20,h 21),(h 23,h 24),(c*h 26,s*h 26),
  (h 28,h 29),(c*h 31,s*h 31),(h 33,h 34),(h 36,h 37),(h 39,h 40),(h 42,h 43)]

def angular (h : Fin 45 → ℝ) : Fin 17 → ℝ := ![
  h 2,h 5,h 8,h 11,h 13,0,h 16,h 19,h 22,h 25,h 27,h 30,h 32,h 35,h 38,h 41,h 44]

def centres (a b z : ℝ) (h : Fin 45 → ℝ) (i : Fin 17) : ℝ × ℝ :=
  LocalSlider.centres a b z i + translation h i

def directions (h : Fin 45 → ℝ) (i : Fin 17) : ℝ × ℝ :=
  (Real.cos (baseAngle i+angular h i),Real.sin (baseAngle i+angular h i))

theorem directions_unit (h : Fin 45 → ℝ) (i : Fin 17) :
    (directions h i).1^2+(directions h i).2^2=1 := Real.cos_sq_add_sin_sq _

private theorem bounded_multiple (u v q : ℝ) (hu : |u| ≤ 1) (hv : |v| ≤ q) :
    |u*v| ≤ q := by
  rw [abs_mul]
  have h := mul_le_mul_of_nonneg_right hu (abs_nonneg v)
  nlinarith

theorem translation_bounds (h : Fin 45 → ℝ) (q : ℝ)
    (hq : 0 ≤ q) (hh : ∀ j, |h j| ≤ q) (i : Fin 17) :
    |(translation h i).1| ≤ q ∧ |(translation h i).2| ≤ q := by
  have hc : |c| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [cs_unit,sq_nonneg s]
  have hs : |s| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [cs_unit,sq_nonneg c]
  have hc' : ∀ j, |c*h j| ≤ q := fun j => bounded_multiple c (h j) q hc (hh j)
  have hs' : ∀ j, |s*h j| ≤ q := fun j => bounded_multiple s (h j) q hs (hh j)
  fin_cases i <;> simp [translation,hh,hq,hc',hs',-abs_mul]

theorem angular_bounds (h : Fin 45 → ℝ) (q : ℝ)
    (hq : 0 ≤ q) (hh : ∀ j, |h j| ≤ q) (i : Fin 17) : |angular h i| ≤ q := by
  fin_cases i <;> simp [angular,hh,hq]

theorem translation_difference_bounds (h : Fin 45 → ℝ) (q : ℝ)
    (hq : 0 ≤ q) (hh : ∀ j, |h j| ≤ q) (i j : Fin 17) :
    |(translation h j).1-(translation h i).1| ≤ 2*q ∧
    |(translation h j).2-(translation h i).2| ≤ 2*q := by
  have hi := translation_bounds h q hq hh i
  have hj := translation_bounds h q hq hh j
  have h1 := abs_sub_le (translation h j).1 0 (translation h i).1
  have h2 := abs_sub_le (translation h j).2 0 (translation h i).2
  simp only [sub_zero,zero_sub,abs_neg] at h1 h2
  constructor <;> linarith

theorem centres_zero (a b z : ℝ) (i : Fin 17) :
    centres a b z (fun _ => 0) i = LocalSlider.centres a b z i := by
  fin_cases i <;> simp [centres,translation]

theorem directions_zero (i : Fin 17) :
    directions (fun _ => 0) i = EndpointGeometry.directions i := by
  have ha : angular (fun _ => (0 : ℝ)) i = 0 := by fin_cases i <;> simp [angular]
  simp only [directions,ha,add_zero,baseAngle_direction]

#print axioms translation_bounds
#print axioms angular_bounds
#print axioms translation_difference_bounds
end
end Sq17.LocalPerturbation
