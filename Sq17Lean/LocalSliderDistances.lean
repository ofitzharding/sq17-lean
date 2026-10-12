import Sq17Lean.LocalSliderGeometry
import Sq17Lean.EndpointPacking

namespace Sq17.LocalSlider
open Sq17.EndpointGeometry Sq17.WallCapacity

 theorem offset_bounds {a b z : ℝ} (h : sliderBox a b z) (i : Fin 17) :
    |(offset a b z i).1| ≤ 1/4 ∧ |(offset a b z i).2| ≤ 1/4 := by
  have ha : |a| ≤ 1/4 := by rw [abs_le]; constructor <;> linarith [h.1,h.2.1]
  have hb : |b| ≤ 1/4 := by rw [abs_le]; constructor <;> linarith [h.2.2.1,h.2.2.2.1]
  have hz : |z| ≤ 1/4 := by rw [abs_le]; constructor <;> linarith [h.2.2.2.2.1,h.2.2.2.2.2]
  have hc : |c| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [cs_unit,sq_nonneg s]
  have hs : |s| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [cs_unit,sq_nonneg c]
  have prod (x y : ℝ) (hx : |x| ≤ 1/4) (hy : |y| ≤ 1) : |x*y| ≤ 1/4 := by
    rw [abs_mul]
    nlinarith [mul_nonneg (abs_nonneg x) (sub_nonneg.mpr hy)]
  unfold offset
  split_ifs
  · simpa using And.intro ha (show |(0:ℝ)| ≤ 1/4 by norm_num)
  · simpa using And.intro (prod b s hb hs) (prod b c hb hc)
  · simpa using And.intro (prod z s hz hs) (prod z c hz hc)
  · norm_num

 theorem centres_abs_le_five {a b z : ℝ} (h : sliderBox a b z) (i : Fin 17) :
    |(centres a b z i).1| ≤ 5 ∧ |(centres a b z i).2| ≤ 5 := by
  have hp := squares_contained i (interior_subset (square_center_mem_interior
    (EndpointGeometry.centres i).1 (EndpointGeometry.centres i).2
    (directions i).1 (directions i).2))
  change 0 ≤ (EndpointGeometry.centres i).1 ∧ (EndpointGeometry.centres i).1 ≤ side ∧
    0 ≤ (EndpointGeometry.centres i).2 ∧ (EndpointGeometry.centres i).2 ≤ side at hp
  have hoff := offset_bounds h i
  have hside : side + 1/4 ≤ 5 := by
    have hb := EndpointIntervals.side_bounds.2
    norm_num at hb
    linarith
  simp only [centres,Prod.fst_add,Prod.snd_add]
  have hx := abs_add_le (EndpointGeometry.centres i).1 (offset a b z i).1
  have hy := abs_add_le (EndpointGeometry.centres i).2 (offset a b z i).2
  rw [abs_of_nonneg hp.1] at hx
  rw [abs_of_nonneg hp.2.2.1] at hy
  constructor <;> linarith [hoff.1,hoff.2,hp.2.1,hp.2.2.2]

 theorem pair_distances_le_ten {a b z : ℝ} (h : sliderBox a b z) (i j : Fin 17) :
    |(centres a b z j).1-(centres a b z i).1| ≤ 10 ∧
    |(centres a b z j).2-(centres a b z i).2| ≤ 10 := by
  have hi := centres_abs_le_five h i
  have hj := centres_abs_le_five h j
  have hx := abs_sub (centres a b z j).1 (centres a b z i).1
  have hy := abs_sub (centres a b z j).2 (centres a b z i).2
  constructor <;> linarith [hi.1,hi.2,hj.1,hj.2]

end Sq17.LocalSlider
#print axioms Sq17.LocalSlider.pair_distances_le_ten
