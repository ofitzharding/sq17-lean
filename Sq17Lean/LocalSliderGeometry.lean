import Sq17Lean.EndpointContacts

/-! The exact three-slider family. Indices are zero-based; the source square
labels 5, 11, and 13 are therefore indices 4, 10, and 12.
The designated wall and pair equalities hold for arbitrary real sliders.
The closed slider box is used only for the uniform inequality certificates. -/
namespace Sq17.LocalSlider
open Sq17.EndpointGeometry
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def offset (a b z : ℝ) (i : Fin 17) : ℝ × ℝ :=
  if i = 4 then (-a,0) else if i = 10 then (b*s,-b*c)
  else if i = 12 then (-z*s,z*c) else (0,0)

def centres (a b z : ℝ) (i : Fin 17) : ℝ × ℝ :=
  EndpointGeometry.centres i + offset a b z i

def sliderBox (a b z : ℝ) : Prop :=
  0 ≤ a ∧ a ≤ 1/4 ∧ -(1/2500) ≤ b ∧ b ≤ 1/12 ∧ -(1/8) ≤ z ∧ z ≤ 1/16

def pairGap (a b z : ℝ) (i j : Fin 17) (k : Fin 6) : ℝ :=
  (axes k).1*((centres a b z j).1-(centres a b z i).1)+
    (axes k).2*((centres a b z j).2-(centres a b z i).2)-
    supportTable (directionKind i) (axisKind k)-supportTable (directionKind j) (axisKind k)

def wallGap (a b z : ℝ) (i : Fin 17) (k : Fin 4) : ℝ :=
  (![ (centres a b z i).1,side-(centres a b z i).1,
    (centres a b z i).2,side-(centres a b z i).2] k)-supportTable (directionKind i) 0

theorem centres_zero (i : Fin 17) : centres 0 0 0 i = EndpointGeometry.centres i := by
  simp [centres,offset]

/-- The exact midpoint and half-width bounds of the closed slider box. -/
theorem sliderBox_centered {a b z : ℝ} (h : sliderBox a b z) :
    |a-1/8| ≤ 1/8 ∧ |b-311/7500| ≤ 157/3750 ∧ |z+1/32| ≤ 3/32 := by
  rcases h with ⟨ha,ha',hb,hb',hz,hz'⟩
  constructor
  · rw [abs_le]; constructor <;> linarith
  constructor
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

/-- A coefficientwise affine bound, valid on the entire closed slider box. -/
theorem affine_upper {a b z : ℝ} (h : sliderBox a b z) (g A B C : ℝ) :
    g+a*A+b*B+z*C ≤
      g+(1/8)*A+(311/7500)*B-(1/32)*C+
        (1/8)*|A|+(157/3750)*|B|+(3/32)*|C| := by
  obtain ⟨ha,hb,hz⟩ := sliderBox_centered h
  have hA := mul_le_mul_of_nonneg_right ha (abs_nonneg A)
  have hB := mul_le_mul_of_nonneg_right hb (abs_nonneg B)
  have hC := mul_le_mul_of_nonneg_right hz (abs_nonneg C)
  rw [← abs_mul] at hA hB hC
  have hA' := le_abs_self ((a-1/8)*A)
  have hB' := le_abs_self ((b-311/7500)*B)
  have hC' := le_abs_self ((z+1/32)*C)
  nlinarith

theorem pair_contact_1_2 (a b z : ℝ) : pairGap a b z 0 1 0 = 0 := by
  have he : pairGap a b z 0 1 0 = EndpointGeometry.pairGap 0 1 0 := by
    norm_num [pairGap,EndpointGeometry.pairGap,centres,offset,axes]
    <;> ring
  rw [he,EndpointGeometry.pair_contact_1_2]

theorem pair_contact_1_3 (a b z : ℝ) : pairGap a b z 0 2 1 = 0 := by
  have he : pairGap a b z 0 2 1 = EndpointGeometry.pairGap 0 2 1 := by
    norm_num [pairGap,EndpointGeometry.pairGap,centres,offset,axes]
    <;> ring
  rw [he,EndpointGeometry.pair_contact_1_3]

theorem pair_contact_5_7 (a b z : ℝ) : pairGap a b z 4 6 1 = 0 := by
  have he : pairGap a b z 4 6 1 = EndpointGeometry.pairGap 4 6 1 := by
    norm_num [pairGap,EndpointGeometry.pairGap,centres,offset,axes]
    <;> ring
  rw [he,EndpointGeometry.pair_contact_5_7]

theorem pair_contact_3_9 (a b z : ℝ) : pairGap a b z 2 8 1 = 0 := by
  have he : pairGap a b z 2 8 1 = EndpointGeometry.pairGap 2 8 1 := by
    norm_num [pairGap,EndpointGeometry.pairGap,centres,offset,axes]
    <;> ring
  rw [he,EndpointGeometry.pair_contact_3_9]

theorem pair_contact_9_10 (a b z : ℝ) : pairGap a b z 8 9 2 = 0 := by
  have he : pairGap a b z 8 9 2 = EndpointGeometry.pairGap 8 9 2 := by
    norm_num [pairGap,EndpointGeometry.pairGap,centres,offset,axes]
    <;> ring
  rw [he,EndpointGeometry.pair_contact_9_10]

theorem pair_contact_4_10 (a b z : ℝ) : pairGap a b z 3 9 3 = 0 := by
  have he : pairGap a b z 3 9 3 = EndpointGeometry.pairGap 3 9 3 := by
    norm_num [pairGap,EndpointGeometry.pairGap,centres,offset,axes]
    <;> ring
  rw [he,EndpointGeometry.pair_contact_4_10]

theorem pair_contact_3_11 (a b z : ℝ) : pairGap a b z 2 10 2 = 0 := by
  have he : pairGap a b z 2 10 2 = EndpointGeometry.pairGap 2 10 2 := by
    norm_num [pairGap,EndpointGeometry.pairGap,centres,offset,axes]
    <;> ring
  rw [he,EndpointGeometry.pair_contact_3_11]

theorem pair_contact_11_12 (a b z : ℝ) : pairGap a b z 10 11 2 = 0 := by
  have he : pairGap a b z 10 11 2 = EndpointGeometry.pairGap 10 11 2 := by
    norm_num [pairGap,EndpointGeometry.pairGap,centres,offset,axes]
    <;> ring
  rw [he,EndpointGeometry.pair_contact_11_12]

theorem pair_contact_10_12 (a b z : ℝ) : pairGap a b z 9 11 3 = 0 := by
  have he : pairGap a b z 9 11 3 = EndpointGeometry.pairGap 9 11 3 := by
    norm_num [pairGap,EndpointGeometry.pairGap,centres,offset,axes]
    <;> ring
  rw [he,EndpointGeometry.pair_contact_10_12]

theorem pair_contact_2_13 (a b z : ℝ) : pairGap a b z 1 12 2 = 0 := by
  have he : pairGap a b z 1 12 2 = EndpointGeometry.pairGap 1 12 2 := by
    norm_num [pairGap,EndpointGeometry.pairGap,centres,offset,axes]
    <;> ring
  rw [he,EndpointGeometry.pair_contact_2_13]

theorem pair_contact_13_14 (a b z : ℝ) : pairGap a b z 12 13 2 = 0 := by
  have he : pairGap a b z 12 13 2 = EndpointGeometry.pairGap 12 13 2 := by
    norm_num [pairGap,EndpointGeometry.pairGap,centres,offset,axes]
    <;> ring
  rw [he,EndpointGeometry.pair_contact_13_14]

theorem pair_contact_12_14 (a b z : ℝ) : pairGap a b z 11 13 3 = 0 := by
  have he : pairGap a b z 11 13 3 = EndpointGeometry.pairGap 11 13 3 := by
    norm_num [pairGap,EndpointGeometry.pairGap,centres,offset,axes]
    <;> ring
  rw [he,EndpointGeometry.pair_contact_12_14]

theorem pair_contact_10_15 (a b z : ℝ) : pairGap a b z 9 14 2 = 0 := by
  have he : pairGap a b z 9 14 2 = EndpointGeometry.pairGap 9 14 2 := by
    norm_num [pairGap,EndpointGeometry.pairGap,centres,offset,axes]
    <;> ring
  rw [he,EndpointGeometry.pair_contact_10_15]

theorem pair_contact_14_17 (a b z : ℝ) : pairGap a b z 13 16 2 = 0 := by
  have he : pairGap a b z 13 16 2 = EndpointGeometry.pairGap 13 16 2 := by
    norm_num [pairGap,EndpointGeometry.pairGap,centres,offset,axes]
    <;> ring
  rw [he,EndpointGeometry.pair_contact_14_17]

theorem pair_contact_15_16 (a b z : ℝ) : pairGap a b z 14 15 4 = 0 := by
  have he : pairGap a b z 14 15 4 = EndpointGeometry.pairGap 14 15 4 := by
    norm_num [pairGap,EndpointGeometry.pairGap,centres,offset,axes]
    <;> ring
  rw [he,EndpointGeometry.pair_contact_15_16]

theorem pair_contact_16_8 (a b z : ℝ) : pairGap a b z 15 7 5 = 0 := by
  have he : pairGap a b z 15 7 5 = EndpointGeometry.pairGap 15 7 5 := by
    norm_num [pairGap,EndpointGeometry.pairGap,centres,offset,axes]
    <;> ring
  rw [he,EndpointGeometry.pair_contact_16_8]

theorem pair_contact_14_7 (a b z : ℝ) : pairGap a b z 13 6 3 = 0 := by
  have he : pairGap a b z 13 6 3 = EndpointGeometry.pairGap 13 6 3 := by
    norm_num [pairGap,EndpointGeometry.pairGap,centres,offset,axes]
    <;> ring
  rw [he,EndpointGeometry.pair_contact_14_7]

theorem pair_contact_16_17 (a b z : ℝ) : pairGap a b z 15 16 4 = 0 := by
  have he : pairGap a b z 15 16 4 = EndpointGeometry.pairGap 15 16 4 := by
    norm_num [pairGap,EndpointGeometry.pairGap,centres,offset,axes]
    <;> ring
  rw [he,EndpointGeometry.pair_contact_16_17]

theorem pair_contact_12_16 (a b z : ℝ) : pairGap a b z 11 15 2 = 0 := by
  have he : pairGap a b z 11 15 2 = EndpointGeometry.pairGap 11 15 2 := by
    norm_num [pairGap,EndpointGeometry.pairGap,centres,offset,axes]
    <;> ring
  rw [he,EndpointGeometry.pair_contact_12_16]

theorem wall_contact_1_0 (a b z : ℝ) : wallGap a b z 0 0 = 0 := by
  have he : wallGap a b z 0 0 = EndpointGeometry.wallGap 0 0 := by
    norm_num [wallGap,EndpointGeometry.wallGap,centres,offset]
  rw [he,EndpointGeometry.wall_contact_1_0]

theorem wall_contact_1_2 (a b z : ℝ) : wallGap a b z 0 2 = 0 := by
  have he : wallGap a b z 0 2 = EndpointGeometry.wallGap 0 2 := by
    norm_num [wallGap,EndpointGeometry.wallGap,centres,offset]
  rw [he,EndpointGeometry.wall_contact_1_2]

theorem wall_contact_2_2 (a b z : ℝ) : wallGap a b z 1 2 = 0 := by
  have he : wallGap a b z 1 2 = EndpointGeometry.wallGap 1 2 := by
    norm_num [wallGap,EndpointGeometry.wallGap,centres,offset]
  rw [he,EndpointGeometry.wall_contact_2_2]

theorem wall_contact_3_0 (a b z : ℝ) : wallGap a b z 2 0 = 0 := by
  have he : wallGap a b z 2 0 = EndpointGeometry.wallGap 2 0 := by
    norm_num [wallGap,EndpointGeometry.wallGap,centres,offset]
  rw [he,EndpointGeometry.wall_contact_3_0]

theorem wall_contact_4_0 (a b z : ℝ) : wallGap a b z 3 0 = 0 := by
  have he : wallGap a b z 3 0 = EndpointGeometry.wallGap 3 0 := by
    norm_num [wallGap,EndpointGeometry.wallGap,centres,offset]
  rw [he,EndpointGeometry.wall_contact_4_0]

theorem wall_contact_4_3 (a b z : ℝ) : wallGap a b z 3 3 = 0 := by
  have he : wallGap a b z 3 3 = EndpointGeometry.wallGap 3 3 := by
    norm_num [wallGap,EndpointGeometry.wallGap,centres,offset]
  rw [he,EndpointGeometry.wall_contact_4_3]

theorem wall_contact_5_2 (a b z : ℝ) : wallGap a b z 4 2 = 0 := by
  have he : wallGap a b z 4 2 = EndpointGeometry.wallGap 4 2 := by
    norm_num [wallGap,EndpointGeometry.wallGap,centres,offset]
  rw [he,EndpointGeometry.wall_contact_5_2]

theorem wall_contact_7_1 (a b z : ℝ) : wallGap a b z 6 1 = 0 := by
  have he : wallGap a b z 6 1 = EndpointGeometry.wallGap 6 1 := by
    norm_num [wallGap,EndpointGeometry.wallGap,centres,offset]
  rw [he,EndpointGeometry.wall_contact_7_1]

theorem wall_contact_8_1 (a b z : ℝ) : wallGap a b z 7 1 = 0 := by
  have he : wallGap a b z 7 1 = EndpointGeometry.wallGap 7 1 := by
    norm_num [wallGap,EndpointGeometry.wallGap,centres,offset]
  rw [he,EndpointGeometry.wall_contact_8_1]

theorem wall_contact_8_3 (a b z : ℝ) : wallGap a b z 7 3 = 0 := by
  have he : wallGap a b z 7 3 = EndpointGeometry.wallGap 7 3 := by
    norm_num [wallGap,EndpointGeometry.wallGap,centres,offset]
  rw [he,EndpointGeometry.wall_contact_8_3]

theorem wall_contact_9_0 (a b z : ℝ) : wallGap a b z 8 0 = 0 := by
  have he : wallGap a b z 8 0 = EndpointGeometry.wallGap 8 0 := by
    norm_num [wallGap,EndpointGeometry.wallGap,centres,offset]
  rw [he,EndpointGeometry.wall_contact_9_0]

theorem wall_contact_15_3 (a b z : ℝ) : wallGap a b z 14 3 = 0 := by
  have he : wallGap a b z 14 3 = EndpointGeometry.wallGap 14 3 := by
    norm_num [wallGap,EndpointGeometry.wallGap,centres,offset]
  rw [he,EndpointGeometry.wall_contact_15_3]

theorem wall_contact_17_1 (a b z : ℝ) : wallGap a b z 16 1 = 0 := by
  have he : wallGap a b z 16 1 = EndpointGeometry.wallGap 16 1 := by
    norm_num [wallGap,EndpointGeometry.wallGap,centres,offset]
  rw [he,EndpointGeometry.wall_contact_17_1]

def contactPairs : Fin 19 → Fin 17 × Fin 17 × Fin 6 := ![(0,1,0),(0,2,1),(4,6,1),(2,8,1),(8,9,2),(3,9,3),(2,10,2),(10,11,2),(9,11,3),(1,12,2),(12,13,2),(11,13,3),(9,14,2),(13,16,2),(14,15,4),(15,7,5),(13,6,3),(15,16,4),(11,15,2)]
def wallAnchors : Fin 13 → Fin 17 × Fin 4 := ![(0,0),(0,2),(1,2),(2,0),(3,0),(3,3),(4,2),(6,1),(7,1),(7,3),(8,0),(14,3),(16,1)]
theorem contact_tight (a b z : ℝ) (k : Fin 19) :
    pairGap a b z (contactPairs k).1 (contactPairs k).2.1 (contactPairs k).2.2 = 0 := by
  fin_cases k
  · exact pair_contact_1_2 a b z
  · exact pair_contact_1_3 a b z
  · exact pair_contact_5_7 a b z
  · exact pair_contact_3_9 a b z
  · exact pair_contact_9_10 a b z
  · exact pair_contact_4_10 a b z
  · exact pair_contact_3_11 a b z
  · exact pair_contact_11_12 a b z
  · exact pair_contact_10_12 a b z
  · exact pair_contact_2_13 a b z
  · exact pair_contact_13_14 a b z
  · exact pair_contact_12_14 a b z
  · exact pair_contact_10_15 a b z
  · exact pair_contact_14_17 a b z
  · exact pair_contact_15_16 a b z
  · exact pair_contact_16_8 a b z
  · exact pair_contact_14_7 a b z
  · exact pair_contact_16_17 a b z
  · exact pair_contact_12_16 a b z
theorem wall_tight (a b z : ℝ) (k : Fin 13) :
    wallGap a b z (wallAnchors k).1 (wallAnchors k).2 = 0 := by
  fin_cases k
  · exact wall_contact_1_0 a b z
  · exact wall_contact_1_2 a b z
  · exact wall_contact_2_2 a b z
  · exact wall_contact_3_0 a b z
  · exact wall_contact_4_0 a b z
  · exact wall_contact_4_3 a b z
  · exact wall_contact_5_2 a b z
  · exact wall_contact_7_1 a b z
  · exact wall_contact_8_1 a b z
  · exact wall_contact_8_3 a b z
  · exact wall_contact_9_0 a b z
  · exact wall_contact_15_3 a b z
  · exact wall_contact_17_1 a b z

def tangentialOffset (a b z : ℝ) (i j : Fin 17) (k : Fin 6) : ℝ :=
  -(axes k).2*((centres a b z j).1-(centres a b z i).1)+
    (axes k).1*((centres a b z j).2-(centres a b z i).2)

theorem offset_1_2 (a b z : ℝ) : tangentialOffset a b z 0 1 0 = 0 := by
  norm_num [tangentialOffset,centres,offset,axes,EndpointGeometry.centres]
theorem offset_1_3 (a b z : ℝ) : tangentialOffset a b z 0 2 1 = 0 := by
  norm_num [tangentialOffset,centres,offset,axes,EndpointGeometry.centres]
theorem offset_5_7 (a b z : ℝ) : tangentialOffset a b z 4 6 1 = -a := by
  norm_num [tangentialOffset,centres,offset,axes,EndpointGeometry.centres]
  <;> ring

theorem endpoint_denominators_positive :
    0 < t ∧ 0 < t+1 ∧ 0 < 1-t*t ∧ 0 < 1+t*t ∧
      0 < 1+beta*beta ∧ 0 < 1+2*t-t*t ∧ 0 < c ∧ 0 < s := by
  have ht := t_bounds
  have ht0 : 0 ≤ t := by linarith
  exact ⟨by linarith,by linarith,
    by nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) ht0],
    denominator_positive.1,denominator_positive.2.1,denominator_positive.2.2,
    cs_positive.1,cs_positive.2⟩

end
end Sq17.LocalSlider
#print axioms Sq17.LocalSlider.contact_tight
#print axioms Sq17.LocalSlider.wall_tight
#print axioms Sq17.LocalSlider.affine_upper
