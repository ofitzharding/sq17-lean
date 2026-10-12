import Sq17Lean.LocalChartBounds
import Sq17Lean.LocalGeometricRowsLower

/-! Transfer genuine square poses into the local rows. Only the sixteen
constrained owners are reconstructed; the unused owner6 is never assigned
a disjointness property that did not follow from the original packing. -/
namespace Sq17.LocalPerturbation
open Sq17.EndpointGeometry
noncomputable section

def poseSquare (P : Fin 17 → ℝ × ℝ) (θ : Fin 17 → ℝ) (i : Fin 17) : Set (ℝ × ℝ) :=
  Sq17.sq (P i).1 (P i).2 (Real.cos (θ i)) (Real.sin (θ i))

theorem motionSquare_encode (P : Fin 17 → ℝ × ℝ) (θ : Fin 17 → ℝ)
    (i : Fin 17) (hi : i ≠ 5) :
    motionSquare (sliderA P) (sliderB P) (sliderZ P) (encode P θ) i = poseSquare P θ i := by
  simp only [motionSquare,centres_encode P θ i hi,directions_encode P θ i hi,poseSquare]

theorem omitted_motionSquare (a b z : ℝ) (h : Fin 45 → ℝ) :
    motionSquare a b z h 5 = EndpointGeometry.squares 5 := by
  simp [motionSquare,centres,translation,directions,angular,baseAngle,
    LocalSlider.centres,LocalSlider.offset,EndpointGeometry.squares,EndpointGeometry.directions]

theorem fitsEndpoint_encode (P : Fin 17 → ℝ × ℝ) (θ : Fin 17 → ℝ)
    (hf : ∀ i, poseSquare P θ i ⊆
      {p | 0 ≤ p.1 ∧ p.1 ≤ side ∧ 0 ≤ p.2 ∧ p.2 ≤ side}) :
    FitsEndpoint (sliderA P) (sliderB P) (sliderZ P) (encode P θ) := by
  intro i
  change motionSquare _ _ _ _ i ⊆ _
  by_cases hi : i = 5
  · subst i
    rw [omitted_motionSquare]
    exact EndpointGeometry.squares_contained 5
  · rw [motionSquare_encode P θ i hi]
    exact hf i

theorem contactDisjoint_encode (P : Fin 17 → ℝ × ℝ) (θ : Fin 17 → ℝ)
    (hd : ∀ i j, i ≠ j → Disjoint (interior (poseSquare P θ i)) (interior (poseSquare P θ j))) :
    ContactDisjoint (sliderA P) (sliderB P) (sliderZ P) (encode P θ) := by
  intro r
  have hi : (LocalSlider.contactPairs r).1 ≠ 5 := by fin_cases r <;> decide
  have hj : (LocalSlider.contactPairs r).2.1 ≠ 5 := by fin_cases r <;> decide
  have hij : (LocalSlider.contactPairs r).1 ≠ (LocalSlider.contactPairs r).2.1 := by
    fin_cases r <;> decide
  rw [motionSquare_encode P θ _ hi,motionSquare_encode P θ _ hj]
  exact hd _ _ hij

theorem encoded_geometricRows_lower (P : Fin 17 → ℝ × ℝ) (θ : Fin 17 → ℝ)
    (hbox : LocalSlider.sliderBox (sliderA P) (sliderB P) (sliderZ P))
    (hb : CoordinateBounds P θ ((1:ℝ)/10000000))
    (hf : ∀ i, poseSquare P θ i ⊆
      {p | 0 ≤ p.1 ∧ p.1 ≤ side ∧ 0 ≤ p.2 ∧ p.2 ≤ side})
    (hd : ∀ i j, i ≠ j → Disjoint (interior (poseSquare P θ i)) (interior (poseSquare P θ j))) :
    ∀ row, -50*(LocalRigidity.maxAbs (encode P θ))^2 ≤
      geometricRows (sliderA P) (sliderB P) (sliderZ P) (encode P θ) row :=
  geometricRows_lower _ hbox (encode_bounded P θ _ hb) (fitsEndpoint_encode P θ hf)
    (contactDisjoint_encode P θ hd)

/-- The width obstruction applies to the original packing, including when
its unused square differs from the chart's fixed placeholder. -/
theorem pose_side_le_of_encoded_zero (P : Fin 17 → ℝ × ℝ) (θ : Fin 17 → ℝ)
    (hz : ∀ j, encode P θ j = 0) (lower L : ℝ)
    (hf : ∀ i, ∀ p ∈ poseSquare P θ i, lower ≤ p.1 ∧ p.1 ≤ lower+L) : side ≤ L := by
  have he : encode P θ = fun _ => 0 := funext hz
  have hl := zero_motion_left (sliderA P) (sliderB P) (sliderZ P)
  have hr := zero_motion_right (sliderA P) (sliderB P) (sliderZ P)
  rw [← he,motionSquare_encode P θ 0 (by decide)] at hl
  rw [← he,motionSquare_encode P θ 6 (by decide)] at hr
  have hl' := (hf 0 _ hl).1
  have hr' := (hf 6 _ hr).2
  change lower ≤ 0 at hl'
  change side ≤ lower+L at hr'
  linarith

#print axioms encoded_geometricRows_lower
#print axioms pose_side_le_of_encoded_zero
end
end Sq17.LocalPerturbation
