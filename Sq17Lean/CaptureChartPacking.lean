import Sq17Lean.CaptureChartFrame
import Sq17Lean.LocalChartGeometry

/-! Exact relabeling and pose transport from the captured representative to
the local geometric theorem. Terminal membership/bounds remain to be checked
against the actual capture certificate. -/
namespace Sq17.CaptureChart
open Sq17.EndpointGeometry Sq17.LocalPerturbation
noncomputable section

/-- The label-to-owner permutation in the independently audited capture chart. -/
def owners : Fin 17 → Fin 17 := ![11,2,15,1,16,12,0,6,3,9,4,5,13,7,10,8,14]
theorem owners_injective : Function.Injective owners := by decide +kernel

def chartCentres (sigma : ℝ) (P : Fin 17 → ℝ × ℝ) (i : Fin 17) : ℝ × ℝ :=
  turn sigma (P (owners i))
def chartAngles (θ : Fin 17 → ℝ) (i : Fin 17) : ℝ := θ (owners i)

theorem chart_pose_image (sigma : ℝ) (P : Fin 17 → ℝ × ℝ) (θ : Fin 17 → ℝ)
    (i : Fin 17) :
    poseSquare (chartCentres sigma P) (chartAngles θ) i =
      turn sigma '' poseSquare P θ (owners i) := by
  exact (turn_square_image sigma (P (owners i))
    (Real.cos (θ (owners i)),Real.sin (θ (owners i)))).symm

theorem chart_pose_fit (L sigma : ℝ) (P : Fin 17 → ℝ × ℝ) (θ : Fin 17 → ℝ)
    (hf : ∀ i, poseSquare P θ i ⊆ CenteredOrbitFrame.traceBox L sigma) :
    ∀ i, poseSquare (chartCentres sigma P) (chartAngles θ) i ⊆ chartBox L := by
  intro i
  exact turn_square_fit L sigma (P (owners i))
    (Real.cos (θ (owners i)),Real.sin (θ (owners i))) (hf (owners i))

theorem chart_pose_disjoint (sigma : ℝ) (P : Fin 17 → ℝ × ℝ) (θ : Fin 17 → ℝ)
    (hd : ∀ i j, i ≠ j → Disjoint (interior (poseSquare P θ i)) (interior (poseSquare P θ j))) :
    ∀ i j, i ≠ j → Disjoint
      (interior (poseSquare (chartCentres sigma P) (chartAngles θ) i))
      (interior (poseSquare (chartCentres sigma P) (chartAngles θ) j)) := by
  intro i j hij
  exact turn_square_disjoint sigma (P (owners i)) (P (owners j))
    (Real.cos (θ (owners i)),Real.sin (θ (owners i)))
    (Real.cos (θ (owners j)),Real.sin (θ (owners j)))
    (hd _ _ (fun he => hij (owners_injective he)))

theorem capture_geometricRows_lower (L sigma : ℝ) (P : Fin 17 → ℝ × ℝ) (θ : Fin 17 → ℝ)
    (hL : L ≤ side)
    (hf : ∀ i, poseSquare P θ i ⊆ CenteredOrbitFrame.traceBox L sigma)
    (hd : ∀ i j, i ≠ j → Disjoint (interior (poseSquare P θ i)) (interior (poseSquare P θ j)))
    (hb : CoordinateBounds (chartCentres sigma P) (chartAngles θ) ((1:ℝ)/10000000))
    (hbox : LocalSlider.sliderBox (sliderA (chartCentres sigma P))
      (sliderB (chartCentres sigma P)) (sliderZ (chartCentres sigma P))) :
    ∀ row, -50*(LocalRigidity.maxAbs (encode (chartCentres sigma P) (chartAngles θ)))^2 ≤
      geometricRows (sliderA (chartCentres sigma P)) (sliderB (chartCentres sigma P))
        (sliderZ (chartCentres sigma P)) (encode (chartCentres sigma P) (chartAngles θ)) row := by
  apply encoded_geometricRows_lower _ _ hbox hb
  · intro i
    exact (chart_pose_fit L sigma P θ hf i).trans (chartBox_subset_endpoint hL)
  · exact chart_pose_disjoint sigma P θ hd

theorem capture_side_le_of_encoded_zero (L sigma : ℝ) (P : Fin 17 → ℝ × ℝ) (θ : Fin 17 → ℝ)
    (hf : ∀ i, poseSquare P θ i ⊆ CenteredOrbitFrame.traceBox L sigma)
    (hz : ∀ j, encode (chartCentres sigma P) (chartAngles θ) j = 0) : side ≤ L := by
  apply pose_side_le_of_encoded_zero _ _ hz ((side-L)/2) L
  intro i p hp
  have h := chart_pose_fit L sigma P θ hf i hp
  exact ⟨h.1,by linarith [h.2.1]⟩

#print axioms owners_injective
#print axioms capture_geometricRows_lower
#print axioms capture_side_le_of_encoded_zero
end
end Sq17.CaptureChart
