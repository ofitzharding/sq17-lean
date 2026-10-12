import Sq17Lean.CaptureChartPacking
import Sq17Lean.LocalRigidityCertified

/-! Exact width obstruction in the certified capture neighborhood. This theorem
still requires chart membership; the global traces must establish it for the
surviving case. It is not an unconditional optimality theorem. -/
namespace Sq17.CaptureChart
open Sq17.EndpointGeometry Sq17.LocalPerturbation

theorem side_eq_of_local_capture (L sigma : ℝ)
    (P : Fin 17 → ℝ × ℝ) (θ : Fin 17 → ℝ)
    (hL : L ≤ side)
    (hf : ∀ i, poseSquare P θ i ⊆ CenteredOrbitFrame.traceBox L sigma)
    (hd : ∀ i j, i ≠ j → Disjoint
      (interior (poseSquare P θ i)) (interior (poseSquare P θ j)))
    (hb : CoordinateBounds (chartCentres sigma P) (chartAngles θ) ((1 : ℝ)/10000000))
    (hbox : LocalSlider.sliderBox (sliderA (chartCentres sigma P))
      (sliderB (chartCentres sigma P)) (sliderZ (chartCentres sigma P))) :
    L = side := by
  apply le_antisymm hL
  apply capture_side_le_of_encoded_zero L sigma P θ hf
  exact LocalRigidity.geometric_local_rigidity hbox
    (encode (chartCentres sigma P) (chartAngles θ))
    (encode_bounded _ _ _ hb)
    (capture_geometricRows_lower L sigma P θ hL hf hd hb hbox)

end Sq17.CaptureChart

#print axioms Sq17.CaptureChart.side_eq_of_local_capture
