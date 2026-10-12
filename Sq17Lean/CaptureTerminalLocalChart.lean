import Sq17Lean.CaptureTerminalStateData
import Sq17Lean.CaptureTerminalBoundsData

/-! Exact chart bounds for every pose represented by the exported authoritative
terminal. Propagation from the initial state to this terminal is a separate
trace theorem; it is not assumed or established by the data export. -/
namespace Sq17.CaptureChart
open Sq17.Propagation Sq17.EndpointGeometry Sq17.LocalPerturbation
noncomputable section

theorem terminal_coordinate_bounds (p : Fin 17 → AnglePose)
    (hrep : Represents (stateDomains terminalState) p) :
    CoordinateBounds (chartCentres terminalSigma (fun i => (p i).center))
      (chartAngles (fun i => (p i).angle)) ((1:ℝ)/10000000) := by
  have h := terminal_coordinateBounds terminalState terminalSigma (1/10000000) p hrep
    (terminalSummary_angleRowsCheck terminalState terminalState_checked)
    (by norm_num; exact terminalSummary_vertexBounds terminalState terminalState_checked)
  norm_num at h
  exact h

theorem terminal_slider_box (L : ℝ) (p : Fin 17 → AnglePose)
    (hrep : Represents (stateDomains terminalState) p) (hL : L ≤ side)
    (hfit : ∀ i, (p i).square ⊆ CenteredOrbitFrame.traceBox L terminalSigma) :
    LocalSlider.sliderBox (sliderA (chartCentres terminalSigma (fun i => (p i).center)))
      (sliderB (chartCentres terminalSigma (fun i => (p i).center)))
      (sliderZ (chartCentres terminalSigma (fun i => (p i).center))) := by
  apply terminal_sliderBox terminalState terminalSigma ((1:ℝ)/10000000) p hrep
    (terminalSummary_vertexBounds terminalState terminalState_checked)
  intro q hq
  have h := chart_pose_fit L terminalSigma (fun i => (p i).center)
    (fun i => (p i).angle) hfit 4 hq
  exact (chartBox_subset_endpoint hL h).2.1

end
end Sq17.CaptureChart
#print axioms Sq17.CaptureChart.terminal_coordinate_bounds
#print axioms Sq17.CaptureChart.terminal_slider_box
