import Sq17Lean.CaptureTerminalLocalChart
import Sq17Lean.CaptureLocalOptimality

/-! The captured-family local theorem, composed.

Any seventeen unit squares that are represented by the authoritative capture
terminal state, fit the centred trace box of side `L ≤ side`, and have pairwise
disjoint interiors, force `L = side`.

Scope. The hypothesis `hrep` (representation by `terminalState`) is exactly what
the global capture trace must supply. That trace is externally replayed but is
not a Lean theorem, so this result does not by itself prove global optimality. -/
namespace Sq17.CaptureChart
open Sq17.Propagation Sq17.EndpointGeometry Sq17.LocalPerturbation

theorem side_eq_of_terminal_representation (L : ℝ) (p : Fin 17 → AnglePose)
    (hL : L ≤ side)
    (hrep : Represents (stateDomains terminalState) p)
    (hfit : ∀ i, (p i).square ⊆ CenteredOrbitFrame.traceBox L terminalSigma)
    (hd : ∀ i j, i ≠ j →
      Disjoint (interior (p i).square) (interior (p j).square)) :
    L = side := by
  have hf : ∀ i, poseSquare (fun i => (p i).center) (fun i => (p i).angle) i ⊆
      CenteredOrbitFrame.traceBox L terminalSigma := fun i => hfit i
  have hdis : ∀ i j, i ≠ j → Disjoint
      (interior (poseSquare (fun i => (p i).center) (fun i => (p i).angle) i))
      (interior (poseSquare (fun i => (p i).center) (fun i => (p i).angle) j)) :=
    fun i j hij => hd i j hij
  exact side_eq_of_local_capture L terminalSigma (fun i => (p i).center)
    (fun i => (p i).angle) hL hf hdis (terminal_coordinate_bounds p hrep)
    (terminal_slider_box L p hrep hL hfit)

end Sq17.CaptureChart

#print axioms Sq17.CaptureChart.side_eq_of_terminal_representation
