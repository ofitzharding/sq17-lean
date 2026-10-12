import Sq17Lean.CaptureOpen.Chain
import Sq17Lean.CaptureOpen.Seed
import Sq17Lean.CaptureWindowBridge
namespace Sq17.Propagation.HalfPlaneState.CaptureOpen
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem summary_checked : CaptureSummary.summaryCheck Chunk0164.table Chunk0164.E CaptureSummary.summaryTargets = true := by native_decide
theorem capture_excluded (L : ℝ) (hL : L < Sq17.EndpointGeometry.side) (holes : List (Fin 24)) (P : Sq17.HalfPlaneAssembly.RepresentativePacking holes L) (hroster : Sq17.CaptureFamily.sourceRoster.toFinset = holes.toFinsetᶜ) : False :=
  Sq17.CaptureWindowBridge.classifier_capture_excluded Chunk0000.table Chunk0164.table Chunk0000.S0 Chunk0164.E Sq17.CaptureSeedWindows.windows (fun i => (Sq17.CaptureSeedWindows.real_windows_checked i).2.2.le) seed_checked Chunk0000.initial_length propagates summary_checked L hL holes P hroster
end Sq17.Propagation.HalfPlaneState.CaptureOpen
#print axioms Sq17.Propagation.HalfPlaneState.CaptureOpen.capture_excluded
