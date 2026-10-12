import Sq17Lean.CaptureOpen.Chunk0000Data
import Sq17Lean.CaptureFamily
import Sq17Lean.HalfPlaneWindowSeed
import Sq17Lean.CaptureSeedWindowsData
namespace Sq17.Propagation.HalfPlaneState.CaptureOpen
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem seed_checked : windowSeedOK Chunk0000.table Sq17.CaptureSeedWindows.windows (rosterCells Sq17.CaptureChart.terminalSigma (List.ofFn Sq17.CaptureFamily.roster)) Chunk0000.S0 = true := by native_decide
end Sq17.Propagation.HalfPlaneState.CaptureOpen
