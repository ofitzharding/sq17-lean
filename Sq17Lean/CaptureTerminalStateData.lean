import Sq17Lean.CaptureTerminalRowsData00
import Sq17Lean.CaptureTerminalRowsData01
import Sq17Lean.CaptureTerminalRowsData02
import Sq17Lean.CaptureTerminalRowsData03
import Sq17Lean.CaptureTerminalRowsData04
import Sq17Lean.CaptureTerminalRowsData05
import Sq17Lean.CaptureTerminalRowsData06
import Sq17Lean.CaptureTerminalRowsData07
import Sq17Lean.CaptureTerminalRowsData08
import Sq17Lean.CaptureTerminalRowsData09
import Sq17Lean.CaptureTerminalRowsData10
import Sq17Lean.CaptureTerminalRowsData11
import Sq17Lean.CaptureTerminalRowsData12
import Sq17Lean.CaptureTerminalRowsData13
import Sq17Lean.CaptureTerminalRowsData14
import Sq17Lean.CaptureTerminalRowsData15
import Sq17Lean.CaptureTerminalRowsData16

namespace Sq17.CaptureChart
open Sq17.Propagation
def terminalState : Fin 17 → List PolygonRow := ![terminalRows0,terminalRows1,terminalRows2,terminalRows3,terminalRows4,terminalRows5,terminalRows6,terminalRows7,terminalRows8,terminalRows9,terminalRows10,terminalRows11,terminalRows12,terminalRows13,terminalRows14,terminalRows15,terminalRows16]
theorem terminalState_checked : ∀ i, (terminalSummary i).check (terminalState i) = true := by
  intro i
  fin_cases i
  · exact terminalRows0_checked
  · exact terminalRows1_checked
  · exact terminalRows2_checked
  · exact terminalRows3_checked
  · exact terminalRows4_checked
  · exact terminalRows5_checked
  · exact terminalRows6_checked
  · exact terminalRows7_checked
  · exact terminalRows8_checked
  · exact terminalRows9_checked
  · exact terminalRows10_checked
  · exact terminalRows11_checked
  · exact terminalRows12_checked
  · exact terminalRows13_checked
  · exact terminalRows14_checked
  · exact terminalRows15_checked
  · exact terminalRows16_checked
end Sq17.CaptureChart
#print axioms Sq17.CaptureChart.terminalState_checked
