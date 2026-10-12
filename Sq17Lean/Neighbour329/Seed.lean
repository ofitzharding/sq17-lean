import Sq17Lean.Neighbour329.Chunk0000Data
import Sq17Lean.HalfPlaneTree
namespace Sq17.Propagation.HalfPlaneState.Neighbour329
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def side : ℚ := Chunk0000.side
def shift : ℚ := Chunk0000.shift
def sigma : ℚ := (8668243015428611/36893488147419103232 : ℚ)
def roster : Fin 17 → Fin 24 := ![0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19, 20]
theorem seed_checked : stateSeedOK Chunk0000.table (-initialAngleRadius) initialAngleRadius (rosterCells sigma (List.ofFn roster)) Chunk0000.S0 = true := by native_decide
end Sq17.Propagation.HalfPlaneState.Neighbour329
#print axioms Sq17.Propagation.HalfPlaneState.Neighbour329.seed_checked
