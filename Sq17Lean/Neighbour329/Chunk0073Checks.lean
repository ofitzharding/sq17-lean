import Sq17Lean.Neighbour329.Chunk0073Data
import Sq17Lean.Neighbour329.Chunk0072Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0073
def freshBoundsRaw : String := ""

def freshBounds : Array (CaptureTableFast.Bounds × CaptureTableFast.Bounds) := CaptureTableFast.decodeBounds 1000000 (parseInts freshBoundsRaw) 0 #[]
theorem fresh_checked : CaptureTableFast.freshCheck 44 table previousEntryIds.size freshBounds = true := by native_decide
theorem inherited_checked : CaptureTableFast.inheritedCheck Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0072.table table previousEntryIds = true := by native_decide
end Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0073

namespace Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0073
theorem initial_length : S0.length = 17 := by native_decide
theorem final_length : E.length = 17 := by native_decide
theorem boundary_checked : sameGeometry Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0072.table table Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0072.E S0 = true := by native_decide
end Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0073
