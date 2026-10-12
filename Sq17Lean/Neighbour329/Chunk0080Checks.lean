import Sq17Lean.Neighbour329.Chunk0080Data
import Sq17Lean.Neighbour329.Chunk0079Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0080
def freshBoundsRaw : String := ""

def freshBounds : Array (CaptureTableFast.Bounds × CaptureTableFast.Bounds) := CaptureTableFast.decodeBounds 1000000 (parseInts freshBoundsRaw) 0 #[]
theorem fresh_checked : CaptureTableFast.freshCheck 44 table previousEntryIds.size freshBounds = true := by native_decide
theorem inherited_checked : CaptureTableFast.inheritedCheck Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0079.table table previousEntryIds = true := by native_decide
end Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0080

namespace Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0080
theorem initial_length : S0.length = 17 := by native_decide
theorem final_length : E.length = 17 := by native_decide
theorem boundary_checked : sameGeometry Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0079.table table Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0079.E S0 = true := by native_decide
end Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0080
