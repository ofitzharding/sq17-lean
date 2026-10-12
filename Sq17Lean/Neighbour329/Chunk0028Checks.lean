import Sq17Lean.Neighbour329.Chunk0028Data
import Sq17Lean.Neighbour329.Chunk0027Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0028
def freshBoundsRaw : String := ""

def freshBounds : Array (CaptureTableFast.Bounds × CaptureTableFast.Bounds) := CaptureTableFast.decodeBounds 1000000 (parseInts freshBoundsRaw) 0 #[]
theorem fresh_checked : CaptureTableFast.freshCheck 44 table previousEntryIds.size freshBounds = true := by native_decide
theorem inherited_checked : CaptureTableFast.inheritedCheck Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0027.table table previousEntryIds = true := by native_decide
end Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0028

namespace Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0028
theorem initial_length : S0.length = 17 := by native_decide
theorem final_length : E.length = 17 := by native_decide
theorem boundary_checked : sameGeometry Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0027.table table Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0027.E S0 = true := by native_decide
end Sq17.Propagation.HalfPlaneState.Neighbour329.Chunk0028
