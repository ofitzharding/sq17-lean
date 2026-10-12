import Sq17Lean.LocalRigidityResidualMetadata
namespace Sq17.LocalRigidity.ResidualData
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
theorem accepted010 : sparseResidualCheck bounds support WeightData.box010 mid010 target010 = true := by decide +kernel
end Sq17.LocalRigidity.ResidualData
#print axioms Sq17.LocalRigidity.ResidualData.accepted010
