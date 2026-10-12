import Sq17Lean.LocalRigidityResidualMetadata
namespace Sq17.LocalRigidity.ResidualData
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
theorem accepted053 : sparseResidualCheck bounds support WeightData.box053 mid053 target053 = true := by decide +kernel
end Sq17.LocalRigidity.ResidualData
#print axioms Sq17.LocalRigidity.ResidualData.accepted053
