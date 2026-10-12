import Sq17Lean.LocalRigidityResidualMetadata
namespace Sq17.LocalRigidity.ResidualData
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
theorem accepted064 : sparseResidualCheck bounds support WeightData.box064 mid064 target064 = true := by decide +kernel
end Sq17.LocalRigidity.ResidualData
#print axioms Sq17.LocalRigidity.ResidualData.accepted064
