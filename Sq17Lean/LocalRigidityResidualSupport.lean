import Sq17Lean.LocalRigiditySparseResidual
import Sq17Lean.LocalRigidityMatrixData
import Sq17Lean.LocalRigidityWeightCoverData

namespace Sq17.LocalRigidity.ResidualData
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
def support : LocalMatrixSupport := ![![{0,1,25,26},{2,3,27,28},{0,1,2,3,25,26,27,28},{25,26,40},{4,5,40},{4,5,25,26,40},{6,7,35},{27,28,31,35},{6,7,27,28,31,35},{8,9,34},{10,11,34},{8,9,10,11,34},{12,13,29,30},{12,13,29,30},{14,15,49},{29,30,49},{14,15,29,30,49},{16,17,48},{18,19,48},{16,17,18,19,48},{20,32,33},{31,32,33},{20,31,32,33},{32,33,34,38,39,45},{32,33,34,38,39,45},{32,33,34,38,39,45},{35,36,37},{35,36,37},{36,37,38,39,43,44,51},{36,37,38,39,43,44,51},{36,37,38,39,43,44,51},{40,41,42},{40,41,42},{41,42,43,44,46,49},{41,42,43,44,46,49},{41,42,43,44,46,49},{45,47},{21,22,45,47},{21,22,45,47},{47,48,50,51},{47,48,50,51},{47,48,50,51},{23,24,46,50},{46,50},{23,24,46,50}],![{},{},{},{},{},{},{},{},{},{},{},{},{},{29,30},{},{},{29,30},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}],![{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{35,36,37},{},{},{36,37},{},{},{},{},{},{},{},{},{},{},{},{},{},{}],![{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{40,41,42},{},{},{41,42},{},{},{},{},{},{},{},{},{}]]
theorem support_codes : ∀ k j i, i ∉ support k j → MatrixData.codes k i j = 0 := by decide +kernel

def bounds : LocalIntervalMatrix := MatrixData.coefficientBounds

theorem bounds_sound (k : Fin 4) (i : Fin 52) (j : Fin 45) :
    (bounds k i j).Holds (MatrixData.coefficient k i j) := MatrixData.coefficient_bounded k i j

theorem supported (k : Fin 4) (j : Fin 45) (i : Fin 52) (hi : i ∉ support k j) :
    bounds k i j = ⟨0,0⟩ := by
  change MatrixData.bounds (MatrixData.codes k i j) = ⟨0,0⟩
  rw [support_codes k j i hi]
  rfl
end Sq17.LocalRigidity.ResidualData
#print axioms Sq17.LocalRigidity.ResidualData.supported
