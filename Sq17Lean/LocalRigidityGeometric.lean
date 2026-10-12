import Sq17Lean.LocalRigidityResidualGlobal
import Sq17Lean.LocalRigidityMatrixRows
import Sq17Lean.LocalGeometricRowsLower

namespace Sq17.LocalRigidity
open scoped BigOperators

/-- Acceptance of all 93 residual boxes proves rigidity of the actual geometric
linear rows. The numeric checks are instantiated in `LocalRigidityCertified`. -/
theorem geometric_local_rigidity_of_checked
    (haccepted : ∀ i, sparseResidualCheck ResidualData.bounds ResidualData.support
      (WeightData.boxes i) (ResidualData.mid i) (ResidualData.target i) = true)
    {a b z : ℝ}
    (hb : Sq17.LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ)
    (hlocal : ∀ j, |h j| ≤ (1/10000000 : ℝ))
    (hrows : ∀ row, -50*(maxAbs h)^2 ≤ Sq17.LocalPerturbation.geometricRows a b z h row) :
    ∀ j, h j = 0 := by
  apply matrix_local_rigidity_of_checked haccepted ![a,b,z] h
  · intro k
    fin_cases k <;> norm_num [WeightCoverData.globalLower,WeightCoverData.globalUpper]
    · exact ⟨hb.1,hb.2.1⟩
    · exact ⟨hb.2.2.1,hb.2.2.2.1⟩
    · exact ⟨hb.2.2.2.2.1,hb.2.2.2.2.2⟩
  · exact hlocal
  · intro row
    rw [MatrixRows.matrix_geometric hb]
    exact hrows row

end Sq17.LocalRigidity
#print axioms Sq17.LocalRigidity.geometric_local_rigidity_of_checked
