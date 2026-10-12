import Sq17Lean.LocalRigidityGeometric
import Sq17Lean.LocalRigidityResidualData

namespace Sq17.LocalRigidity
open scoped BigOperators

/-- The complete 93-box certificate proves rigidity of the actual geometric
linear rows, with no unverified numerical acceptance premise. -/
theorem geometric_local_rigidity {a b z : ℝ}
    (hb : Sq17.LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ)
    (hlocal : ∀ j, |h j| ≤ (1/10000000 : ℝ))
    (hrows : ∀ row, -50*(maxAbs h)^2 ≤ Sq17.LocalPerturbation.geometricRows a b z h row) :
    ∀ j, h j = 0 :=
  geometric_local_rigidity_of_checked ResidualData.accepted hb h hlocal hrows

/-- Actual fitted squares with disjoint retained contacts have no non-slider
motion in the certified chart neighborhood. -/
theorem packing_local_rigidity {a b z : ℝ}
    (hb : Sq17.LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ)
    (hlocal : ∀ j, |h j| ≤ (1/10000000 : ℝ))
    (hfit : Sq17.LocalPerturbation.FitsEndpoint a b z h)
    (hd : Sq17.LocalPerturbation.ContactDisjoint a b z h) :
    ∀ j, h j = 0 :=
  geometric_local_rigidity hb h hlocal
    (Sq17.LocalPerturbation.geometricRows_lower h hb hlocal hfit hd)

end Sq17.LocalRigidity
#print axioms Sq17.LocalRigidity.geometric_local_rigidity

#print axioms Sq17.LocalRigidity.packing_local_rigidity
