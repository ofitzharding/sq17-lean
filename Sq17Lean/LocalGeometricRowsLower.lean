import Sq17Lean.LocalGeometricWallRows
import Sq17Lean.LocalGeometricPairRows
import Sq17Lean.LocalPackingSpan
import Sq17Lean.LocalRigidityFiniteMax

/-! All 52 local row inequalities derived from actual packing geometry. -/
namespace Sq17.LocalPerturbation
open Sq17.EndpointGeometry Sq17.LocalRigidity
noncomputable section

def ContactDisjoint (a b z : ℝ) (h : Fin 45 → ℝ) : Prop :=
  ∀ r : Fin 19, Disjoint
    (interior (motionSquare a b z h (LocalSlider.contactPairs r).1))
    (interior (motionSquare a b z h (LocalSlider.contactPairs r).2.1))

theorem geometricRows_lower {a b z : ℝ} (h : Fin 45 → ℝ)
    (hbox : LocalSlider.sliderBox a b z)
    (hh : ∀ k, |h k| ≤ (1:ℝ)/10000000)
    (hfit : FitsEndpoint a b z h) (hd : ContactDisjoint a b z h) :
    ∀ row, -50*(maxAbs h)^2 ≤ geometricRows a b z h row := by
  have hq0 : 0 ≤ maxAbs h := abs_nonneg _
  have hqr : maxAbs h ≤ (1:ℝ)/10000000 := hh (maxCoordinate h)
  have hq : maxAbs h ≤ 1/2 := by linarith
  have hselected : ∀ r : Fin 19, ∃ k : Fin 8, (r,k) ∈ LocalSlider.designatedOptions ∧
      supportGap a b z h (LocalSlider.contactPairs r).1 (LocalSlider.contactPairs r).2.1 k := by
    intro r
    exact disjoint_has_designated hbox h hh r (hd r)
  intro row
  by_cases hr : row.val < 25
  · let r : Fin 25 := ⟨row.val,hr⟩
    have he : r.castLE (by decide : 25 ≤ 52) = row := Fin.ext rfl
    have hw := first25_rows_lower hbox hq0 hq (le_maxAbs h) hfit r
    rw [he] at hw
    linarith
  · let r : Fin 27 := ⟨row.val-25,by omega⟩
    have he : pairRowIndex r = row := by apply Fin.ext; dsimp [pairRowIndex,r]; omega
    have hp := last27_rows_lower hbox hq0 hq (le_maxAbs h) hselected r
    rw [he] at hp
    linarith

#print axioms geometricRows_lower
end
end Sq17.LocalPerturbation
