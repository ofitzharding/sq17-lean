import Sq17Lean.LocalRigidityResidualMetadata
import Sq17Lean.LocalRigidityWeightGlobal
import Sq17Lean.LocalRigidityFiniteMax

namespace Sq17.LocalRigidity
open scoped BigOperators
open WeightCoverData

/-- Each point of a certificate box inherits both its accepted residual and
its accepted nonnegative dual weights. -/
theorem box_signed_dual (i : Fin 93)
    (haccepted : sparseResidualCheck ResidualData.bounds ResidualData.support
      (WeightData.boxes i) (ResidualData.mid i) (ResidualData.target i) = true)
    (w : Fin 3 → ℝ) (hw : cellHolds i w) :
    (∀ row, 0 ≤ weights i w row) ∧
    (∑ row, weights i w row * 100) ≤ 1200000 ∧
    (∑ j, |(∑ row, weights i w row * matrixFamily MatrixData.coefficient w row j) +
      (ResidualData.target i j : ℝ)|) ≤ 1/4 := by
  let z : Fin 3 → ℝ := fun k => w k - (ResidualData.mid i k : ℝ)
  have hz : ∀ k, |z k| ≤ ((WeightData.boxes i).half k : ℝ) := by
    simpa only [z, ResidualData.mid_correct] using centered_bounds i w hw
  have hweights : dualWeights (WeightData.boxes i) z = weights i w := by
    funext row
    simp only [dualWeights,weights,z,ResidualData.mid_correct]
  have hwcenter : (fun k => (ResidualData.mid i k : ℝ)+z k) = w := by
    funext k
    dsimp [z]
    ring
  have hr := sparseResidualCheck_weighted ResidualData.bounds MatrixData.coefficient
    ResidualData.support ResidualData.bounds_sound ResidualData.supported (WeightData.boxes i) (ResidualData.mid i)
    (ResidualData.target i) haccepted z hz
  rw [hweights,hwcenter] at hr
  have hs := AffineWeightCertificate.check_sound (WeightData.boxes i)
    (WeightData.accepted i) z hz
  change (∀ row, 0 ≤ dualWeights (WeightData.boxes i) z row) ∧
    (∑ row, dualWeights (WeightData.boxes i) z row *
      ((WeightData.boxes i).curvature row : ℝ)) ≤ ((WeightData.boxes i).mass : ℝ) ∧
    0 ≤ ((WeightData.boxes i).mass : ℝ) at hs
  rw [hweights] at hs
  have hk : ∀ row, (1 : ℝ) ≤ ((WeightData.boxes i).curvature row : ℝ) := by
    intro row
    exact_mod_cast curvature_ge_one i row
  have hm := universal_curvature_mass (weights i w)
    (fun row => ((WeightData.boxes i).curvature row : ℝ)) 100
    ((WeightData.boxes i).mass : ℝ) hs.1 hk (by norm_num) hs.2.1
  have hmass : ((WeightData.boxes i).mass : ℝ) ≤ 12000 := by
    exact_mod_cast mass_bounded i
  exact ⟨hs.1, by linarith, hr⟩

/-- Checked certificates for all signed coordinates force every sufficiently
small feasible displacement to vanish. The geometric row inequalities remain
an explicit premise of this purely linear certificate theorem. -/
theorem matrix_local_rigidity_of_checked
    (haccepted : ∀ i, sparseResidualCheck ResidualData.bounds ResidualData.support
      (WeightData.boxes i) (ResidualData.mid i) (ResidualData.target i) = true)
    (w : Fin 3 → ℝ) (h : Fin 45 → ℝ)
    (hw : ∀ k, (globalLower k : ℝ) ≤ w k ∧ w k ≤ (globalUpper k : ℝ))
    (hlocal : ∀ j, |h j| ≤ (1/10000000 : ℝ))
    (hrows : ∀ row, -50*(maxAbs h)^2 ≤ ∑ j, matrixFamily MatrixData.coefficient w row j*h j) :
    ∀ j, h j = 0 := by
  classical
  apply all_zero_of_signed_duals _ h hlocal hrows
  intro j s hs
  let b : Bool := decide (s = 1)
  have hsval : s = (if b then 1 else -1) := by
    rcases hs with rfl | rfl <;> norm_num [b]
  obtain ⟨i,hi,hcell⟩ := cover (ResidualData.signedIndex j b) w hw
  obtain ⟨hn,hm,hr⟩ := box_signed_dual i (haccepted i) w hcell
  refine ⟨weights i w,hn,hm,?_⟩
  have ht : ∀ k, (ResidualData.target i k : ℝ) = signedCoordinate j s k := by
    intro k
    rw [ResidualData.target_by_owner,hi]
    rcases ResidualData.signedIndex_correct j b with ⟨hc,hsign⟩
    rw [hc,hsign]
    simp only [signedCoordinate]
    split_ifs <;> simp_all
  simpa only [ht] using hr

end Sq17.LocalRigidity
#print axioms Sq17.LocalRigidity.matrix_local_rigidity_of_checked
