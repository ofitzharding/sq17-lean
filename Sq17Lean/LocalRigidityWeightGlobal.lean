import Sq17Lean.LocalRigidityWeightCover
import Sq17Lean.LocalRigidityUniversalMass

namespace Sq17.LocalRigidity.WeightCoverData
open scoped BigOperators

noncomputable def weights (i : Fin 93) (w : Fin 3 → ℝ) (row : Fin 52) : ℝ :=
  ((WeightData.boxes i).base row : ℝ) + ∑ k,
    (w k - (((lower i k + upper i k)/2 : ℚ) : ℝ)) *
      ((WeightData.boxes i).slope k row : ℝ)

/-- Every signed coordinate direction has an actual inherited affine dual
with nonnegative weights and universal-curvature mass at most 1,200,000.
Only slider-box membership is assumed; matrix residuals remain separate. -/
theorem exists_nonnegative_mass (j : Fin 90) (w : Fin 3 → ℝ)
    (hw : ∀ k, (globalLower k : ℝ) ≤ w k ∧ w k ≤ (globalUpper k : ℝ)) :
    ∃ i : Fin 93, owner i = j ∧ (∀ row, 0 ≤ weights i w row) ∧
      (∑ row, weights i w row * 100) ≤ 1200000 := by
  obtain ⟨i,hi,hcell⟩ := cover j w hw
  have hs := AffineWeightCertificate.check_sound (WeightData.boxes i)
    (WeightData.accepted i)
    (fun k => w k - (((lower i k + upper i k)/2 : ℚ) : ℝ))
    (centered_bounds i w hcell)
  change (∀ row, 0 ≤ weights i w row) ∧
    (∑ row, weights i w row * ((WeightData.boxes i).curvature row : ℝ)) ≤
      ((WeightData.boxes i).mass : ℝ) ∧ 0 ≤ ((WeightData.boxes i).mass : ℝ) at hs
  have hk : ∀ row, (1 : ℝ) ≤ ((WeightData.boxes i).curvature row : ℝ) := by
    intro row
    exact_mod_cast curvature_ge_one i row
  have hm := universal_curvature_mass (weights i w)
    (fun row => ((WeightData.boxes i).curvature row : ℝ)) 100
    ((WeightData.boxes i).mass : ℝ) hs.1 hk (by norm_num) hs.2.1
  have hbound : ((WeightData.boxes i).mass : ℝ) ≤ 12000 := by
    exact_mod_cast mass_bounded i
  exact ⟨i,hi,hs.1,by linarith⟩

end Sq17.LocalRigidity.WeightCoverData
#print axioms Sq17.LocalRigidity.WeightCoverData.exists_nonnegative_mass
