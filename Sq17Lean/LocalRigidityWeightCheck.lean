import Sq17Lean.LocalRigidityBox

namespace Sq17.LocalRigidity
open scoped BigOperators

/-- Rational data certifying affine weights on a centered slider box. -/
structure AffineWeightCertificate (rows params : ℕ) where
  half : Fin params → ℚ
  base : Fin rows → ℚ
  slope : Fin params → Fin rows → ℚ
  curvature : Fin rows → ℚ
  mass : ℚ

def AffineWeightCertificate.check {rows params : ℕ}
    (c : AffineWeightCertificate rows params) : Bool :=
  decide ((∀ k, 0 ≤ c.half k) ∧
    (∀ i, (∑ k, c.half k * |c.slope k i|) ≤ c.base i) ∧
    ((∑ i, c.base i * c.curvature i) +
      ∑ k, c.half k * |∑ i, c.slope k i * c.curvature i|) ≤ c.mass ∧
    0 ≤ c.mass)

theorem AffineWeightCertificate.check_sound {rows params : ℕ}
    (c : AffineWeightCertificate rows params) (hc : c.check = true)
    (z : Fin params → ℝ) (hz : ∀ k, |z k| ≤ (c.half k : ℝ)) :
    (∀ i, 0 ≤ (c.base i : ℝ) + ∑ k, z k * (c.slope k i : ℝ)) ∧
    (∑ i, ((c.base i : ℝ) + ∑ k, z k * (c.slope k i : ℝ)) *
      (c.curvature i : ℝ)) ≤ (c.mass : ℝ) ∧ 0 ≤ (c.mass : ℝ) := by
  unfold check at hc
  obtain ⟨_, hw, hm, hpos⟩ := of_decide_eq_true hc
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply affine_weight_nonnegative z (fun k => (c.half k : ℝ))
      (fun k => (c.slope k i : ℝ)) (c.base i : ℝ) hz
    exact_mod_cast hw i
  · apply affine_curvature_mass z (fun k => (c.half k : ℝ))
      (fun i => (c.base i : ℝ)) (fun i => (c.curvature i : ℝ))
      (fun k i => (c.slope k i : ℝ)) (c.mass : ℝ) hz
    exact_mod_cast hm
  · exact_mod_cast hpos

end Sq17.LocalRigidity
#print axioms Sq17.LocalRigidity.AffineWeightCertificate.check_sound
