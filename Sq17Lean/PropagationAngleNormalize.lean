import Sq17Lean.PropagationStateSeed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Real.Pi.Bounds

/-! Unit-square direction normalization preserves the actual closed square.
The selected angle lies in `[-π/4, π/4]`, hence in the rational outer interval
used by the initial rows of the expanded A trace. -/
namespace Sq17.Propagation

theorem square_neg_direction (cx cy ux uy : ℝ) :
    Sq17.sq cx cy (-ux) (-uy) = Sq17.sq cx cy ux uy := by
  ext p
  have h₁ : (p.1-cx)*(-ux)+(p.2-cy)*(-uy) = -((p.1-cx)*ux+(p.2-cy)*uy) := by ring
  have h₂ : (p.2-cy)*(-ux)-(p.1-cx)*(-uy) = -((p.2-cy)*ux-(p.1-cx)*uy) := by ring
  simp only [Sq17.sq, Set.mem_ofPred_eq, h₁, h₂, abs_neg]

theorem square_quarter_turn (cx cy ux uy : ℝ) :
    Sq17.sq cx cy (-uy) ux = Sq17.sq cx cy ux uy := by
  ext p
  have h₁ : (p.1-cx)*(-uy)+(p.2-cy)*ux = (p.2-cy)*ux-(p.1-cx)*uy := by ring
  have h₂ : (p.2-cy)*(-uy)-(p.1-cx)*ux = -((p.1-cx)*ux+(p.2-cy)*uy) := by ring
  simp only [Sq17.sq, Set.mem_ofPred_eq, h₁, h₂, abs_neg, and_comm]

theorem square_angle_quarter_turn (cx cy θ : ℝ) :
    Sq17.sq cx cy (Real.cos (θ+Real.pi/2)) (Real.sin (θ+Real.pi/2)) =
      Sq17.sq cx cy (Real.cos θ) (Real.sin θ) := by
  simpa only [Real.cos_add_pi_div_two, Real.sin_add_pi_div_two] using
    square_quarter_turn cx cy (Real.cos θ) (Real.sin θ)

theorem square_angle_normalize_half (cx cy θ : ℝ)
    (hθ : θ ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2)) :
    ∃ φ ∈ Set.Icc (-(Real.pi/4)) (Real.pi/4),
      Sq17.sq cx cy (Real.cos φ) (Real.sin φ) =
        Sq17.sq cx cy (Real.cos θ) (Real.sin θ) := by
  by_cases hlo : θ < -(Real.pi/4)
  · exact ⟨θ+Real.pi/2, ⟨by linarith [hθ.1], by linarith⟩,
      square_angle_quarter_turn cx cy θ⟩
  · by_cases hhi : Real.pi/4 < θ
    · refine ⟨θ-Real.pi/2, ⟨by linarith, by linarith [hθ.2]⟩, ?_⟩
      have h := square_angle_quarter_turn cx cy (θ-Real.pi/2)
      rw [sub_add_cancel] at h
      exact h.symm
    · exact ⟨θ, ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩, rfl⟩

theorem square_unit_direction_normalize (cx cy ux uy : ℝ)
    (hunit : ux^2+uy^2 = 1) :
    ∃ θ ∈ Set.Icc (-(Real.pi/4)) (Real.pi/4),
      Sq17.sq cx cy (Real.cos θ) (Real.sin θ) = Sq17.sq cx cy ux uy := by
  have hnonneg (a b : ℝ) (ha : 0 ≤ a) (hu : a^2+b^2 = 1) :
      Sq17.sq cx cy (Real.cos (Real.arcsin b)) (Real.sin (Real.arcsin b)) =
        Sq17.sq cx cy a b := by
    have hb : -1 ≤ b ∧ b ≤ 1 := ⟨by nlinarith [sq_nonneg a], by nlinarith [sq_nonneg a]⟩
    have hs := Real.sin_arcsin hb.1 hb.2
    have hc : Real.cos (Real.arcsin b) = a := by
      have ht := Real.sin_sq_add_cos_sq (Real.arcsin b)
      rw [hs] at ht
      nlinarith [Real.cos_arcsin_nonneg b]
    rw [hc, hs]
  by_cases hx : 0 ≤ ux
  · obtain ⟨θ, hθ, heq⟩ := square_angle_normalize_half cx cy (Real.arcsin uy)
      ⟨Real.neg_pi_div_two_le_arcsin uy, Real.arcsin_le_pi_div_two uy⟩
    exact ⟨θ, hθ, heq.trans (hnonneg ux uy hx hunit)⟩
  · obtain ⟨θ, hθ, heq⟩ := square_angle_normalize_half cx cy (Real.arcsin (-uy))
      ⟨Real.neg_pi_div_two_le_arcsin (-uy), Real.arcsin_le_pi_div_two (-uy)⟩
    refine ⟨θ, hθ, heq.trans ((hnonneg (-ux) (-uy) (by linarith) ?_).trans
      (square_neg_direction cx cy ux uy))⟩
    nlinarith

def initialAngleRadius : ℚ := 884279719004579 / 1125899906842624

theorem pi_div_four_lt_initialAngleRadius : Real.pi/4 < (initialAngleRadius : ℝ) := by
  have hp := Real.pi_lt_d20
  norm_num [initialAngleRadius] at *
  linarith

theorem square_unit_direction_normalize_initial (cx cy ux uy : ℝ)
    (hunit : ux^2+uy^2 = 1) :
    ∃ θ ∈ Set.Icc (-(initialAngleRadius : ℝ)) (initialAngleRadius : ℝ),
      Sq17.sq cx cy (Real.cos θ) (Real.sin θ) = Sq17.sq cx cy ux uy := by
  obtain ⟨θ, hθ, heq⟩ := square_unit_direction_normalize cx cy ux uy hunit
  have hp := pi_div_four_lt_initialAngleRadius
  exact ⟨θ, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩, heq⟩

/-- Every family of actual unit squares with centers in the checked cell hulls
has a represented angle-pose family with the same centers and closed squares.
Consequently containment and interior-disjointness can be transported by equality. -/
theorem polygonSeedCheck_represents_unit_squares {Owner : Type*}
    (cells : Owner → List (ℚ × ℚ)) (S : Owner → List PolygonRow)
    (witness : Owner → PolygonRow → (ℚ × ℚ) → HullTriangleWitness)
    (hc : ∀ i, polygonSeedCheck (cells i) (S i) (-initialAngleRadius)
      initialAngleRadius (witness i) = true)
    (c u : Owner → ℝ × ℝ) (hunit : ∀ i, (u i).1^2+(u i).2^2 = 1)
    (hcenter : ∀ i, c i ∈ convexHull ℝ (realPoint '' {v | v ∈ cells i})) :
    ∃ p : Owner → AnglePose, Represents (stateDomains S) p ∧
      (∀ i, (p i).center = c i) ∧
      ∀ i, (p i).square = Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2 := by
  choose θ hθ heq using fun i =>
    square_unit_direction_normalize_initial (c i).1 (c i).2 (u i).1 (u i).2 (hunit i)
  refine ⟨fun i => ⟨c i, θ i⟩, ?_, fun _ => rfl, heq⟩
  apply polygonStateSeedCheck_sound cells S (-initialAngleRadius) initialAngleRadius
    witness hc (fun i => ⟨c i, θ i⟩) hcenter
  intro i
  simpa only [Rat.cast_neg] using hθ i

end Sq17.Propagation

#print axioms Sq17.Propagation.square_quarter_turn
#print axioms Sq17.Propagation.square_unit_direction_normalize
#print axioms Sq17.Propagation.pi_div_four_lt_initialAngleRadius
#print axioms Sq17.Propagation.square_unit_direction_normalize_initial
#print axioms Sq17.Propagation.polygonSeedCheck_represents_unit_squares
