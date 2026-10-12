import Sq17Lean.LocalRigidityWeightCoverData

namespace Sq17.LocalRigidity.WeightCoverData

def cellHolds (i : Fin 93) (w : Fin 3 → ℝ) : Prop :=
  ∀ k, (lower i k : ℝ) ≤ w k ∧ w k ≤ (upper i k : ℝ)

/-- The actual 93 boxes cover the full slider box for every one of the
90 signed coordinate directions, including subdivision boundaries. -/
theorem cover (j : Fin 90) (w : Fin 3 → ℝ)
    (hw : ∀ k, (globalLower k : ℝ) ≤ w k ∧ w k ≤ (globalUpper k : ℝ)) :
    ∃ i : Fin 93, owner i = j ∧ cellHolds i w := by
  by_cases hj : j = 55
  · subst j
    have ha : (0 : ℝ) ≤ w 0 ∧ w 0 ≤ 1/4 := by
      have h := hw 0
      norm_num [globalLower,globalUpper] at h ⊢
      exact h
    have hb : (-(1/2500) : ℝ) ≤ w 1 ∧ w 1 ≤ 1/12 := by
      have h := hw 1
      norm_num [globalLower,globalUpper] at h ⊢
      exact h
    have hz : (-(1/8) : ℝ) ≤ w 2 ∧ w 2 ≤ 1/16 := by
      have h := hw 2
      norm_num [globalLower,globalUpper] at h ⊢
      exact h
    by_cases h0 : (1/64 : ℝ) ≤ w 2
    · refine ⟨55, rfl, ?_⟩
      intro k
      fin_cases k <;> norm_num [lower,upper,WeightData.lo055,WeightData.hi055]
      · exact ha
      · exact hb
      · exact ⟨h0,hz.2⟩
    · by_cases h1 : (-(1/32) : ℝ) ≤ w 2
      · refine ⟨56, rfl, ?_⟩
        intro k
        fin_cases k <;> norm_num [lower,upper,WeightData.lo056,WeightData.hi056]
        · exact ha
        · exact hb
        · exact ⟨h1,le_of_lt (lt_of_not_ge h0)⟩
      · by_cases h2 : (-(5/64) : ℝ) ≤ w 2
        · refine ⟨57, rfl, ?_⟩
          intro k
          fin_cases k <;> norm_num [lower,upper,WeightData.lo057,WeightData.hi057]
          · exact ha
          · exact hb
          · exact ⟨h2,le_of_lt (lt_of_not_ge h1)⟩
        · refine ⟨58, rfl, ?_⟩
          intro k
          fin_cases k <;> norm_num [lower,upper,WeightData.lo058,WeightData.hi058]
          · exact ha
          · exact hb
          · exact ⟨hz.1,le_of_lt (lt_of_not_ge h2)⟩
  · refine ⟨first j,owner_first j,?_⟩
    intro k
    rcases ordinary_bounds j hj k with ⟨hl,hu⟩
    simpa only [hl,hu] using hw k

/-- Membership in a recorded box gives exactly the centered halfwidth
assumptions required by the already accepted affine-weight checker. -/
theorem centered_bounds (i : Fin 93) (w : Fin 3 → ℝ) (hw : cellHolds i w) :
    ∀ k, |w k - (((lower i k + upper i k)/2 : ℚ) : ℝ)| ≤
      ((WeightData.boxes i).half k : ℝ) := by
  intro k
  rw [halfwidths i k]
  push_cast
  have hk := hw k
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end Sq17.LocalRigidity.WeightCoverData
#print axioms Sq17.LocalRigidity.WeightCoverData.cover
#print axioms Sq17.LocalRigidity.WeightCoverData.centered_bounds
