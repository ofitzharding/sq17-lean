import Mathlib.Tactic.Linarith
import Sq17Lean.PropagationRational

/-! Exact coverage for clipping a segment by a closed half-plane. This is a
primitive for polygon clipping, not yet a proof of the full polygon algorithm.
The boundary point is retained, including a cut at either endpoint. -/
namespace Sq17.Propagation

theorem segment_clip_coverage (f : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (u v : ℝ × ℝ) (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) (hdir : f u < f v) :
    segment ℝ u v ∩ {x | f x ≤ f u + r*(f v-f u)} =
      segment ℝ u (u + r • (v-u)) := by
  have hd : 0 < f v-f u := sub_pos.mpr hdir
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hf⟩
    rw [segment_eq_image'] at hx ⊢
    rcases hx with ⟨t, ⟨ht0, ht1⟩, rfl⟩
    change f (u+t • (v-u)) ≤ f u+r*(f v-f u) at hf
    simp only [map_add, map_smul, map_sub, smul_eq_mul] at hf
    have ht : t ≤ r := by
      by_contra ht
      have hm := mul_lt_mul_of_pos_right (lt_of_not_ge ht) hd
      linarith
    by_cases hz : r = 0
    · subst r
      have htzero : t = 0 := by linarith
      subst t
      exact ⟨0, ⟨le_refl 0, zero_le_one⟩, by simp⟩
    · have hp : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hz)
      refine ⟨t/r, ⟨div_nonneg ht0 hr.1, (div_le_one hp).mpr ht⟩, ?_⟩
      simp only [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hz]
  · intro x hx
    rw [segment_eq_image'] at hx
    rcases hx with ⟨t, ⟨ht0, ht1⟩, rfl⟩
    simp only [add_sub_cancel_left, smul_smul]
    have htr0 : 0 ≤ t*r := mul_nonneg ht0 hr.1
    have htr : t*r ≤ r := by nlinarith [mul_le_mul_of_nonneg_right ht1 hr.1]
    constructor
    · rw [segment_eq_image']
      exact ⟨t*r, ⟨htr0, htr.trans hr.2⟩, rfl⟩
    · change f (u+(t*r) • (v-u)) ≤ f u+r*(f v-f u)
      simp only [map_add, map_smul, map_sub, smul_eq_mul]
      exact add_le_add (le_refl (f u)) (mul_le_mul_of_nonneg_right htr hd.le)

/-- The exact division formula used to form an edge intersection supplies
the required cut parameter, even when the retained side is just an endpoint. -/
theorem segment_clip_at (f : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (u v : ℝ × ℝ) (q : ℝ) (hu : f u ≤ q) (hv : q < f v) :
    segment ℝ u v ∩ {x | f x ≤ q} =
      segment ℝ u (u + ((q-f u)/(f v-f u)) • (v-u)) := by
  have hd : 0 < f v-f u := by linarith
  have hr : 0 ≤ (q-f u)/(f v-f u) ∧ (q-f u)/(f v-f u) ≤ 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hu) hd.le, (div_le_one hd).mpr (by linarith)⟩
  have heq : f u + (q-f u)/(f v-f u)*(f v-f u) = q := by
    rw [div_mul_cancel₀ _ (ne_of_gt hd)]
    ring
  simpa only [heq] using segment_clip_coverage f u v _ hr (by linarith)

end Sq17.Propagation

#print axioms Sq17.Propagation.segment_clip_coverage
#print axioms Sq17.Propagation.segment_clip_at
