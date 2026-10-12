import Sq17Lean.HalfPlaneInt

/-! The half-plane trace checker's definitions live in `HalfPlaneFast`, which is
compiled to native code. This module keeps the old import name and the one bridge
lemma the proofs need. -/
namespace Sq17.Propagation.HalfPlaneState

theorem halfSpan_eq (span : ℚ) : halfSpan span = max 1 span/2 := by
  unfold halfSpan
  split_ifs with h
  · rw [max_eq_right h]
  · rw [max_eq_left (not_le.mp h).le]

end Sq17.Propagation.HalfPlaneState
