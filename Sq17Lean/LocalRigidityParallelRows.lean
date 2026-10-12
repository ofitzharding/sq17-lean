import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A parallel face may separate along either owner's normal. Both cases
imply the same two convex-combined linear rows, with the same error bound. -/
namespace Sq17.LocalRigidity

private theorem common_lower_combination (X Y L w : ℝ)
    (hX : L ≤ X) (hY : L ≤ Y) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    L ≤ (1-w)*X+w*Y := by
  have h1 := mul_le_mul_of_nonneg_left hX (sub_nonneg.mpr hw1)
  have h2 := mul_le_mul_of_nonneg_left hY hw
  nlinarith

/-- The exact two parallel-face rows. No choice of separating owner remains
in the conclusion; both possible owners give both rows. -/
theorem parallel_face_rows (T d a b K : ℝ) (hd : |d| ≤ 1)
    (hrows :
      (-K ≤ T+(d+1/2)*a-(1/2)*b ∧ -K ≤ T+(d-1/2)*a+(1/2)*b) ∨
      (-K ≤ T+(1/2)*a+(d-1/2)*b ∧ -K ≤ T-(1/2)*a+(d+1/2)*b)) :
    (-K ≤ T+(d/2+(1-|d|)/2)*a+(d/2-(1-|d|)/2)*b) ∧
    (-K ≤ T+(d/2-(1-|d|)/2)*a+(d/2+(1-|d|)/2)*b) := by
  have hd0 := (abs_le.mp hd).1
  have hd1 := (abs_le.mp hd).2
  by_cases hp : 0 ≤ d
  · rw [abs_of_nonneg hp]
    rcases hrows with ⟨hLp,hLm⟩ | ⟨hRp,hRm⟩
    · have h := common_lower_combination _ _ (-K) d hLp hLm hp hd1
      constructor
      · convert h using 1 <;> ring
      · convert hLm using 1 <;> ring
    · have h := common_lower_combination _ _ (-K) d hRm hRp hp hd1
      constructor
      · convert hRp using 1 <;> ring
      · convert h using 1 <;> ring
  · have hn : d ≤ 0 := le_of_not_ge hp
    rw [abs_of_nonpos hn]
    rcases hrows with ⟨hLp,hLm⟩ | ⟨hRp,hRm⟩
    · have h := common_lower_combination _ _ (-K) (-d) hLm hLp (by linarith) (by linarith)
      constructor
      · convert hLp using 1 <;> ring
      · convert h using 1 <;> ring
    · have h := common_lower_combination _ _ (-K) (-d) hRp hRm (by linarith) (by linarith)
      constructor
      · convert h using 1 <;> ring
      · convert hRm using 1 <;> ring

#print axioms parallel_face_rows
end Sq17.LocalRigidity
