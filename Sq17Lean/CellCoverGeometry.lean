import Sq17Lean.SquareBase
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Closed pointwise coverage lemmas for exact vertical-slab certificates. -/
namespace Sq17.CellCover

/-- Every value between the endpoints of a finite chain lies between some
adjacent pair. No strictness or monotonicity is required at chain junctions. -/
theorem interval_chain_cover (n : ℕ) (hn : 0 < n) (f : ℕ → ℝ) (y : ℝ)
    (hlo : f 0 ≤ y) (hhi : y ≤ f n) :
    ∃ k : ℕ, k < n ∧ f k ≤ y ∧ y ≤ f (k+1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hz : n = 0
    · subst n
      exact ⟨0,by omega,hlo,hhi⟩
    by_cases hy : y ≤ f n
    · obtain ⟨k,hk,ha,hb⟩ := ih (by omega) hy
      exact ⟨k,by omega,ha,hb⟩
    · exact ⟨n,by omega,(lt_of_not_ge hy).le,hhi⟩

def blend (a b t : ℝ) : ℝ := (1-t)*a+t*b

/-- A closed vertical interval belongs to any convex set containing its ends. -/
theorem vertical_mem {C : Set (ℝ × ℝ)} (hC : Convex ℝ C)
    (x lo hi y : ℝ) (hl : (x,lo) ∈ C) (hh : (x,hi) ∈ C)
    (hy0 : lo ≤ y) (hy1 : y ≤ hi) : (x,y) ∈ C := by
  by_cases he : lo = hi
  · have : y = lo := by linarith
    simpa [this] using hl
  have hd : 0 < hi-lo := sub_pos.mpr (lt_of_le_of_ne (hy0.trans hy1) he)
  let t := (y-lo)/(hi-lo)
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).mpr (by linarith)
  have h := hC hl hh (sub_nonneg.mpr ht1) ht0 (by ring : (1-t)+t=1)
  have hid : (1-t) • (x,lo) + t • (x,hi) = (x,y) := by
    apply Prod.ext
    · dsimp
      ring
    · dsimp [t]
      field_simp
      nlinarith
  rw [hid] at h
  exact h

/-- The four closed corners of a trapezoid suffice to cover every point
between its linearly interpolated lower and upper edges. -/
theorem trapezoid_mem {C : Set (ℝ × ℝ)} (hC : Convex ℝ C)
    (left right loL loR hiL hiR x y : ℝ)
    (hwidth : left < right) (hx0 : left ≤ x) (hx1 : x ≤ right)
    (hll : (left,loL) ∈ C) (hlr : (right,loR) ∈ C)
    (hhl : (left,hiL) ∈ C) (hhr : (right,hiR) ∈ C)
    (hy0 : blend loL loR ((x-left)/(right-left)) ≤ y)
    (hy1 : y ≤ blend hiL hiR ((x-left)/(right-left))) : (x,y) ∈ C := by
  let t := (x-left)/(right-left)
  have hd : 0 < right-left := sub_pos.mpr hwidth
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx0) hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).mpr (by linarith)
  have point (a b : ℝ) : (1-t) • (left,a) + t • (right,b) =
      (x,blend a b t) := by
    apply Prod.ext
    · dsimp [t]
      field_simp
      nlinarith
    · rfl
  have hl := hC hll hlr (sub_nonneg.mpr ht1) ht0 (by ring : (1-t)+t=1)
  have hh := hC hhl hhr (sub_nonneg.mpr ht1) ht0 (by ring : (1-t)+t=1)
  rw [point] at hl hh
  exact vertical_mem hC x _ _ y hl hh hy0 hy1

end Sq17.CellCover

#print axioms Sq17.CellCover.interval_chain_cover
#print axioms Sq17.CellCover.trapezoid_mem
