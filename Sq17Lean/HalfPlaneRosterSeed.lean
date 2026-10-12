import Sq17Lean.HalfPlaneCells

/-! Positive cell seeding for OPEN runs and branch roots. This adapter preserves
the actual closed squares, so every original fit and disjointness fact transfers.
It is not a LOAD/checkpoint seeding theorem. -/
namespace Sq17.Propagation.HalfPlaneState

theorem roster_represented (T : Array Entry) (sigma : ℚ) (n : ℕ)
    (roster : Fin n → Fin 24) (S : HState)
    (hseed : stateSeedOK T (-initialAngleRadius) initialAngleRadius
      (rosterCells sigma (List.ofFn roster)) S = true)
    (hlen : S.length = n) (c u : Fin n → ℝ × ℝ)
    (hunit : ∀ i, (u i).1^2 + (u i).2^2 = 1)
    (hcenter : ∀ i, c i ∈ CenteredOrbitFrame.shift (-(sigma:ℝ)) ''
      ExactCells.cell (roster i)) :
    ∃ p : ℕ → AnglePose, Rep T S p ∧ ∀ i : Fin n,
      (p i.val).square = Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2 := by
  let c' : ℕ → ℝ × ℝ := fun k => if h : k < n then c ⟨k, h⟩ else (0, 0)
  let u' : ℕ → ℝ × ℝ := fun k => if h : k < n then u ⟨k, h⟩ else (1, 0)
  have hc' (k : ℕ) (h : k < n) : c' k = c ⟨k, h⟩ := by simp [c', h]
  have hu' (k : ℕ) (h : k < n) : u' k = u ⟨k, h⟩ := by simp [u', h]
  have hunit' : ∀ i, i < S.length → (u' i).1^2 + (u' i).2^2 = 1 := by
    intro i hi
    have hin : i < n := by simpa only [hlen] using hi
    rw [hu' i hin]
    exact hunit _
  have hcenter' : ∀ i, i < S.length → c' i ∈ convexHull ℝ
      (realPoint '' {v | v ∈ (rosterCells sigma (List.ofFn roster)).getD i []}) := by
    intro i hi
    have hin : i < n := by simpa only [hlen] using hi
    rw [hc' i hin]
    have hcell : (rosterCells sigma (List.ofFn roster)).getD i [] =
        shiftedCell sigma (roster ⟨i, hin⟩) := by
      simp [rosterCells, List.getD_eq_getElem?_getD, hin]
    rw [hcell]
    exact shift_cell_subset sigma _ (hcenter _)
  obtain ⟨p, hr, hs⟩ := seed_unit_squares T (rosterCells sigma (List.ofFn roster)) S
    hseed c' u' hunit' hcenter'
  refine ⟨p, hr, ?_⟩
  intro i
  rw [hs i.val (by simpa only [hlen] using i.isLt), hc' i.val i.isLt, hu' i.val i.isLt]

end Sq17.Propagation.HalfPlaneState

#print axioms Sq17.Propagation.HalfPlaneState.roster_represented
