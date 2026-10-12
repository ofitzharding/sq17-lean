import Sq17Lean.HalfPlaneCells
import Mathlib.Algebra.Field.Periodic

/-! Positive seeding with a separately chosen angle window for each owner.
A unit square can be normalized into any closed interval of width at least π/2,
by quarter-turn periodicity of the square as a set. -/
namespace Sq17.Propagation

theorem square_unit_direction_normalize_window (cx cy ux uy lo hi : ℝ)
    (hunit : ux^2+uy^2 = 1) (hwidth : Real.pi/2 ≤ hi-lo) :
    ∃ θ ∈ Set.Icc lo hi,
      Sq17.sq cx cy (Real.cos θ) (Real.sin θ) = Sq17.sq cx cy ux uy := by
  obtain ⟨θ, _, heq⟩ := square_unit_direction_normalize cx cy ux uy hunit
  have hperiod : Function.Periodic
      (fun φ : ℝ => Sq17.sq cx cy (Real.cos φ) (Real.sin φ)) (Real.pi/2) :=
    square_angle_quarter_turn cx cy
  obtain ⟨φ,hφ,hsq⟩ := hperiod.exists_mem_Ico (by positivity) θ lo
  refine ⟨φ,⟨hφ.1,?_⟩,hsq.symm.trans heq⟩
  linarith [hφ.2]

namespace HalfPlaneState
open Sq17.Propagation.HalfPlaneInt

/-- Each owner has its own normalized interval; rows still cover that interval
and contain every exact cell vertex, with checked cached boxes. -/
def windowSeedOK (T : Array Entry) (windows : ℕ → ℚ × ℚ)
    (cells : List (List (ℚ × ℚ))) (S : HState) : Bool :=
  (List.range S.length).all fun i =>
    seedOK T (windows i).1 (windows i).2 (cells.getD i []) (rowsOf S i)

theorem windowSeedOK_sound (T : Array Entry) (windows : ℕ → ℚ × ℚ)
    (cells : List (List (ℚ × ℚ))) (S : HState)
    (h : windowSeedOK T windows cells S = true) (p : ℕ → AnglePose)
    (hcenter : ∀ i, i < S.length →
      (p i).center ∈ convexHull ℝ (realPoint '' {v | v ∈ cells.getD i []}))
    (hangle : ∀ i, i < S.length →
      (p i).angle ∈ Set.Icc ((windows i).1:ℝ) ((windows i).2:ℝ)) :
    Rep T S p := by
  intro i hlt
  have h1 := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h i (List.mem_range.mpr hlt))
  obtain ⟨r,hr,e,he,hθ⟩ := angleCover_sound T _ (windows i).1 (windows i).2
    h1.1 (p i).angle (hangle i hlt)
  have h2 := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h1.2 r hr)
  have hdom := cellInside_sound _ _ h2.1 (hcenter i hlt)
  have hbox : r.box = mkBox r.cons := of_decide_eq_true h2.2
  exact ⟨r,hr,e,he,hdom,hbox ▸ mkBox_good _ _ hdom,hθ⟩

theorem window_seed_unit_squares (T : Array Entry) (windows : ℕ → ℚ × ℚ)
    (cells : List (List (ℚ × ℚ))) (S : HState)
    (h : windowSeedOK T windows cells S = true)
    (hwidth : ∀ i, i < S.length → Real.pi/2 ≤ ((windows i).2:ℝ)-((windows i).1:ℝ))
    (c u : ℕ → ℝ × ℝ) (hunit : ∀ i, i < S.length → (u i).1^2+(u i).2^2 = 1)
    (hcenter : ∀ i, i < S.length →
      c i ∈ convexHull ℝ (realPoint '' {v | v ∈ cells.getD i []})) :
    ∃ p : ℕ → AnglePose, Rep T S p ∧
      ∀ i, i < S.length → (p i).square = Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2 := by
  have H : ∀ i, ∃ θ : ℝ, i < S.length →
      θ ∈ Set.Icc ((windows i).1:ℝ) ((windows i).2:ℝ) ∧
      Sq17.sq (c i).1 (c i).2 (Real.cos θ) (Real.sin θ) =
        Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2 := by
    intro i
    by_cases hi : i < S.length
    · obtain ⟨θ,hθ,heq⟩ := square_unit_direction_normalize_window
        (c i).1 (c i).2 (u i).1 (u i).2 (windows i).1 (windows i).2
        (hunit i hi) (hwidth i hi)
      exact ⟨θ,fun _ => ⟨hθ,heq⟩⟩
    · exact ⟨0,fun h => (hi h).elim⟩
  choose θ hθ using H
  refine ⟨fun i => ⟨c i,θ i⟩,?_,fun i hi => (hθ i hi).2⟩
  exact windowSeedOK_sound T windows cells S h _ hcenter (fun i hi => (hθ i hi).1)

/-- Named-cell seeding for OPEN capture runs with per-owner angle windows. -/
theorem roster_window_represented (T : Array Entry) (sigma : ℚ) (n : ℕ)
    (roster : Fin n → Fin 24) (S : HState) (windows : ℕ → ℚ × ℚ)
    (hseed : windowSeedOK T windows (rosterCells sigma (List.ofFn roster)) S = true)
    (hwidth : ∀ i : Fin n,
      Real.pi/2 ≤ ((windows i.val).2:ℝ)-((windows i.val).1:ℝ))
    (hlen : S.length = n) (c u : Fin n → ℝ × ℝ)
    (hunit : ∀ i, (u i).1^2+(u i).2^2 = 1)
    (hcenter : ∀ i, c i ∈ CenteredOrbitFrame.shift (-(sigma:ℝ)) ''
      ExactCells.cell (roster i)) :
    ∃ p : ℕ → AnglePose, Rep T S p ∧ ∀ i : Fin n,
      (p i.val).square = Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2 := by
  let c' : ℕ → ℝ × ℝ := fun k => if h : k < n then c ⟨k,h⟩ else (0,0)
  let u' : ℕ → ℝ × ℝ := fun k => if h : k < n then u ⟨k,h⟩ else (1,0)
  have hc' (k : ℕ) (h : k < n) : c' k = c ⟨k,h⟩ := by simp [c',h]
  have hu' (k : ℕ) (h : k < n) : u' k = u ⟨k,h⟩ := by simp [u',h]
  have hunit' : ∀ i, i < S.length → (u' i).1^2+(u' i).2^2 = 1 := by
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
        shiftedCell sigma (roster ⟨i,hin⟩) := by
      simp [rosterCells,List.getD_eq_getElem?_getD,hin]
    rw [hcell]
    exact shift_cell_subset sigma _ (hcenter _)
  have hwidth' : ∀ i, i < S.length →
      Real.pi/2 ≤ ((windows i).2:ℝ)-((windows i).1:ℝ) := by
    intro i hi
    exact hwidth ⟨i,by simpa only [hlen] using hi⟩
  obtain ⟨p,hr,hs⟩ := window_seed_unit_squares T windows
    (rosterCells sigma (List.ofFn roster)) S hseed hwidth' c' u' hunit' hcenter'
  refine ⟨p,hr,?_⟩
  intro i
  rw [hs i.val (by simpa only [hlen] using i.isLt),hc' i.val i.isLt,hu' i.val i.isLt]

end HalfPlaneState
end Sq17.Propagation
#print axioms Sq17.Propagation.square_unit_direction_normalize_window
#print axioms Sq17.Propagation.HalfPlaneState.roster_window_represented
