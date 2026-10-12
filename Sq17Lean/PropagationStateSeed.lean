import Sq17Lean.PropagationState

/-! Finite checked initialization from a rational cell polygon and a closed
angle interval. Converting arbitrary square directions into that angle interval
and placing centers in the supplied cells are explicit, separate obligations. -/
namespace Sq17.Propagation

/-- Ordered closed intervals may overlap. Each next interval must start no
later than the current covered endpoint; at least one row must cover the end. -/
def angleRowsCoverCheck (lo hi : ℚ) : List PolygonRow → Bool
  | [] => false
  | r :: rows => decide (r.lo ≤ lo) &&
      (decide (hi ≤ r.hi) || angleRowsCoverCheck r.hi hi rows)

theorem angleRowsCoverCheck_sound (lo hi : ℚ) (rows : List PolygonRow)
    (hc : angleRowsCoverCheck lo hi rows = true) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (lo : ℝ) (hi : ℝ)) :
    ∃ r ∈ rows, θ ∈ Set.Icc (r.lo : ℝ) (r.hi : ℝ) := by
  induction rows generalizing lo with
  | nil => simp [angleRowsCoverCheck] at hc
  | cons r rows ih =>
    have hh := Bool.and_eq_true_iff.mp hc
    have hlo : (r.lo : ℝ) ≤ lo := by exact_mod_cast of_decide_eq_true hh.1
    by_cases hright : θ ≤ (r.hi : ℝ)
    · exact ⟨r, List.mem_cons_self, hlo.trans hθ.1, hright⟩
    · have hrest : angleRowsCoverCheck r.hi hi rows = true := by
        rcases Bool.or_eq_true_iff.mp hh.2 with hstop | hnext
        · have hhi : (hi : ℝ) ≤ r.hi := by exact_mod_cast of_decide_eq_true hstop
          exact (hright (hθ.2.trans hhi)).elim
        · exact hnext
      obtain ⟨s, hs, hsθ⟩ := ih r.hi hrest ⟨(lt_of_not_ge hright).le, hθ.2⟩
      exact ⟨s, List.mem_cons_of_mem r hs, hsθ⟩

def polygonSeedCheck (cell : List (ℚ × ℚ)) (rows : List PolygonRow)
    (lo hi : ℚ) (witness : PolygonRow → (ℚ × ℚ) → HullTriangleWitness) : Bool :=
  angleRowsCoverCheck lo hi rows && rows.all (fun r =>
    cell.all (fun v => triangleHullCheck r.vertices v (witness r v)))

theorem polygonSeedCheck_sound (cell : List (ℚ × ℚ)) (rows : List PolygonRow)
    (lo hi : ℚ) (witness : PolygonRow → (ℚ × ℚ) → HullTriangleWitness)
    (hc : polygonSeedCheck cell rows lo hi witness = true) (p : AnglePose)
    (hcenter : p.center ∈ convexHull ℝ (realPoint '' {v | v ∈ cell}))
    (hangle : p.angle ∈ Set.Icc (lo : ℝ) (hi : ℝ)) :
    p ∈ rowsRegion rows := by
  have hh := Bool.and_eq_true_iff.mp hc
  obtain ⟨r, hr, hθ⟩ := angleRowsCoverCheck_sound lo hi rows hh.1 p.angle hangle
  have hpoly := triangleHullCheck_list_sound cell r.vertices (witness r)
    ((List.all_eq_true.mp hh.2) r hr)
  exact ⟨r, hr, hpoly hcenter, hθ⟩

/-- A generic state is seeded once each owner's finite check passes and its
actual center and angle satisfy the declared cell and angle assumptions. -/
theorem polygonStateSeedCheck_sound {Owner : Type*}
    (cells : Owner → List (ℚ × ℚ)) (S : Owner → List PolygonRow)
    (lo hi : ℚ) (witness : Owner → PolygonRow → (ℚ × ℚ) → HullTriangleWitness)
    (hc : ∀ i, polygonSeedCheck (cells i) (S i) lo hi (witness i) = true)
    (p : Owner → AnglePose)
    (hcenter : ∀ i, (p i).center ∈ convexHull ℝ (realPoint '' {v | v ∈ cells i}))
    (hangle : ∀ i, (p i).angle ∈ Set.Icc (lo : ℝ) (hi : ℝ)) :
    Represents (stateDomains S) p := by
  intro i
  exact polygonSeedCheck_sound (cells i) (S i) lo hi (witness i) (hc i)
    (p i) (hcenter i) (hangle i)

end Sq17.Propagation

#print axioms Sq17.Propagation.angleRowsCoverCheck_sound
#print axioms Sq17.Propagation.polygonSeedCheck_sound
#print axioms Sq17.Propagation.polygonStateSeedCheck_sound
