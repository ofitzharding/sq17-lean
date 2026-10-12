import Sq17Lean.OrbitCensus.Complete
import Sq17Lean.RepresentativeCaseParts.All
import Sq17Lean.HalfPlaneFullRoute
import Sq17Lean.HalfPlanePatterns.Dispatch
import Sq17Lean.HalfPlaneCases.Ordinary
import Sq17Lean.CaptureOpen.Optimality
import Sq17Lean.CaptureClassifierBinding
import Sq17Lean.PackingStatement

/-! Concrete assembly with only the four neighbouring full cases outstanding.
All dispatch uses the classifier's compact indices. This avoids an unnecessary
round trip through source case IDs. The neighbour premise is explicit: this
file does NOT yet prove unconditional optimality. -/
namespace Sq17.HalfPlaneAssembly
open Propagation CenteredOrbitFrame OrbitCellAssignment RepresentativeCases
open RepresentativeCaseData

/-- The remaining cases, in order: 329, 1528, 1531, 1563. -/
def NeighbourCasesExcluded : Prop :=
  ∀ k : ℕ, k ∈ [209, 1158, 1161, 1193] →
    ∀ L : ℝ, L < EndpointGeometry.side → ∀ holes : List (Fin 24),
    RepresentativePacking holes L →
    (fullCases k).toFinset = holes.toFinsetᶜ → False

theorem lower_bound_of_neighbours (neighbours : NeighbourCasesExcluded)
    (L : ℝ) (c u : Fin 17 → ℝ × ℝ)
    (hu : ∀ i, (u i).1^2 + (u i).2^2 = 1)
    (hf : ∀ i, Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2 ⊆ containerBox L)
    (hd : ∀ i j, i ≠ j → Disjoint
      (interior (Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2))
      (interior (Sq17.sq (c j).1 (c j).2 (u j).1 (u j).2))) :
    EndpointGeometry.side ≤ L := by
  by_contra hn
  have hL : L < EndpointGeometry.side := lt_of_not_ge hn
  have hcover : L ≤ 1169/250 := by
    have hb := EndpointIntervals.side_decimal_bounds.2
    linarith
  obtain ⟨g, holes, hholes, hcard, assigned, hinj, hplace, hunit, hfit, hdis⟩ :=
    packing_reaches_trace_table_exact OrbitFiniteData.representatives
      OrbitCensus.exhaustive L 0 hcover c u hu hf hd
  let P : RepresentativePacking holes L :=
    ⟨(fun i => traceCentre g L 0 (c i)), (fun i => CellSymmetry.direction g (u i)),
      assigned, hcard, hinj, (fun i => (hplace i).1), (fun i => (hplace i).2),
      hunit, hfit, hdis⟩
  obtain ⟨a, _, ha⟩ := all_representatives_classified holes hholes
  cases a with
  | pattern index symmetry =>
    exact HalfPlaneState.patterns_dispatch L hL holes P index symmetry ha
  | full k =>
    have hm : (fullCases k).length = 17 ∧ (fullCases k).Nodup ∧
        (fullCases k).toFinset = holes.toFinsetᶜ := ha
    rcases full_route k hm.1 with ho | hn | hc
    · exact HalfPlaneState.ordinary_full_dispatch k ho L hL holes P hm.2.2
    · exact neighbours k hn L hL holes P hm.2.2
    · subst k
      have hr : CaptureFamily.sourceRoster.toFinset = holes.toFinsetᶜ := by
        rw [← CaptureFamily.full_204_roster]
        exact hm.2.2
      exact HalfPlaneState.CaptureOpen.capture_excluded L hL holes P hr

theorem feasible_iff_of_neighbours (neighbours : NeighbourCasesExcluded)
    (L : ℝ) : Feasible L ↔ EndpointGeometry.side ≤ L := by
  constructor
  · rintro ⟨c, u, hu, hf, hd⟩
    exact lower_bound_of_neighbours neighbours L c u hu hf hd
  · intro hL
    refine ⟨EndpointGeometry.centres, EndpointGeometry.directions,
      EndpointGeometry.directions_unit, ?_, EndpointGeometry.squares_disjoint⟩
    intro i z hz
    obtain ⟨hx0, hx1, hy0, hy1⟩ := EndpointGeometry.squares_contained i hz
    exact ⟨hx0, hx1.trans hL, hy0, hy1.trans hL⟩

theorem plainPacking_iff_of_neighbours (neighbours : NeighbourCasesExcluded)
    (L : ℝ) : PlainPacking L ↔ EndpointGeometry.side ≤ L := by
  rw [← feasible_iff_plainPacking, feasible_iff_of_neighbours neighbours]

end Sq17.HalfPlaneAssembly

#print axioms Sq17.HalfPlaneAssembly.plainPacking_iff_of_neighbours
