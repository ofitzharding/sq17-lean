import Sq17Lean.HalfPlanePatternDispatch

/-! From a case theorem stated in the shifted capture-neighbour header frame to
the assembly's dispatch form. The packing is re-indexed by the roster and
translated by `-sigma`. -/
namespace Sq17.HalfPlaneAssembly
open Propagation CenteredOrbitFrame OrbitCellAssignment HalfPlaneFrameBounds

theorem neighbour_dispatch_of_case (roster : Fin 17 → Fin 24)
    (hinj : Function.Injective roster) (side pad sigma : ℚ)
    (hside : side = captureNeighbour.side) (hpad : pad = captureNeighbour.padding)
    (hsigma : sigma = captureNeighbour.sigma)
    (hcase : ∀ c u : Fin 17 → ℝ × ℝ, (∀ i, (u i).1^2+(u i).2^2 = 1) →
      (∀ i, c i ∈ shift (-(sigma:ℝ)) '' ExactCells.cell (roster i)) →
      (∀ i j, i ≠ j → Disjoint
        (interior (Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2))
        (interior (Sq17.sq (c j).1 (c j).2 (u j).1 (u j).2))) →
      (∀ i, Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2 ⊆ traceContainer side pad) → False)
    (L : ℝ) (hL : L < EndpointGeometry.side) (holes : List (Fin 24))
    (P : RepresentativePacking holes L)
    (hroster : (List.ofFn roster).toFinset = holes.toFinsetᶜ) : False := by
  obtain ⟨π, hπinj, hπ⟩ := reindex roster hinj holes L P hroster
  subst hside hpad hsigma
  have hb := capture_neighbour_bounds L hL.le
  have hbox := frame_subset captureNeighbour L hb.1 hb.2
  apply hcase (fun i => shift (-(captureNeighbour.sigma:ℝ)) (P.c (π i))) (fun i => P.u (π i))
    (fun i => P.unit _)
  · intro i
    have h := P.centres (π i)
    rw [hπ i] at h
    unfold traceCell at h
    rw [shift_zero_image] at h
    exact ⟨_, h, rfl⟩
  · intro i j hij
    exact shift_square_disjoint _ _ _ _ _ (P.disjoint _ _ (fun e => hij (hπinj e)))
  · intro i
    have hf := P.fit (π i)
    rw [traceBox_zero] at hf
    exact (square_fit_trace L _ (P.c (π i)) (P.u (π i)) hf).trans hbox

end Sq17.HalfPlaneAssembly

#print axioms Sq17.HalfPlaneAssembly.neighbour_dispatch_of_case
