import Sq17Lean.HalfPlaneAssemblySkeleton
import Sq17Lean.HalfPlaneFrameBounds

/-! From a per-case statement to the assembly's dispatch form.

A case theorem speaks about seventeen squares indexed by its own roster, in the
header frame. The assembly hands over a packing indexed arbitrarily, whose cells
are the roster's cells as a set, in the trace frame of side `L`. This module
re-indexes the packing by the roster and moves it into the header frame. -/
namespace Sq17.HalfPlaneAssembly
open Propagation CenteredOrbitFrame OrbitCellAssignment HalfPlaneFrameBounds

/-- The packing occupies exactly the roster's cells, so it can be re-indexed by
the roster. -/
theorem reindex (roster : Fin 17 → Fin 24) (hinj : Function.Injective roster)
    (holes : List (Fin 24)) (L : ℝ) (P : RepresentativePacking holes L)
    (hroster : (List.ofFn roster).toFinset = holes.toFinsetᶜ) :
    ∃ π : Fin 17 → Fin 17, Function.Injective π ∧ ∀ i, P.assigned (π i) = roster i := by
  have himg : Finset.univ.image P.assigned = holes.toFinsetᶜ := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact P.occupied i
    · rw [Finset.card_image_of_injective _ P.injective, P.occupied_card]
      simp
  have hex : ∀ i, ∃ j, P.assigned j = roster i := by
    intro i
    have hmem : roster i ∈ holes.toFinsetᶜ := by
      rw [← hroster, List.mem_toFinset, List.mem_ofFn]
      first | exact ⟨i, rfl⟩ | exact Set.mem_range_self i
    rw [← himg] at hmem
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
    exact ⟨j, hj⟩
  choose π hπ using hex
  refine ⟨π, ?_, hπ⟩
  intro a b hab
  apply hinj
  rw [← hπ a, ← hπ b, hab]

/-- An ordinary case theorem, stated in the ordinary header frame, excludes every
representative packing on its roster for every side below the endpoint. -/
theorem ordinary_dispatch_of_case (roster : Fin 17 → Fin 24)
    (hinj : Function.Injective roster) (side pad sigma : ℚ)
    (hside : side = ordinary.side) (hpad : pad = ordinary.padding) (hsigma : sigma = 0)
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
  have hb := ordinary_bounds L hL.le
  have hbox := frame_subset ordinary L hb.1 hb.2
  apply hcase (fun i => P.c (π i)) (fun i => P.u (π i)) (fun i => P.unit _)
  · intro i
    have h := P.centres (π i)
    rw [hπ i] at h
    simpa [traceCell] using h
  · intro i j hij
    exact P.disjoint _ _ (fun h => hij (hπinj h))
  · intro i
    exact (P.fit (π i)).trans (by simpa [ordinary] using hbox)

end Sq17.HalfPlaneAssembly

#print axioms Sq17.HalfPlaneAssembly.ordinary_dispatch_of_case
