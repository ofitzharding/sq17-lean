import Sq17Lean.HalfPlaneDispatch
import Sq17Lean.CellSymmetryBridge
import Sq17Lean.WallSquareSymmetry

/-! From a pattern theorem to the assembly's pattern dispatch.

The classifier matches a pattern up to one of the eight square symmetries `g`:
the packing occupies the cells `perm g (roster i)`. The squares in those cells
are selected, carried back by the inverse symmetry, and handed to the pattern
theorem, which speaks about the cells `roster i` themselves. -/
namespace Sq17.HalfPlaneAssembly
open Propagation CenteredOrbitFrame OrbitCellAssignment HalfPlaneFrameBounds

theorem traceBox_zero (L : ℝ) : traceBox L 0 = centeredBox L := by
  ext z
  simp [traceBox, centeredBox]

theorem shift_zero_image (S : Set (ℝ × ℝ)) : shift (-(0:ℝ)) '' S = S := by
  ext z
  simp [shift]

theorem pattern_dispatch_of_case (n : ℕ) (roster : Fin n → Fin 24)
    (hinj : Function.Injective roster) (side pad sigma : ℚ)
    (hside : side = ordinary.side) (hpad : pad = ordinary.padding) (hsigma : sigma = 0)
    (hcase : ∀ c u : Fin n → ℝ × ℝ, (∀ i, (u i).1^2+(u i).2^2 = 1) →
      (∀ i, c i ∈ shift (-(sigma:ℝ)) '' ExactCells.cell (roster i)) →
      (∀ i j, i ≠ j → Disjoint
        (interior (Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2))
        (interior (Sq17.sq (c j).1 (c j).2 (u j).1 (u j).2))) →
      (∀ i, Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2 ⊆ traceContainer side pad) → False)
    (L : ℝ) (hL : L < EndpointGeometry.side) (holes : List (Fin 24))
    (P : RepresentativePacking holes L) (g : Fin 8)
    (hocc : ∀ i, CellPermutation.perm g (roster i) ∈ holes.toFinsetᶜ) : False := by
  have himg : Finset.univ.image P.assigned = holes.toFinsetᶜ := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact P.occupied i
    · rw [Finset.card_image_of_injective _ P.injective, P.occupied_card]
      simp
  have hex : ∀ i, ∃ j, P.assigned j = CellPermutation.perm g (roster i) := by
    intro i
    have hmem := hocc i
    rw [← himg] at hmem
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
    exact ⟨j, hj⟩
  choose π hπ using hex
  have hπinj : Function.Injective π := by
    intro a b hab
    apply hinj
    have h1 : CellPermutation.perm g (roster a) = CellPermutation.perm g (roster b) := by
      rw [← hπ a, ← hπ b, hab]
    have h2 := congrArg (CellPermutation.perm (CellPermutation.inv g)) h1
    rwa [CellPermutation.perm_inverse, CellPermutation.perm_inverse] at h2
  subst hside hpad hsigma
  have hb := ordinary_bounds L hL.le
  have hbox : centeredBox L ⊆ traceContainer ordinary.side ordinary.padding := by
    have h0 := frame_subset ordinary L hb.1 hb.2
    have hz : ((ordinary.sigma : ℚ) : ℝ) = 0 := by norm_num [ordinary]
    rw [hz, traceBox_zero] at h0
    exact h0
  apply hcase (fun i => CellSymmetry.action (CellPermutation.inv g) (P.c (π i)))
    (fun i => CellSymmetry.direction (CellPermutation.inv g) (P.u (π i)))
  · intro i
    exact CellSymmetry.direction_unit _ _ (P.unit _)
  · intro i
    have hc := P.centres (π i)
    rw [hπ i] at hc
    have hc' : P.c (π i) ∈ ExactCells.cell (CellPermutation.perm g (roster i)) := by
      unfold traceCell at hc
      rwa [shift_zero_image] at hc
    have hm := CellSymmetryBridge.finite_action_mem_cell (CellPermutation.inv g) _ hc'
    have he : CellPermutation.cellEquiv (CellPermutation.inv g)
        (CellPermutation.perm g (roster i)) = roster i :=
      CellPermutation.perm_inverse g (roster i)
    rw [he] at hm
    have hz : (((0:ℚ):ℝ)) = 0 := by norm_num
    rw [hz, shift_zero_image]
    exact hm
  · intro i j hij
    exact CellSymmetry.action_square_disjoint _ _ _ _ _
      (P.disjoint _ _ (fun e => hij (hπinj e)))
  · intro i
    have hf := P.fit (π i)
    rw [traceBox_zero] at hf
    exact (action_square_fit_centered (CellPermutation.inv g) L (P.c (π i)) (P.u (π i)) hf).trans hbox

end Sq17.HalfPlaneAssembly

#print axioms Sq17.HalfPlaneAssembly.pattern_dispatch_of_case
