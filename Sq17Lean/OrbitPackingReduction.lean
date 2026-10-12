import Sq17Lean.OrbitCellAssignment

/-! Strengthen the geometric orbit reduction with exact occupied cardinality.
This permits selection of every requested representative cell, rather than
merely knowing that the assigned cells lie in its complement of holes. The
exhaustive finite cover remains an explicit premise until census assembly. -/
namespace Sq17.OrbitCellAssignment
open Sq17.FiniteOrbitCover Sq17.CenteredOrbitFrame

theorem packing_reaches_trace_table_exact (t : RepTree)
    (hcover : ∀ s : Finset (Fin 24), s.card = 17 → Reaches t s)
    (L sigma : ℝ) (hL : L ≤ 1169/250) (p u : Fin 17 → ℝ × ℝ)
    (hunit : ∀ i, (u i).1^2+(u i).2^2=1)
    (hfit : ∀ i, Sq17.sq (p i).1 (p i).2 (u i).1 (u i).2 ⊆
      Propagation.containerBox L)
    (hdis : ∀ i j, i ≠ j → Disjoint
      (interior (Sq17.sq (p i).1 (p i).2 (u i).1 (u i).2))
      (interior (Sq17.sq (p j).1 (p j).2 (u j).1 (u j).2))) :
    ∃ g : Fin 8, ∃ holes : List (Fin 24), t.Contains holes ∧ (holes.toFinsetᶜ).card = 17 ∧
      ∃ mapped : Fin 17 → Fin 24, Function.Injective mapped ∧
        (∀ i, mapped i ∈ holes.toFinsetᶜ ∧
          traceCentre g L sigma (p i) ∈ traceCell sigma (mapped i)) ∧
        (∀ i, (CellSymmetry.direction g (u i)).1^2 +
          (CellSymmetry.direction g (u i)).2^2 = 1) ∧
        (∀ i, Sq17.sq (traceCentre g L sigma (p i)).1
          (traceCentre g L sigma (p i)).2 (CellSymmetry.direction g (u i)).1
          (CellSymmetry.direction g (u i)).2 ⊆ traceBox L sigma) ∧
        (∀ i j, i ≠ j → Disjoint
          (interior (Sq17.sq (traceCentre g L sigma (p i)).1
            (traceCentre g L sigma (p i)).2 (CellSymmetry.direction g (u i)).1
            (CellSymmetry.direction g (u i)).2))
          (interior (Sq17.sq (traceCentre g L sigma (p j)).1
            (traceCentre g L sigma (p j)).2 (CellSymmetry.direction g (u j)).1
            (CellSymmetry.direction g (u j)).2))) := by
  let q := fun i => shift (delta L) (p i)
  have hcenter : ∀ i, Sq17.sq (q i).1 (q i).2 (u i).1 (u i).2 ⊆ centeredBox L :=
    fun i => square_fit_centered L (p i) (u i) (hfit i)
  have hqfit : ∀ i, Sq17.sq (q i).1 (q i).2 (u i).1 (u i).2 ⊆
      Propagation.containerBox (1169/250) :=
    fun i => (hcenter i).trans (centered_subset_cover L hL)
  have hqdis : ∀ i j, i ≠ j → Disjoint
      (interior (Sq17.sq (q i).1 (q i).2 (u i).1 (u i).2))
      (interior (Sq17.sq (q j).1 (q j).2 (u j).1 (u j).2)) :=
    fun i j hij => shift_square_disjoint (delta L) (p i) (p j) (u i) (u j) (hdis i j hij)
  obtain ⟨occupied, hcard, assign, hinj, ha⟩ :=
    ExactCells.unit_packing_cell_subset (1169/250) le_rfl q u hunit hqfit hqdis
  obtain ⟨g, holes, hh, hmap⟩ := hcover occupied hcard
  let mapped := fun i => CellPermutation.cellEquiv g (assign i)
  have hm : Function.Injective mapped := (CellPermutation.cellEquiv g).injective.comp hinj
  have hhcard : (holes.toFinsetᶜ).card = 17 := by
    rw [← hmap, Finset.card_map]
    exact hcard
  have hplace : ∀ i, mapped i ∈ holes.toFinsetᶜ ∧
      CellSymmetry.action g (q i) ∈ ExactCells.cell (mapped i) := by
    intro i
    constructor
    · rw [← hmap]
      exact Finset.mem_map.mpr ⟨assign i, (ha i).1, rfl⟩
    · exact CellSymmetryBridge.finite_action_mem_cell g (assign i) (ha i).2
  refine ⟨g,holes,hh,hhcard,mapped,hm,?_,?_,?_,?_⟩
  · intro i
    exact ⟨(hplace i).1,shift_mem_trace_cell sigma (mapped i) _ (hplace i).2⟩
  · intro i
    exact CellSymmetry.direction_unit g (u i) (hunit i)
  · intro i
    exact square_fit_trace L sigma (CellSymmetry.action g (q i))
      (CellSymmetry.direction g (u i)) (action_square_fit_centered g L (q i) (u i) (hcenter i))
  · intro i j hij
    exact shift_square_disjoint (-sigma) (CellSymmetry.action g (q i))
      (CellSymmetry.action g (q j)) (CellSymmetry.direction g (u i))
      (CellSymmetry.direction g (u j))
      (CellSymmetry.action_square_disjoint g (q i) (q j) (u i) (u j) (hqdis i j hij))

end Sq17.OrbitCellAssignment
#print axioms Sq17.OrbitCellAssignment.packing_reaches_trace_table_exact
