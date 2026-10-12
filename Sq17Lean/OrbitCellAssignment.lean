import Sq17Lean.FiniteOrbitCoverCheck
import Sq17Lean.CellSymmetryBridge
import Sq17Lean.PackingCellReduction
import Sq17Lean.WallSquareSymmetry
import Sq17Lean.CenteredOrbitFrame

/-! The interface from finite orbit coverage to actual closed-cell placement.
The exhaustive-census premise is explicit. All 24 cell capacities and full
square symmetry transport come from proved imports. The final theorem preserves the exact smaller target side by centering first
and then subtracting the trace header shift. -/
namespace Sq17.OrbitCellAssignment
open Sq17.FiniteOrbitCover

/-- One symmetry simultaneously places every assigned centre in the actual
cells of a single table representative, preserving distinct cell assignments. -/
theorem realize_assignment {I : Type*} (t : RepTree) (occupied : Finset (Fin 24))
    (hreach : Reaches t occupied) (p : I → ℝ × ℝ) (assign : I → Fin 24)
    (hinj : Function.Injective assign)
    (ha : ∀ i, assign i ∈ occupied ∧ p i ∈ ExactCells.cell (assign i)) :
    ∃ g : Fin 8, ∃ holes : List (Fin 24), t.Contains holes ∧
      ∃ mapped : I → Fin 24, Function.Injective mapped ∧
        ∀ i, mapped i ∈ holes.toFinsetᶜ ∧
          CellSymmetry.action g (p i) ∈ ExactCells.cell (mapped i) := by
  obtain ⟨g,holes,hh,hmap⟩ := hreach
  let mapped := fun i => CellPermutation.cellEquiv g (assign i)
  refine ⟨g,holes,hh,mapped,(CellPermutation.cellEquiv g).injective.comp hinj,?_⟩
  intro i
  constructor
  · rw [← hmap]
    exact Finset.mem_map.mpr ⟨assign i,(ha i).1,rfl⟩
  · exact CellSymmetryBridge.finite_action_mem_cell g (assign i) (ha i).2

/-- A unit-square packing reaches an actual table member. All cell capacities
are discharged by the geometric reduction; only finite coverage is a premise. -/
theorem packing_centres_reach_table (t : RepTree)
    (hcover : ∀ s : Finset (Fin 24), s.card = 17 → Reaches t s)
    (side : ℝ) (hside : side ≤ 1169/250) (p u : Fin 17 → ℝ × ℝ)
    (hunit : ∀ i, (u i).1^2+(u i).2^2=1)
    (hfit : ∀ i, Sq17.sq (p i).1 (p i).2 (u i).1 (u i).2 ⊆
      Propagation.containerBox side)
    (hdis : ∀ i j, i ≠ j → Disjoint
      (interior (Sq17.sq (p i).1 (p i).2 (u i).1 (u i).2))
      (interior (Sq17.sq (p j).1 (p j).2 (u j).1 (u j).2))) :
    ∃ g : Fin 8, ∃ holes : List (Fin 24), t.Contains holes ∧
      ∃ mapped : Fin 17 → Fin 24, Function.Injective mapped ∧
        ∀ i, mapped i ∈ holes.toFinsetᶜ ∧
          CellSymmetry.action g (p i) ∈ ExactCells.cell (mapped i) := by
  obtain ⟨occupied,hcard,assign,hinj,ha⟩ :=
    ExactCells.unit_packing_cell_subset side hside p u hunit hfit hdis
  exact realize_assignment t occupied (hcover occupied hcard) p assign hinj ha

/-- The same representative has a complete transformed packing in the cover
frame, with unit directions, pairwise disjoint interiors and exact cell centres. -/
theorem packing_reaches_table (t : RepTree)
    (hcover : ∀ s : Finset (Fin 24), s.card = 17 → Reaches t s)
    (p u : Fin 17 → ℝ × ℝ) (hunit : ∀ i, (u i).1^2+(u i).2^2=1)
    (hfit : ∀ i, Sq17.sq (p i).1 (p i).2 (u i).1 (u i).2 ⊆
      Propagation.containerBox (1169/250))
    (hdis : ∀ i j, i ≠ j → Disjoint
      (interior (Sq17.sq (p i).1 (p i).2 (u i).1 (u i).2))
      (interior (Sq17.sq (p j).1 (p j).2 (u j).1 (u j).2))) :
    ∃ g : Fin 8, ∃ holes : List (Fin 24), t.Contains holes ∧
      ∃ mapped : Fin 17 → Fin 24, Function.Injective mapped ∧
        (∀ i, mapped i ∈ holes.toFinsetᶜ ∧
          CellSymmetry.action g (p i) ∈ ExactCells.cell (mapped i)) ∧
        (∀ i, (CellSymmetry.direction g (u i)).1^2 +
          (CellSymmetry.direction g (u i)).2^2 = 1) ∧
        (∀ i, Sq17.sq (CellSymmetry.action g (p i)).1
          (CellSymmetry.action g (p i)).2 (CellSymmetry.direction g (u i)).1
          (CellSymmetry.direction g (u i)).2 ⊆ Propagation.containerBox (1169/250)) ∧
        (∀ i j, i ≠ j → Disjoint
          (interior (Sq17.sq (CellSymmetry.action g (p i)).1
            (CellSymmetry.action g (p i)).2 (CellSymmetry.direction g (u i)).1
            (CellSymmetry.direction g (u i)).2))
          (interior (Sq17.sq (CellSymmetry.action g (p j)).1
            (CellSymmetry.action g (p j)).2 (CellSymmetry.direction g (u j)).1
            (CellSymmetry.direction g (u j)).2))) := by
  obtain ⟨g,holes,hh,mapped,hinj,ha⟩ :=
    packing_centres_reach_table t hcover (1169/250) le_rfl p u hunit hfit hdis
  exact ⟨g,holes,hh,mapped,hinj,ha,
    fun i => CellSymmetry.direction_unit g (u i) (hunit i),
    fun i => CellSymmetry.action_square_fit g (p i) (u i) (hfit i),
    fun i j hij => CellSymmetry.action_square_disjoint g (p i) (p j) (u i) (u j)
      (hdis i j hij)⟩

open Sq17.CenteredOrbitFrame

noncomputable def traceCentre (g : Fin 8) (L sigma : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  shift (-sigma) (CellSymmetry.action g (shift (delta L) p))

def traceCell (sigma : ℝ) (i : Fin 24) : Set (ℝ × ℝ) :=
  shift (-sigma) '' ExactCells.cell i

/-- Exact root interface: a packing of side L reaches one representative with
all squares still inside the centered target L-box minus sigma, and centres
inside that representative's exact cells minus sigma. No enlargement to U is
used in the final containment conclusion. -/
theorem packing_reaches_trace_table (t : RepTree)
    (hcover : ∀ s : Finset (Fin 24), s.card = 17 → Reaches t s)
    (L sigma : ℝ) (hL : L ≤ 1169/250) (p u : Fin 17 → ℝ × ℝ)
    (hunit : ∀ i, (u i).1^2+(u i).2^2=1)
    (hfit : ∀ i, Sq17.sq (p i).1 (p i).2 (u i).1 (u i).2 ⊆
      Propagation.containerBox L)
    (hdis : ∀ i j, i ≠ j → Disjoint
      (interior (Sq17.sq (p i).1 (p i).2 (u i).1 (u i).2))
      (interior (Sq17.sq (p j).1 (p j).2 (u j).1 (u j).2))) :
    ∃ g : Fin 8, ∃ holes : List (Fin 24), t.Contains holes ∧
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
  obtain ⟨g,holes,hh,mapped,hinj,ha⟩ :=
    packing_centres_reach_table t hcover (1169/250) le_rfl q u hunit hqfit hqdis
  refine ⟨g,holes,hh,mapped,hinj,?_,?_,?_,?_⟩
  · intro i
    exact ⟨(ha i).1,shift_mem_trace_cell sigma (mapped i) _ (ha i).2⟩
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

#print axioms Sq17.OrbitCellAssignment.realize_assignment
#print axioms Sq17.OrbitCellAssignment.packing_centres_reach_table

#print axioms Sq17.OrbitCellAssignment.packing_reaches_table

#print axioms Sq17.OrbitCellAssignment.packing_reaches_trace_table
