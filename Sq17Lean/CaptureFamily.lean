import Sq17Lean.HalfPlaneAssemblySkeleton
import Sq17Lean.PackingSubfamily
import Sq17Lean.HalfPlaneFrameBounds

/-! Bind the classifier's capture family to the frozen trace owner order.
The family is reflected in y in the cover frame, then translated by -sigma.
The actual target box of side L is retained throughout. -/
namespace Sq17.CaptureFamily
open Propagation CenteredOrbitFrame OrbitCellAssignment HalfPlaneAssembly

/-- all_orbits case 1442, in the classifier's cell labels. -/
def sourceRoster : List (Fin 24) :=
  [0,1,2,3,5,6,7,8,10,11,12,13,14,15,18,19,20]

/-- Owners in the capture trace's I-record order. -/
def roster : Fin 17 → Fin 24 :=
  ![13,0,7,4,19,18,2,20,14,6,10,1,15,11,9,12,3]

def sourceCells (i : Fin 17) : Fin 24 := CellSymmetry.perm 2 (roster i)

theorem sourceCells_injective : Function.Injective sourceCells := by decide +kernel

theorem sourceCells_mem (i : Fin 17) : sourceCells i ∈ sourceRoster := by
  have h : ∀ i, sourceCells i ∈ sourceRoster := by decide +kernel
  exact h i

theorem reflected_sourceCells (i : Fin 17) :
    CellSymmetry.perm 2 (sourceCells i) = roster i := by
  have h : ∀ i, CellSymmetry.perm 2 (sourceCells i) = roster i := by decide +kernel
  exact h i

/-- This is the geometric input needed by capture's CELLS seeding. -/
theorem prepare (L sigma : ℝ) (holes : List (Fin 24))
    (P : RepresentativePacking holes L)
    (hroster : sourceRoster.toFinset = holes.toFinsetᶜ) :
    ∃ c u : Fin 17 → ℝ × ℝ,
      (∀ i, c i ∈ shift (-sigma) '' ExactCells.cell (roster i)) ∧
      (∀ i, (u i).1^2 + (u i).2^2 = 1) ∧
      (∀ i, Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2 ⊆ traceBox L sigma) ∧
      (∀ i j, i ≠ j → Disjoint
        (interior (Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2))
        (interior (Sq17.sq (c j).1 (c j).2 (u j).1 (u j).2))) := by
  classical
  obtain ⟨owner, ho, ha⟩ := PackingSubfamily.select holes.toFinsetᶜ
    P.occupied_card P.assigned P.injective P.occupied sourceCells sourceCells_injective
    (fun i => hroster ▸ List.mem_toFinset.mpr (sourceCells_mem i))
  let c := fun i => shift (-sigma) (CellSymmetry.action 2 (P.c (owner i)))
  let u := fun i => CellSymmetry.direction 2 (P.u (owner i))
  refine ⟨c, u, ?_, ?_, ?_, ?_⟩
  · intro i
    apply shift_mem_trace_cell
    have hp := P.centres (owner i)
    have hp' : P.c (owner i) ∈ ExactCells.cell (sourceCells i) := by
      simpa [traceCell,shift,ha i] using hp
    simpa only [reflected_sourceCells] using CellSymmetry.action_mem_cell 2 _ hp'
  · intro i
    exact CellSymmetry.direction_unit 2 _ (P.unit (owner i))
  · intro i
    apply square_fit_trace
    apply action_square_fit_centered
    simpa only [traceBox,centeredBox,sub_zero] using P.fit (owner i)
  · intro i j hij
    apply shift_square_disjoint
    apply CellSymmetry.action_square_disjoint
    exact P.disjoint (owner i) (owner j) (fun h => hij (ho h))

end Sq17.CaptureFamily
#print axioms Sq17.CaptureFamily.prepare
