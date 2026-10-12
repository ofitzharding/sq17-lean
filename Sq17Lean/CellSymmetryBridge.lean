import Sq17Lean.CellPermutation
import Sq17Lean.CellSymmetry

/-! Kernel linkage between the small finite checker dependency and the actual
D4 geometry. Census chunks need not import real analysis or the cell cover. -/
namespace Sq17.CellSymmetryBridge

theorem perm_eq (g : Fin 8) (i : Fin 24) :
    CellPermutation.perm g i = CellSymmetry.perm g i := by rfl

/-- The finite action used by orbit certificates is the actual action on each
whole closed real cell, including its boundary. -/
theorem finite_action_cell_image (g : Fin 8) (i : Fin 24) :
    CellSymmetry.action g '' ExactCells.cell i =
      ExactCells.cell (CellPermutation.cellEquiv g i) := by
  change CellSymmetry.action g '' ExactCells.cell i =
    ExactCells.cell (CellPermutation.perm g i)
  rw [perm_eq]
  exact CellSymmetry.action_cell_image g i

theorem finite_action_mem_cell (g : Fin 8) (i : Fin 24) {p : ℝ × ℝ}
    (hp : p ∈ ExactCells.cell i) :
    CellSymmetry.action g p ∈ ExactCells.cell (CellPermutation.cellEquiv g i) := by
  rw [← finite_action_cell_image]
  exact ⟨p,hp,rfl⟩

end Sq17.CellSymmetryBridge

#print axioms Sq17.CellSymmetryBridge.perm_eq
#print axioms Sq17.CellSymmetryBridge.finite_action_cell_image
