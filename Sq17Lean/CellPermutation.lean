import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin

/-! Finite permutation data for the actual D4 cell action.
Geometric linkage is proved separately by CellSymmetryBridge. -/
namespace Sq17.CellPermutation

def perm : Fin 8 → Fin 24 → Fin 24 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  ![1, 0, 3, 2, 12, 13, 7, 6, 8, 9, 11, 10, 4, 5, 15, 14, 22, 23, 21, 19, 20, 18, 16, 17],
  ![2, 3, 0, 1, 5, 4, 14, 15, 9, 8, 10, 11, 13, 12, 6, 7, 17, 16, 18, 20, 19, 21, 23, 22],
  ![3, 2, 1, 0, 13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 23, 22, 21, 20, 19, 18, 17, 16],
  ![0, 2, 1, 3, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 16, 22, 19, 18, 21, 20, 17, 23],
  ![1, 3, 0, 2, 7, 6, 12, 13, 11, 10, 8, 9, 15, 14, 4, 5, 22, 16, 19, 21, 18, 20, 23, 17],
  ![2, 0, 3, 1, 14, 15, 5, 4, 10, 11, 9, 8, 6, 7, 13, 12, 17, 23, 20, 18, 21, 19, 16, 22],
  ![3, 1, 2, 0, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 23, 17, 20, 21, 18, 19, 22, 16]]

def comp : Fin 8 → Fin 8 → Fin 8 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![1, 0, 3, 2, 5, 4, 7, 6],
  ![2, 3, 0, 1, 6, 7, 4, 5],
  ![3, 2, 1, 0, 7, 6, 5, 4],
  ![4, 6, 5, 7, 0, 2, 1, 3],
  ![5, 7, 4, 6, 1, 3, 0, 2],
  ![6, 4, 7, 5, 2, 0, 3, 1],
  ![7, 5, 6, 4, 3, 1, 2, 0]]

def inv : Fin 8 → Fin 8 := ![0,1,2,3,4,6,5,7]

theorem perm_identity : ∀ i : Fin 24, perm 0 i = i := by decide +kernel
theorem perm_inverse : ∀ g : Fin 8, ∀ i : Fin 24, perm (inv g) (perm g i) = i := by
  decide +kernel
theorem inverse_inverse : ∀ g : Fin 8, inv (inv g) = g := by decide +kernel
theorem perm_comp : ∀ g h : Fin 8, ∀ i : Fin 24, perm (comp g h) i = perm g (perm h i) := by
  decide +kernel
theorem comp_assoc : ∀ g h k : Fin 8, comp (comp g h) k = comp g (comp h k) := by
  decide +kernel
theorem comp_identity : ∀ g : Fin 8, comp 0 g = g ∧ comp g 0 = g := by decide +kernel
theorem comp_inverse : ∀ g : Fin 8, comp (inv g) g = 0 ∧ comp g (inv g) = 0 := by
  decide +kernel

def cellEquiv (g : Fin 8) : Fin 24 ≃ Fin 24 where
  toFun := perm g
  invFun := perm (inv g)
  left_inv := perm_inverse g
  right_inv i := by simpa only [inverse_inverse] using perm_inverse (inv g) i


end Sq17.CellPermutation
