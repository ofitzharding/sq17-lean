import Sq17Lean.ExactCellCover
import Mathlib.Data.Finset.Powerset

/-! The eight actual symmetries of the square cover, with exact finite
permutations and geometric action on the complete real cell hulls. -/
namespace Sq17.CellSymmetry
open Sq17.Propagation Sq17.ExactCells

/-- Identity, x reflection, y reflection, half turn, diagonal reflection,
quarter turn, inverse quarter turn, other diagonal reflection. -/
def action {K : Type*} [Field K] (g : Fin 8) (p : K × K) : K × K :=
  let U : K := 1169/250
  match g.val with
  | 0 => p
  | 1 => (U-p.1,p.2)
  | 2 => (p.1,U-p.2)
  | 3 => (U-p.1,U-p.2)
  | 4 => (p.2,p.1)
  | 5 => (U-p.2,p.1)
  | 6 => (p.2,U-p.1)
  | _ => (U-p.2,U-p.1)

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

/-- Every source vertex maps to an actual vertex of the designated target cell. -/
theorem vertex_action_checked : ∀ g : Fin 8, ∀ i : Fin 24,
    (vertices i).all (fun p => decide (action g p ∈ vertices (perm g i))) = true := by
  decide +kernel

theorem action_cast (g : Fin 8) (p : ℚ × ℚ) :
    realPoint (action g p) = action g (realPoint p) := by
  fin_cases g <;> ext <;>
    simp [action,realPoint,Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat]

theorem action_inverse (g : Fin 8) (p : ℝ × ℝ) : action (inv g) (action g p) = p := by
  fin_cases g <;> ext <;> simp [inv,action]

/-- Every square symmetry preserves affine combinations whose weights sum to one. -/
theorem action_affine (g : Fin 8) (p q : ℝ × ℝ) (a b : ℝ) (hab : a+b=1) :
    action g (a • p + b • q) = a • action g p + b • action g q := by
  fin_cases g <;> ext <;> simp [action] <;> nlinarith only [hab]

theorem action_comp (g h : Fin 8) (p : ℝ × ℝ) :
    action (comp g h) p = action g (action h p) := by
  fin_cases g <;> fin_cases h <;> ext <;> simp [comp,action]

/-- Vertex checking lifts to the entire real closed hull, not just listed points. -/
theorem action_mem_cell (g : Fin 8) (i : Fin 24) {p : ℝ × ℝ}
    (hp : p ∈ cell i) : action g p ∈ cell (perm g i) := by
  let T := cell (perm g i)
  have ht : Convex ℝ T := convex_convexHull ℝ _
  have hpre : Convex ℝ {x | action g x ∈ T} := by
    intro x hx y hy a b ha hb hab
    change action g (a • x+b • y) ∈ T
    rw [action_affine g x y a b hab]
    exact ht hx hy ha hb hab
  apply convexHull_min (t := {x | action g x ∈ T}) ?_ hpre hp
  rintro _ ⟨q,hq,rfl⟩
  change action g (realPoint q) ∈ T
  rw [← action_cast]
  apply subset_convexHull ℝ _
  refine ⟨action g q,?_,rfl⟩
  exact of_decide_eq_true ((List.all_eq_true.mp (vertex_action_checked g i)) q hq)

/-- Exact equality of the transformed cell and its finite permutation image. -/
theorem action_cell_image (g : Fin 8) (i : Fin 24) :
    action g '' cell i = cell (perm g i) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p,hp,rfl⟩
    exact action_mem_cell g i hp
  · intro q hq
    refine ⟨action (inv g) q,?_,?_⟩
    · simpa only [perm_inverse] using action_mem_cell (inv g) (perm g i) hq
    · simpa only [inverse_inverse] using action_inverse (inv g) q

end Sq17.CellSymmetry

#print axioms Sq17.CellSymmetry.perm_comp
#print axioms Sq17.CellSymmetry.vertex_action_checked
#print axioms Sq17.CellSymmetry.action_cell_image
#print axioms Sq17.CellSymmetry.action_comp
