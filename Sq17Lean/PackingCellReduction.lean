import Sq17Lean.ExactWallCapacity
import Sq17Lean.PropagationAngleNormalize

/-! Unconditional reduction of actual unit-square packings to seventeen distinct
cells. All 24 capacity obligations and the pointwise cover are proved imports. -/
namespace Sq17.ExactCells
open Sq17.Propagation

theorem unit_packing_cell_subset (side : ℝ) (hside : side ≤ 1169/250)
    (p u : Fin 17 → ℝ × ℝ) (hunit : ∀ i, (u i).1^2+(u i).2^2=1)
    (hfit : ∀ i, Sq17.sq (p i).1 (p i).2 (u i).1 (u i).2 ⊆ containerBox side)
    (hdis : ∀ i j, i ≠ j → Disjoint
      (interior (Sq17.sq (p i).1 (p i).2 (u i).1 (u i).2))
      (interior (Sq17.sq (p j).1 (p j).2 (u j).1 (u j).2))) :
    ∃ occupied : Finset (Fin 24), occupied.card = 17 ∧
      ∃ assign : Fin 17 → Fin 24, Function.Injective assign ∧
        ∀ i, assign i ∈ occupied ∧ p i ∈ cell (assign i) := by
  choose θ hθ heq using fun i => square_unit_direction_normalize
    (p i).1 (p i).2 (u i).1 (u i).2 (hunit i)
  apply exists_seventeen_cell_subset wall_capacity p θ
  · intro i z hz
    rw [heq i] at hz
    have hh := hfit i hz
    exact ⟨hh.1,hh.2.1.trans hside,hh.2.2.1,hh.2.2.2.trans hside⟩
  · intro i j hij
    rw [heq i,heq j]
    exact hdis i j hij

/-- Set-valued formulation using the project's original IsUnitSquare predicate.
The returned centers and directions describe exactly the supplied square sets. -/
theorem square_packing_cell_subset (side : ℝ) (hside : side ≤ 1169/250)
    (Q : Fin 17 → Set (ℝ × ℝ)) (hunit : ∀ i, Sq17.IsUnitSquare (Q i))
    (hfit : ∀ i, Q i ⊆ containerBox side)
    (hdis : ∀ i j, i ≠ j → Disjoint (interior (Q i)) (interior (Q j))) :
    ∃ p u : Fin 17 → ℝ × ℝ,
      (∀ i, (u i).1^2+(u i).2^2=1 ∧ Q i = Sq17.sq (p i).1 (p i).2 (u i).1 (u i).2) ∧
      ∃ occupied : Finset (Fin 24), occupied.card = 17 ∧
        ∃ assign : Fin 17 → Fin 24, Function.Injective assign ∧
          ∀ i, assign i ∈ occupied ∧ p i ∈ cell (assign i) := by
  choose cx cy ux uy hn he using hunit
  let p : Fin 17 → ℝ × ℝ := fun i => (cx i,cy i)
  let u : Fin 17 → ℝ × ℝ := fun i => (ux i,uy i)
  refine ⟨p,u,fun i => ⟨hn i,he i⟩,?_⟩
  apply unit_packing_cell_subset side hside p u hn
  · intro i
    dsimp [p,u]
    rw [←he i]
    exact hfit i
  · intro i j hij
    dsimp [p,u]
    rw [←he i,←he j]
    exact hdis i j hij

end Sq17.ExactCells
#print axioms Sq17.ExactCells.unit_packing_cell_subset
#print axioms Sq17.ExactCells.square_packing_cell_subset
