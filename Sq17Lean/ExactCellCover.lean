import Sq17Lean.ExactCellCoverData
import Sq17Lean.InteriorCellCapacity
import Sq17Lean.PropagationWallBaseline

/-!
# Exact pointwise cell coverage and finite packing assignments

The 24 cells here are the closed convex hulls of the exact rational vertex lists
in `states/cells.txt`. Pointwise coverage is proved by 22 closed vertical slabs
and 114 closed trapezoids; it is not inferred from an area comparison.

Capacity for the eight interior cells is proved. Injectivity and the 17-element
subset conclusion explicitly assume `WallCapacity` for the other sixteen cells.
Neither this premise nor the 43,593-orbit census is proved in this file.
-/
namespace Sq17.ExactCells
open Sq17.CellCover Sq17.Propagation

def cell (i : Fin 24) : Set (ℝ × ℝ) := polygon vertices i

/-- Every point of the entire closed centre box lies in at least one exact cell. -/
theorem centre_box_covered (x y : ℝ)
    (hx0 : 1/2 ≤ x) (hx1 : x ≤ 522/125)
    (hy0 : 1/2 ≤ y) (hy1 : y ≤ 522/125) :
    ∃ i : Fin 24, (x,y) ∈ cell i := by
  obtain ⟨j,hj,hlo,hhi⟩ := interval_chain_cover 22 (by decide)
    (fun k => (xBreaks k : ℝ)) x
    (by simpa [xBreaks] using hx0) (by simpa [xBreaks] using hx1)
  let i : Fin 22 := ⟨j,hj⟩
  have hc := all_slab_checks i
  apply (slabs i).check_sound vertices (1/2) (522/125) hc.1 x y
  · simpa only [hc.2.1] using hlo
  · simpa only [hc.2.2] using hhi
  · norm_num only [Rat.cast_div, Rat.cast_ofNat] at *
    exact hy0
  · norm_num only [Rat.cast_div, Rat.cast_ofNat] at *
    exact hy1

/-- A fitted square's actual centre can be assigned a cell. The container may
be any size at most the cover-frame side 1169/250. -/
theorem fitted_centre_covered (p : ℝ × ℝ) (θ L : ℝ) (hL : L ≤ 1169/250)
    (hfit : Sq17.sq p.1 p.2 (Real.cos θ) (Real.sin θ) ⊆ containerBox L) :
    ∃ i : Fin 24, p ∈ cell i := by
  have h := square_center_baseline_bounds p.1 p.2 θ L hfit
  exact centre_box_covered p.1 p.2 h.1 (by linarith [h.2.1]) h.2.2.1
    (by linarith [h.2.2.2])

/-- A common shift into the cover frame also receives a cell assignment.
For a centred target use σ=(1169/250-L)/2 with L≤1169/250. -/
theorem shifted_fitted_centre_covered (p : ℝ × ℝ) (θ L σ : ℝ)
    (hσ : 0 ≤ σ) (hLσ : L+σ ≤ 1169/250)
    (hfit : Sq17.sq p.1 p.2 (Real.cos θ) (Real.sin θ) ⊆ containerBox L) :
    ∃ i : Fin 24, (p.1+σ,p.2+σ) ∈ cell i := by
  have h := square_center_baseline_bounds p.1 p.2 θ L hfit
  exact centre_box_covered (p.1+σ) (p.2+σ) (by linarith [h.1])
    (by linarith [h.2.1]) (by linarith [h.2.2.1]) (by linarith [h.2.2.2])

/-- Cell selection uses the proved pointwise cover; boundary points may belong
to several cells, and any such choice is sound. -/
theorem exists_cell_assignment {I : Type*} (p : I → ℝ × ℝ) (θ : I → ℝ)
    (L : ℝ) (hL : L ≤ 1169/250)
    (hfit : ∀ i, Sq17.sq (p i).1 (p i).2 (Real.cos (θ i)) (Real.sin (θ i)) ⊆
      containerBox L) :
    ∃ assign : I → Fin 24, ∀ i, p i ∈ cell (assign i) := by
  classical
  choose assign hassign using (fun i => fitted_centre_covered (p i) (θ i) L hL (hfit i))
  exact ⟨assign,hassign⟩

def interiorIndex (i : Fin 8) : Fin 24 := ⟨16+i.val,by omega⟩
def wallIndex (i : Fin 16) : Fin 24 := ⟨i.val,by omega⟩

/-- The eight interior polygons are exactly those of the capacity theorem,
with the source-file index offset; this is a kernel-checked data identity. -/
theorem interior_vertices_match : ∀ i : Fin 8,
    vertices (interiorIndex i) = Sq17.InteriorCells.vertices i := by decide +kernel

theorem interior_cell_match (i : Fin 8) :
    cell (interiorIndex i) = Sq17.InteriorCells.cell i := by
  unfold cell polygon Sq17.InteriorCells.cell
  rw [interior_vertices_match]
  rfl

/-- The remaining geometric premise: capacity one for each of the sixteen
wall cells, for squares contained in the cover-frame container. -/
def WallCapacity : Prop :=
  ∀ i : Fin 16, ∀ p q : ℝ × ℝ, ∀ θ φ : ℝ,
    Sq17.sq p.1 p.2 (Real.cos θ) (Real.sin θ) ⊆ containerBox (1169/250) →
    Sq17.sq q.1 q.2 (Real.cos φ) (Real.sin φ) ⊆ containerBox (1169/250) →
    p ∈ cell (wallIndex i) → q ∈ cell (wallIndex i) →
    ¬ Disjoint (interior (Sq17.sq p.1 p.2 (Real.cos θ) (Real.sin θ)))
      (interior (Sq17.sq q.1 q.2 (Real.cos φ) (Real.sin φ)))

/-- All-cell capacity uses the eight proved interior cases and only the
explicit remaining wall-capacity premise. -/
theorem cell_capacity_one (hwall : WallCapacity) (i : Fin 24)
    (p q : ℝ × ℝ) (θ φ : ℝ)
    (hpfit : Sq17.sq p.1 p.2 (Real.cos θ) (Real.sin θ) ⊆ containerBox (1169/250))
    (hqfit : Sq17.sq q.1 q.2 (Real.cos φ) (Real.sin φ) ⊆ containerBox (1169/250))
    (hp : p ∈ cell i) (hq : q ∈ cell i) :
    ¬ Disjoint (interior (Sq17.sq p.1 p.2 (Real.cos θ) (Real.sin θ)))
      (interior (Sq17.sq q.1 q.2 (Real.cos φ) (Real.sin φ))) := by
  by_cases hi : i.val < 16
  · exact hwall ⟨i.val,hi⟩ p q θ φ hpfit hqfit hp hq
  · let j : Fin 8 := ⟨i.val-16,by omega⟩
    have he : interiorIndex j = i := by apply Fin.ext; dsimp [interiorIndex,j]; omega
    have hp' : p ∈ Sq17.InteriorCells.cell j := by rwa [← interior_cell_match,he]
    have hq' : q ∈ Sq17.InteriorCells.cell j := by rwa [← interior_cell_match,he]
    exact Sq17.InteriorCells.interior_cell_capacity_one j p q _ _ _ _
      (by nlinarith [Real.sin_sq_add_cos_sq θ])
      (by nlinarith [Real.sin_sq_add_cos_sq φ]) hp' hq'

/-- Distinct squares in a packing receive distinct cells, conditional exactly
on the remaining sixteen wall capacities. -/
theorem exists_injective_cell_assignment {I : Type*} (hwall : WallCapacity)
    (p : I → ℝ × ℝ) (θ : I → ℝ)
    (hfit : ∀ i, Sq17.sq (p i).1 (p i).2 (Real.cos (θ i)) (Real.sin (θ i)) ⊆
      containerBox (1169/250))
    (hdis : ∀ i j, i ≠ j → Disjoint
      (interior (Sq17.sq (p i).1 (p i).2 (Real.cos (θ i)) (Real.sin (θ i))))
      (interior (Sq17.sq (p j).1 (p j).2 (Real.cos (θ j)) (Real.sin (θ j))))) :
    ∃ assign : I → Fin 24, Function.Injective assign ∧ ∀ i, p i ∈ cell (assign i) := by
  obtain ⟨assign,ha⟩ := exists_cell_assignment p θ (1169/250) le_rfl hfit
  refine ⟨assign,?_,ha⟩
  intro i j hij
  by_contra hne
  exact cell_capacity_one hwall (assign i) (p i) (p j) (θ i) (θ j)
    (hfit i) (hfit j) (ha i) (by simpa only [hij] using ha j) (hdis i j hne)

/-- The precise finite object required by the subsequent orbit census:
a 17-element subset of the actual 24 cells, containing every assigned centre. -/
theorem exists_seventeen_cell_subset (hwall : WallCapacity)
    (p : Fin 17 → ℝ × ℝ) (θ : Fin 17 → ℝ)
    (hfit : ∀ i, Sq17.sq (p i).1 (p i).2 (Real.cos (θ i)) (Real.sin (θ i)) ⊆
      containerBox (1169/250))
    (hdis : ∀ i j, i ≠ j → Disjoint
      (interior (Sq17.sq (p i).1 (p i).2 (Real.cos (θ i)) (Real.sin (θ i))))
      (interior (Sq17.sq (p j).1 (p j).2 (Real.cos (θ j)) (Real.sin (θ j))))) :
    ∃ occupied : Finset (Fin 24), occupied.card = 17 ∧
      ∃ assign : Fin 17 → Fin 24, Function.Injective assign ∧
        ∀ i, assign i ∈ occupied ∧ p i ∈ cell (assign i) := by
  classical
  obtain ⟨assign,hinj,ha⟩ := exists_injective_cell_assignment hwall p θ hfit hdis
  refine ⟨Finset.univ.image assign,?_,assign,hinj,?_⟩
  · rw [Finset.card_image_of_injective _ hinj]
    simp
  · intro i
    exact ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩,ha i⟩

end Sq17.ExactCells

#print axioms Sq17.ExactCells.centre_box_covered
#print axioms Sq17.ExactCells.fitted_centre_covered
#print axioms Sq17.ExactCells.exists_cell_assignment
#print axioms Sq17.ExactCells.cell_capacity_one
#print axioms Sq17.ExactCells.exists_seventeen_cell_subset
