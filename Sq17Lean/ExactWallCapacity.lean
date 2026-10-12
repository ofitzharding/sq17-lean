import Sq17Lean.WallSquareSymmetry
import Sq17Lean.WallCapacityRectangle

/-! Capacity one for all sixteen exact wall cells. The finite vertex and
symmetry checks are kernel reductions; all hulls and square interiors are real. -/
namespace Sq17.ExactCells
open Sq17.Propagation Sq17.WallCapacity Sq17.CellSymmetry

def wallCanonical : Fin 3 → Fin 24 := ![0,4,8]
def wallWidth : Fin 3 → ℚ := ![79/100,529/750,257/375]
def wallDepth : Fin 3 → ℚ := ![79/100,911/1000,93/100]
def wallStart : Fin 3 → ℚ := ![1/2,129/100,2993/1500]
def wallClass : Fin 16 → Fin 3 := ![0,0,0,0,1,1,1,1,2,2,2,2,1,1,1,1]
def wallAction : Fin 16 → Fin 8 := ![0,1,2,3,0,2,4,6,0,2,4,6,1,3,5,7]

theorem wall_action_checked : ∀ i : Fin 16,
    perm (wallAction i) (wallIndex i) = wallCanonical (wallClass i) := by decide +kernel

theorem wall_vertex_bounds_checked : ∀ k : Fin 3,
    (vertices (wallCanonical k)).all (fun p => decide
      (wallStart k ≤ p.1 ∧ p.1 ≤ wallStart k+wallWidth k ∧
        p.2 ≤ 1/2+wallDepth k)) = true := by decide +kernel

theorem wall_cell_bounds (k : Fin 3) (p : ℝ × ℝ) (hp : p ∈ cell (wallCanonical k)) :
    (wallStart k : ℝ) ≤ p.1 ∧ p.1 ≤ (wallStart k : ℝ)+(wallWidth k : ℝ) ∧
      p.2 ≤ 1/2+(wallDepth k : ℝ) := by
  have hc : Convex ℝ {p : ℝ × ℝ | (wallStart k : ℝ) ≤ p.1 ∧
      p.1 ≤ (wallStart k : ℝ)+(wallWidth k : ℝ) ∧ p.2 ≤ 1/2+(wallDepth k : ℝ)} := by
    intro x hx y hy a b ha hb hab
    change (wallStart k : ℝ) ≤ a*x.1+b*y.1 ∧
      a*x.1+b*y.1 ≤ (wallStart k : ℝ)+(wallWidth k : ℝ) ∧
      a*x.2+b*y.2 ≤ 1/2+(wallDepth k : ℝ)
    have he : b = 1-a := by linarith
    subst b
    refine ⟨?_,?_,?_⟩
    · nlinarith [mul_nonneg ha (sub_nonneg.mpr hx.1),mul_nonneg hb (sub_nonneg.mpr hy.1)]
    · nlinarith [mul_nonneg ha (sub_nonneg.mpr hx.2.1),mul_nonneg hb (sub_nonneg.mpr hy.2.1)]
    · nlinarith [mul_nonneg ha (sub_nonneg.mpr hx.2.2),mul_nonneg hb (sub_nonneg.mpr hy.2.2)]
  apply convexHull_min (t := {p : ℝ × ℝ | _}) ?_ hc hp
  rintro _ ⟨v,hv,rfl⟩
  have h := of_decide_eq_true ((List.all_eq_true.mp (wall_vertex_bounds_checked k)) v hv)
  change (wallStart k : ℝ) ≤ (v.1 : ℝ) ∧
    (v.1 : ℝ) ≤ (wallStart k : ℝ)+(wallWidth k : ℝ) ∧
    (v.2 : ℝ) ≤ 1/2+(wallDepth k : ℝ)
  refine ⟨by exact_mod_cast h.1,by exact_mod_cast h.2.1,?_⟩
  have hc3 := (Rat.cast_le (K := ℝ)).mpr h.2.2
  norm_num only [Rat.cast_add,Rat.cast_div,Rat.cast_ofNat] at hc3
  exact hc3

theorem wall_parameters (k : Fin 3) :
    (1/2 : ℝ) ≤ wallWidth k ∧ (wallWidth k : ℝ) < 1 ∧
    (1/2 : ℝ) ≤ wallDepth k ∧ (wallDepth k : ℝ) < 1 ∧
    0 < 1/4-((wallWidth k : ℝ)-1/2)^2-((wallDepth k : ℝ)-1/2)^2 ∧
    ∀ b : ℝ, 0 ≤ b → b ≤ 1 → 0 < wallPoly (wallWidth k) (wallDepth k) b := by
  fin_cases k
  · norm_num [wallWidth,wallDepth]
    exact corner_poly_pos
  · norm_num [wallWidth,wallDepth]
    exact outer_poly_pos
  · norm_num [wallWidth,wallDepth]
    exact middle_poly_pos

/-- The actual sixteen wall cells have capacity one in the cover container. -/
theorem wall_capacity : WallCapacity := by
  intro i p q θ φ hpfit hqfit hp hq hdis
  let g := wallAction i
  let k := wallClass i
  let u : ℝ × ℝ := (Real.cos θ,Real.sin θ)
  let v : ℝ × ℝ := (Real.cos φ,Real.sin φ)
  have hpc : action g p ∈ cell (wallCanonical k) := by
    simpa only [g,k,wall_action_checked] using action_mem_cell g (wallIndex i) hp
  have hqc : action g q ∈ cell (wallCanonical k) := by
    simpa only [g,k,wall_action_checked] using action_mem_cell g (wallIndex i) hq
  have hpb := wall_cell_bounds k (action g p) hpc
  have hqb := wall_cell_bounds k (action g q) hqc
  have hu : u.1^2+u.2^2=1 := by dsimp [u]; nlinarith [Real.sin_sq_add_cos_sq θ]
  have hv : v.1^2+v.2^2=1 := by dsimp [v]; nlinarith [Real.sin_sq_add_cos_sq φ]
  have hpf := action_square_fit g p u hpfit
  have hqf := action_square_fit g q v hqfit
  obtain ⟨hw,hw1,hd,hd1,hslack,hpoly⟩ := wall_parameters k
  exact wall_rectangle_capacity (wallWidth k) (wallDepth k) (wallStart k)
    (action g p) (action g q) (direction g u).1 (direction g u).2
    (direction g v).1 (direction g v).2 hw hw1 hd hd1 hslack hpoly
    (direction_unit g u hu) (direction_unit g v hv)
    (fun z hz => (hpf hz).2.2.1) (fun z hz => (hqf hz).2.2.1)
    ⟨hpb.1,hpb.2.1⟩ ⟨hqb.1,hqb.2.1⟩ hpb.2.2 hqb.2.2
    (action_square_disjoint g p q u v hdis)

end Sq17.ExactCells

#print axioms Sq17.ExactCells.wall_action_checked
#print axioms Sq17.ExactCells.wall_cell_bounds
#print axioms Sq17.ExactCells.wall_capacity
