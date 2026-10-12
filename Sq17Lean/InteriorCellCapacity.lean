import Sq17Lean.SquareBase
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Capacity one for the eight interior cells

The geometric lemmas use the actual `Sq17.sq` interiors. Exact rational vertex
certificates below apply to the closed convex hulls, including their boundaries.
This file does not prove coverage of the container, wall-cell capacity, or the
finite orbit census.
-/
namespace Sq17.InteriorCells

def distSq (p q : ℝ × ℝ) : ℝ := (p.1-q.1)^2 + (p.2-q.2)^2

theorem distSq_comm (p q : ℝ × ℝ) : distSq p q = distSq q p := by
  unfold distSq
  ring

/-- A squared Euclidean ball is convex, proved algebraically so there is no
norm convention on the product space hidden in the diameter statement. -/
theorem convex_distSq_le (q : ℝ × ℝ) (r : ℝ) :
    Convex ℝ {p | distSq p q ≤ r} := by
  intro x hx y hy a b ha hb hab
  change distSq x q ≤ r at hx
  change distSq y q ≤ r at hy
  change distSq (a • x + b • y) q ≤ r
  have hvar : 0 ≤ a*b*((x.1-y.1)^2+(x.2-y.2)^2) :=
    mul_nonneg (mul_nonneg ha hb) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have he : distSq (a • x + b • y) q =
      a * distSq x q + b * distSq y q -
        a*b*((x.1-y.1)^2+(x.2-y.2)^2) := by
    have hb' : b = 1-a := by linarith
    subst b
    dsimp [distSq]
    ring
  rw [he]
  have h := add_le_add (mul_le_mul_of_nonneg_left hx ha)
    (mul_le_mul_of_nonneg_left hy hb)
  have hr : a*r+b*r = r := by rw [← add_mul, hab, one_mul]
  linarith only [h, hvar, hr]

/-- A vertex-pair bound controls every pair of points in the closed hull. -/
theorem hull_distSq_le (V : Set (ℝ × ℝ)) (r : ℝ)
    (hV : ∀ p ∈ V, ∀ q ∈ V, distSq p q ≤ r)
    {x y : ℝ × ℝ} (hx : x ∈ convexHull ℝ V) (hy : y ∈ convexHull ℝ V) :
    distSq x y ≤ r := by
  have hver (q : ℝ × ℝ) (hq : q ∈ V) :
      ∀ p ∈ convexHull ℝ V, distSq p q ≤ r :=
    convexHull_min (fun p hp => hV p hp q hq) (convex_distSq_le q r)
  have h : convexHull ℝ V ⊆ {p | distSq p x ≤ r} :=
    convexHull_min (fun p hp => by
      change distSq p x ≤ r
      rw [distSq_comm]
      exact hver p hp x hx)
      (convex_distSq_le x r)
  rw [distSq_comm]
  exact h hy

private theorem abs_lt_half_of_sq_lt {a : ℝ} (ha : a^2 < 1/4) : |a| < 1/2 := by
  rw [abs_lt]
  constructor <;> nlinarith [sq_nonneg (a-1/2), sq_nonneg (a+1/2)]

/-- The open radius-one-half disk lies inside the square interior, for every
unit side direction. Contact remains legal: all inequalities here are strict. -/
theorem disk_subset_square_interior (cx cy u v : ℝ) (hu : u^2+v^2=1)
    {z : ℝ × ℝ} (hz : distSq z (cx,cy) < 1/4) :
    z ∈ interior (Sq17.sq cx cy u v) := by
  let O : Set (ℝ × ℝ) := {p | |(p.1-cx)*u+(p.2-cy)*v| < 1/2 ∧
    |(p.2-cy)*u-(p.1-cx)*v| < 1/2}
  have hopen : IsOpen O := by
    change IsOpen ({p : ℝ × ℝ | |(p.1-cx)*u+(p.2-cy)*v| < 1/2} ∩
      {p : ℝ × ℝ | |(p.2-cy)*u-(p.1-cx)*v| < 1/2})
    exact (isOpen_lt (by fun_prop) (by fun_prop)).inter
      (isOpen_lt (by fun_prop) (by fun_prop))
  have hsub : O ⊆ Sq17.sq cx cy u v := fun _ h => ⟨h.1.le,h.2.le⟩
  apply (hopen.subset_interior_iff.mpr hsub)
  have hid : ((z.1-cx)*u+(z.2-cy)*v)^2 + ((z.2-cy)*u-(z.1-cx)*v)^2 =
      distSq z (cx,cy) := by
    calc
      _ = ((z.1-cx)^2+(z.2-cy)^2)*(u^2+v^2) := by ring
      _ = _ := by rw [hu]; simp [distSq]
  exact ⟨abs_lt_half_of_sq_lt (by nlinarith [sq_nonneg ((z.2-cy)*u-(z.1-cx)*v)]),
    abs_lt_half_of_sq_lt (by nlinarith [sq_nonneg ((z.1-cx)*u+(z.2-cy)*v)])⟩

/-- Centres strictly less than one unit apart force overlap of the actual
square interiors: their midpoint lies in both inscribed open disks. -/
theorem not_disjoint_of_distSq_lt_one (p q : ℝ × ℝ) (u v a b : ℝ)
    (hu : u^2+v^2=1) (ha : a^2+b^2=1) (hd : distSq p q < 1) :
    ¬ Disjoint (interior (Sq17.sq p.1 p.2 u v))
      (interior (Sq17.sq q.1 q.2 a b)) := by
  let m : ℝ × ℝ := ((p.1+q.1)/2,(p.2+q.2)/2)
  have hp : distSq m p = distSq p q / 4 := by dsimp [m,distSq]; ring
  have hq : distSq m q = distSq p q / 4 := by dsimp [m,distSq]; ring
  have hm1 := disk_subset_square_interior p.1 p.2 u v hu (z := m)
    (by simpa only [Prod.eta, hp] using (show distSq p q / 4 < 1/4 by linarith))
  have hm2 := disk_subset_square_interior q.1 q.2 a b ha (z := m)
    (by simpa only [Prod.eta, hq] using (show distSq p q / 4 < 1/4 by linarith))
  exact fun h => Set.disjoint_left.mp h hm1 hm2


/-- Exact vertex columns of `states/cells.txt`, in their original order. -/
def vertices : Fin 8 → List (ℚ × ℚ) := ![
  -- interior-SW
  [(1411/1000, 1411/1000), (91867/46000, 1411/1000), (39044849/19226000, 3707059/1922600), (1048947/519200, 1048947/519200), (3707059/1922600, 39044849/19226000), (1411/1000, 91867/46000)],
  -- interior-NW
  [(1411/1000, 123229/46000), (3707059/1922600, 50855927/19226000), (1048947/519200, 6894161/2596000), (39044849/19226000, 26415093/9613000), (91867/46000, 653/200), (1411/1000, 653/200)],
  -- interior-W
  [(143/100, 999/500), (1048947/519200, 1048947/519200), (1169/500, 1169/500), (1048947/519200, 6894161/2596000), (143/100, 1339/500)],
  -- interior-S
  [(999/500, 143/100), (1339/500, 143/100), (6894161/2596000, 1048947/519200), (1169/500, 1169/500), (1048947/519200, 1048947/519200)],
  -- interior-N
  [(999/500, 1623/500), (1048947/519200, 6894161/2596000), (1169/500, 1169/500), (6894161/2596000, 6894161/2596000), (1339/500, 1623/500)],
  -- interior-E
  [(1169/500, 1169/500), (6894161/2596000, 1048947/519200), (1623/500, 999/500), (1623/500, 1339/500), (6894161/2596000, 6894161/2596000)],
  -- interior-SE
  [(50855927/19226000, 3707059/1922600), (123229/46000, 1411/1000), (653/200, 1411/1000), (653/200, 91867/46000), (26415093/9613000, 39044849/19226000), (6894161/2596000, 1048947/519200)],
  -- interior-NE
  [(50855927/19226000, 26415093/9613000), (6894161/2596000, 6894161/2596000), (26415093/9613000, 50855927/19226000), (653/200, 123229/46000), (653/200, 653/200), (123229/46000, 653/200)]]

def vertexDiameterCheck (vs : List (ℚ × ℚ)) : Bool :=
  vs.all (fun p => vs.all (fun q =>
    decide ((p.1-q.1)^2+(p.2-q.2)^2 ≤ (29377/31250 : ℚ))))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- All finite rational checks are proved by kernel reduction, not native_decide. -/
theorem all_vertex_diameter_checks : ∀ i : Fin 8, vertexDiameterCheck (vertices i) = true := by
  decide +kernel

noncomputable def realVertex (p : ℚ × ℚ) : ℝ × ℝ := (p.1,p.2)

/-- The closed hull of one of the eight exact interior vertex lists. -/
def cell (i : Fin 8) : Set (ℝ × ℝ) :=
  convexHull ℝ (realVertex '' {p | p ∈ vertices i})

theorem interior_cells_diameter_bound (i : Fin 8) {p q : ℝ × ℝ}
    (hp : p ∈ cell i) (hq : q ∈ cell i) : distSq p q ≤ 29377/31250 := by
  apply hull_distSq_le _ _ ?_ hp hq
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
  have hc := all_vertex_diameter_checks i
  simp only [vertexDiameterCheck, List.all_eq_true, decide_eq_true_eq] at hc
  have h := hc a ha b hb
  dsimp [distSq,realVertex]
  have hr := (Rat.cast_le (K := ℝ)).mpr h
  norm_num only [Rat.cast_add, Rat.cast_sub, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat] at hr
  exact hr

/-- Two disjoint unit-square interiors cannot have their centres in the same
one of these eight closed hulls. No angle normalization is assumed. -/
theorem interior_cell_capacity_one (i : Fin 8) (p q : ℝ × ℝ) (u v a b : ℝ)
    (hu : u^2+v^2=1) (ha : a^2+b^2=1)
    (hp : p ∈ cell i) (hq : q ∈ cell i) :
    ¬ Disjoint (interior (Sq17.sq p.1 p.2 u v))
      (interior (Sq17.sq q.1 q.2 a b)) := by
  apply not_disjoint_of_distSq_lt_one p q u v a b hu ha
  exact lt_of_le_of_lt (interior_cells_diameter_bound i hp hq) (by norm_num)

/-- Translating the cover by any common vector preserves its capacity bound.
This covers the centred target shift used by the propagation inputs. -/
theorem translated_interior_cell_capacity_one (i : Fin 8) (t p q : ℝ × ℝ)
    (u v a b : ℝ) (hu : u^2+v^2=1) (ha : a^2+b^2=1)
    (hp : p+t ∈ cell i) (hq : q+t ∈ cell i) :
    ¬ Disjoint (interior (Sq17.sq p.1 p.2 u v))
      (interior (Sq17.sq q.1 q.2 a b)) := by
  have h := interior_cells_diameter_bound i hp hq
  have he : distSq (p+t) (q+t) = distSq p q := by dsimp [distSq]; ring
  rw [he] at h
  apply not_disjoint_of_distSq_lt_one p q u v a b hu ha
  exact lt_of_le_of_lt h (by norm_num)

end Sq17.InteriorCells

#print axioms Sq17.InteriorCells.interior_cell_capacity_one
#print axioms Sq17.InteriorCells.all_vertex_diameter_checks
#print axioms Sq17.InteriorCells.interior_cells_diameter_bound


#print axioms Sq17.InteriorCells.translated_interior_cell_capacity_one
