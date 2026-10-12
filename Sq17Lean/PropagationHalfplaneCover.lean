import Sq17Lean.PropagationClipCover

/-! A strict half-plane portion of a convex hull is covered by retained source
points and all crossing intersections. For a finite source this is finite. -/
namespace Sq17.Propagation
open scoped BigOperators

def clipCandidates (s : Set (ℝ × ℝ)) (f : (ℝ × ℝ) →ₗ[ℝ] ℝ) (q : ℝ) :
    Set (ℝ × ℝ) :=
  (s ∩ {u | f u ≤ q}) ∪ {z | ∃ u ∈ s, ∃ v ∈ s,
    f u ≤ q ∧ q < f v ∧ z = cutPoint (f u-q) (f v-q) u v}

/-- Whole-hull coverage, including a cut through an edge or vertex, independent
of edge order or polygon orientation. -/
theorem closed_halfplane_hull_coverage
    (s : Set (ℝ × ℝ)) (f : (ℝ × ℝ) →ₗ[ℝ] ℝ) (q : ℝ)
    (x : ℝ × ℝ) (hx : x ∈ convexHull ℝ s) (hcut : f x ≤ q) :
    x ∈ convexHull ℝ (clipCandidates s f q) := by
  classical
  rcases mem_convexHull_iff_exists_fintype.mp hx with ⟨K, _, w, z, hw, hm, hz, hx⟩
  let a : K → ℝ := fun i => f (z i)-q
  let I := {i : K // a i ≤ 0}
  let J := {i : K // ¬a i ≤ 0}
  have hmass : (∑ i : I, w i) + (∑ j : J, w j) = 1 :=
    (Fintype.sum_subtype_add_sum_subtype (fun i => a i ≤ 0) w).trans hm
  have hform : (∑ i, w i*a i) = f x-q := by
    rw [← hx, map_sum]
    simp only [a, mul_sub, map_smul, smul_eq_mul, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hm, one_mul]
  have hstrict : (∑ i : I, w i*a i) + (∑ j : J, w j*a j) ≤ 0 := by
    rw [Fintype.sum_subtype_add_sum_subtype (fun i => a i ≤ 0) (fun i => w i*a i)]
    rw [hform]
    linarith
  have hc := split_clip_mem_hull (fun i : I => w i) (fun i : I => a i)
    (fun i : I => z i) (fun j : J => w j) (fun j : J => a j) (fun j : J => z j)
    (fun i => hw i) (fun j => hw j) (fun i => i.property)
    (fun j => lt_of_not_ge j.property) hmass hstrict
  have heq : (∑ i : I, w i • z i) + (∑ j : J, w j • z j) = x :=
    (Fintype.sum_subtype_add_sum_subtype (fun i => a i ≤ 0)
      (fun i => w i • z i)).trans hx
  rw [heq] at hc
  apply convexHull_mono (s := Set.range (fun i : I => z i) ∪
    Set.range (fun ij : I × J => cutPoint (a ij.1) (a ij.2) (z ij.1) (z ij.2))) ?_ hc
  intro y hy
  rcases hy with ⟨i, rfl⟩ | ⟨⟨i,j⟩, rfl⟩
  · exact Or.inl ⟨hz i, sub_nonpos.mp i.property⟩
  · exact Or.inr ⟨z i, hz i, z j, hz j, sub_nonpos.mp i.property,
      sub_pos.mp (lt_of_not_ge j.property), rfl⟩

/-- Strict removal is an immediate special case of closed coverage. -/
theorem strict_halfplane_hull_coverage
    (s : Set (ℝ × ℝ)) (f : (ℝ × ℝ) →ₗ[ℝ] ℝ) (q : ℝ)
    (x : ℝ × ℝ) (hx : x ∈ convexHull ℝ s) (hcut : f x < q) :
    x ∈ convexHull ℝ (clipCandidates s f q) :=
  closed_halfplane_hull_coverage s f q x hx hcut.le

end Sq17.Propagation

#print axioms Sq17.Propagation.closed_halfplane_hull_coverage
#print axioms Sq17.Propagation.strict_halfplane_hull_coverage
