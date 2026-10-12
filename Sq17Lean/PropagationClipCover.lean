import Sq17Lean.PropagationClipHull

/-! Finite convex-hull coverage for a closed half-plane cut. -/
namespace Sq17.Propagation
open scoped BigOperators

/-- A crossing point is computed using exact scalar division. -/
noncomputable def cutPoint (a b : ℝ) (u v : ℝ × ℝ) : ℝ × ℝ :=
  ((b*u.1-a*v.1)/(b-a), (b*u.2-a*v.2)/(b-a))

/-- A split barycentric combination on the retained side can be reconstructed
using retained vertices and all retained/outside crossing points. -/
theorem split_clip_mem_hull {I J : Type*} [Fintype I] [Fintype J]
    (α a : I → ℝ) (u : I → ℝ × ℝ)
    (β b : J → ℝ) (v : J → ℝ × ℝ)
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ j, 0 ≤ β j)
    (ha : ∀ i, a i ≤ 0) (hb : ∀ j, 0 < b j)
    (hmass : (∑ i, α i) + ∑ j, β j = 1)
    (hweak : (∑ i, α i*a i) + ∑ j, β j*b j ≤ 0) :
    (∑ i, α i • u i) + (∑ j, β j • v j) ∈
      convexHull ℝ (Set.range u ∪ Set.range (fun ij : I × J =>
        cutPoint (a ij.1) (b ij.2) (u ij.1) (v ij.2))) := by
  classical
  let A := ∑ i, α i * (-a i)
  let B := ∑ j, β j * b j
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ => mul_nonneg (hβ j) (hb j).le
  have hAB : B ≤ A := by
    have hneg : A = -(∑ i, α i*a i) := by simp [A, Finset.sum_neg_distrib]
    dsimp [B]
    linarith
  by_cases hzero : A = 0
  · have hBzero : B = 0 := le_antisymm (hAB.trans_eq hzero) hB
    have hβzero : ∀ j, β j = 0 := by
      intro j
      have hle : β j*b j ≤ B := Finset.single_le_sum
        (fun k _ => mul_nonneg (hβ k) (hb k).le) (Finset.mem_univ j)
      have hp : β j*b j = 0 := le_antisymm (hle.trans_eq hBzero)
        (mul_nonneg (hβ j) (hb j).le)
      exact (mul_eq_zero.mp hp).resolve_right (ne_of_gt (hb j))
    have hm : ∑ i, α i = 1 := by simpa [hβzero] using hmass
    simp only [hβzero, zero_smul, Finset.sum_const_zero, add_zero]
    exact mem_convexHull_of_exists_fintype α u hα hm
      (fun i => Or.inl ⟨i, rfl⟩) rfl
  have hA : 0 < A := lt_of_le_of_ne (hB.trans hAB) (Ne.symm hzero)
  have hden (i : I) (j : J) : b j-a i ≠ 0 := ne_of_gt (by linarith [ha i, hb j])
  let weights : I ⊕ (I × J) → ℝ := Sum.elim
    (fun i => α i*(1-B/A)) (fun ij => α ij.1*β ij.2*(b ij.2-a ij.1)/A)
  let points : I ⊕ (I × J) → ℝ × ℝ := Sum.elim u
    (fun ij => cutPoint (a ij.1) (b ij.2) (u ij.1) (v ij.2))
  apply mem_convexHull_of_exists_fintype weights points
  · intro k
    cases k with
    | inl i =>
      exact mul_nonneg (hα i) (sub_nonneg.mpr ((div_le_one hA).mpr hAB))
    | inr ij =>
      exact div_nonneg (mul_nonneg (mul_nonneg (hα ij.1) (hβ ij.2))
        (by linarith [ha ij.1, hb ij.2])) hA.le
  · have hid := clip_weight_reconstruction α a (fun _ => 1) β b (fun _ => 1)
      A B rfl rfl (ne_of_gt hA) hden
    simp only [mul_one, div_self (hden _ _)] at hid
    simpa only [weights, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Sum.elim_inl, Sum.elim_inr] using hid.trans hmass
  · intro k
    cases k with
    | inl i => exact Set.mem_union_left _ ⟨i, rfl⟩
    | inr ij => exact Set.mem_union_right _ ⟨ij, rfl⟩
  · have hfirst := clip_weight_reconstruction α a (fun i => (u i).1)
      β b (fun j => (v j).1) A B rfl rfl (ne_of_gt hA) hden
    have hsecond := clip_weight_reconstruction α a (fun i => (u i).2)
      β b (fun j => (v j).2) A B rfl rfl (ne_of_gt hA) hden
    ext <;> simp only [weights, points, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Sum.elim_inl, Sum.elim_inr, Prod.fst_add, Prod.snd_add, Prod.fst_sum,
      Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, cutPoint]
    · exact hfirst
    · exact hsecond

end Sq17.Propagation

#print axioms Sq17.Propagation.split_clip_mem_hull
