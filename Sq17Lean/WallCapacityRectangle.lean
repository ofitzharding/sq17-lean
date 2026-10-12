import Sq17Lean.WallMixedSupport
import Sq17Lean.WallSquareSupport
import Sq17Lean.WallCapacityObstructions

/-! Actual square capacity for a rectangle next to a wall. Ordinary convex
separation and the mixed-support inequality suffice; no edge-normal theorem
or unverified geometric premise is used. -/
namespace Sq17.WallCapacity

private theorem wall_rectangle_ordered (w d x0 : ℝ) (p q : ℝ × ℝ)
    (ux uy vx vy : ℝ) (hw : 1/2 ≤ w) (hw1 : w < 1)
    (hd : 1/2 ≤ d) (hd1 : d < 1)
    (hslack : 0 < 1/4-(w-1/2)^2-(d-1/2)^2)
    (hpoly : ∀ t, 0 ≤ t → t ≤ 1 → 0 < wallPoly w d t)
    (hu : ux^2+uy^2=1) (hv : vx^2+vy^2=1)
    (hpfit : Sq17.sq p.1 p.2 ux uy ⊆ {z | 0 ≤ z.2})
    (hpx : x0 ≤ p.1 ∧ p.1 ≤ x0+w) (hqx : x0 ≤ q.1 ∧ q.1 ≤ x0+w)
    (hqy : q.2 ≤ 1/2+d) (horder : p.2 ≤ q.2) :
    ¬ Disjoint (interior (Sq17.sq p.1 p.2 ux uy))
      (interior (Sq17.sq q.1 q.2 vx vy)) := by
  intro hdis
  obtain ⟨a,b,hm,hsep⟩ := square_disjoint_unit_separator p q ux uy vx vy hu hv hdis
  have haunit : |a|^2+b^2 = 1 := by simpa only [sq_abs] using hm
  have ha1 : |a| ≤ 1 := by nlinarith [sq_abs a,sq_nonneg b,abs_nonneg a]
  have hpS := squareSupport_ge_half ux uy a b hu hm
  have hqS := squareSupport_ge_half vx vy a b hv hm
  have hdx : |q.1-p.1| ≤ w := abs_le.mpr ⟨by linarith [hpx.2,hqx.1],by linarith [hpx.1,hqx.2]⟩
  have hx : a*(q.1-p.1) ≤ |a| * w := calc
    _ ≤ |a*(q.1-p.1)| := le_abs_self _
    _ = |a| * |q.1-p.1| := abs_mul _ _
    _ ≤ |a| * w := mul_le_mul_of_nonneg_left hdx (abs_nonneg a)
  have hb : 0 ≤ b := by
    by_contra hn
    have hby : b*(q.2-p.2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hn)) (sub_nonneg.mpr horder)
    have haw : |a| * w ≤ w := by nlinarith [mul_nonneg (show 0 ≤ w by linarith) (sub_nonneg.mpr ha1)]
    linarith
  have hwall := squareSupport_wall_bound p.1 p.2 ux uy hu hpfit
  have hwm := mul_le_mul_of_nonneg_left hwall hb
  have hqy' := mul_le_mul_of_nonneg_left hqy hb
  have hsum : squareSupport ux uy a b+b*squareSupport ux uy 0 1+1/2 ≤
      |a| * w+b*(1/2+d) := by linarith
  have hmix := mixed_support_normal a b ux uy hb hm hu
  have hmixed : min (|a|+2*b) (1+|a| * b+b^2) ≤
      2*(squareSupport ux uy a b+b*squareSupport ux uy 0 1) := by
    have he : 2*(squareSupport ux uy a b+b*squareSupport ux uy 0 1) =
        |a*ux+b*uy|+|b*ux-a*uy|+b*(|ux|+|uy|) := by
      simp only [squareSupport,zero_mul,one_mul,zero_add,sub_zero]
      ring
    rw [he]
    exact hmix
  apply wall_candidates_excluded w d |a| b hw hd hd1 (abs_nonneg a) hb haunit hslack hpoly
  by_cases hmin : |a|+2*b ≤ 1+|a| * b+b^2
  · rw [min_eq_left hmin] at hmixed
    right
    nlinarith only [hmixed,hsum]
  · rw [min_eq_right (le_of_not_ge hmin)] at hmixed
    left
    nlinarith only [hmixed,hsum]

theorem wall_rectangle_capacity (w d x0 : ℝ) (p q : ℝ × ℝ)
    (ux uy vx vy : ℝ) (hw : 1/2 ≤ w) (hw1 : w < 1)
    (hd : 1/2 ≤ d) (hd1 : d < 1)
    (hslack : 0 < 1/4-(w-1/2)^2-(d-1/2)^2)
    (hpoly : ∀ t, 0 ≤ t → t ≤ 1 → 0 < wallPoly w d t)
    (hu : ux^2+uy^2=1) (hv : vx^2+vy^2=1)
    (hpfit : Sq17.sq p.1 p.2 ux uy ⊆ {z | 0 ≤ z.2})
    (hqfit : Sq17.sq q.1 q.2 vx vy ⊆ {z | 0 ≤ z.2})
    (hpx : x0 ≤ p.1 ∧ p.1 ≤ x0+w) (hqx : x0 ≤ q.1 ∧ q.1 ≤ x0+w)
    (hpy : p.2 ≤ 1/2+d) (hqy : q.2 ≤ 1/2+d) :
    ¬ Disjoint (interior (Sq17.sq p.1 p.2 ux uy))
      (interior (Sq17.sq q.1 q.2 vx vy)) := by
  by_cases horder : p.2 ≤ q.2
  · exact wall_rectangle_ordered w d x0 p q ux uy vx vy hw hw1 hd hd1 hslack hpoly
      hu hv hpfit hpx hqx hqy horder
  · intro hdis
    exact wall_rectangle_ordered w d x0 q p vx vy ux uy hw hw1 hd hd1 hslack hpoly
      hv hu hqfit hqx hpx hpy (le_of_not_ge horder) hdis.symm

end Sq17.WallCapacity
#print axioms Sq17.WallCapacity.wall_rectangle_capacity
