import Sq17Lean.WallCapacityBounds

/-! The analytic consequences of the exact wall-cell quartics. These exclude
the two candidate separation inequalities from the hand argument; deriving
those candidates from disjoint actual squares remains a geometric obligation. -/
namespace Sq17.WallCapacity

theorem wallPoly_excludes_axis (w d a b : ℝ)
    (hw : 1/2 ≤ w) (hd : 1/2 ≤ d) (hd1 : d < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hunit : a^2+b^2 = 1) (hpoly : 0 < wallPoly w d b) :
    w*a+(d+1/2)*b-(a*b+b^2)/2 < 1 := by
  let L := 1-(d+1/2)*b+b^2/2
  let R := (w-b/2)*a
  have hL : 0 < L := by
    have h := mul_nonneg (show 0 ≤ 1-b by linarith)
      (show 0 ≤ d-b/2 by linarith)
    dsimp [L]
    nlinarith
  have hR : 0 ≤ R := mul_nonneg (by linarith) ha
  have he : (w-b/2)^2*(1-b^2) = R^2 := by
    rw [show 1-b^2 = a^2 by linarith]
    dsimp [R]
    ring
  have hs : R^2 < L^2 := by
    unfold wallPoly at hpoly
    rw [he] at hpoly
    exact sub_pos.mp hpoly
  have hlt : R < L := by nlinarith
  dsimp [R,L] at hlt
  linarith

theorem circle_slack_excludes_axis (w d a b : ℝ)
    (hunit : a^2+b^2 = 1)
    (hslack : 0 < 1/4-(w-1/2)^2-(d-1/2)^2) :
    (w-1/2)*a+(d-1/2)*b < 1/2 := by
  have he : ((w-1/2)*a+(d-1/2)*b)^2+
      ((w-1/2)*b-(d-1/2)*a)^2 =
      ((w-1/2)^2+(d-1/2)^2)*(a^2+b^2) := by ring
  rw [hunit,mul_one] at he
  have hs := sq_nonneg ((w-1/2)*b-(d-1/2)*a)
  nlinarith

/-- Both possible scalar obstructions are strictly below their required
separation thresholds. This includes endpoint orientations. -/
theorem wall_candidates_excluded (w d a b : ℝ)
    (hw : 1/2 ≤ w) (hd : 1/2 ≤ d) (hd1 : d < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hunit : a^2+b^2 = 1)
    (hslack : 0 < 1/4-(w-1/2)^2-(d-1/2)^2)
    (hpoly : ∀ t, 0 ≤ t → t ≤ 1 → 0 < wallPoly w d t) :
    ¬ (1 ≤ w*a+(d+1/2)*b-(a*b+b^2)/2 ∨
      1/2 ≤ (w-1/2)*a+(d-1/2)*b) := by
  have hb1 : b ≤ 1 := by nlinarith [sq_nonneg a]
  have h₁ := wallPoly_excludes_axis w d a b hw hd hd1 ha hb hb1 hunit (hpoly b hb hb1)
  have h₂ := circle_slack_excludes_axis w d a b hunit hslack
  rintro (h | h) <;> linarith

theorem corner_candidates_excluded (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hunit : a^2+b^2 = 1) :
    ¬ (1 ≤ (79/100)*a+(79/100+1/2)*b-(a*b+b^2)/2 ∨
      1/2 ≤ (79/100-1/2)*a+(79/100-1/2)*b) :=
  wall_candidates_excluded _ _ a b (by norm_num) (by norm_num) (by norm_num)
    ha hb hunit corner_circle_slack corner_poly_pos

theorem outer_candidates_excluded (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hunit : a^2+b^2 = 1) :
    ¬ (1 ≤ (529/750)*a+(911/1000+1/2)*b-(a*b+b^2)/2 ∨
      1/2 ≤ (529/750-1/2)*a+(911/1000-1/2)*b) :=
  wall_candidates_excluded _ _ a b (by norm_num) (by norm_num) (by norm_num)
    ha hb hunit outer_circle_slack outer_poly_pos

theorem middle_candidates_excluded (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hunit : a^2+b^2 = 1) :
    ¬ (1 ≤ (257/375)*a+(93/100+1/2)*b-(a*b+b^2)/2 ∨
      1/2 ≤ (257/375-1/2)*a+(93/100-1/2)*b) :=
  wall_candidates_excluded _ _ a b (by norm_num) (by norm_num) (by norm_num)
    ha hb hunit middle_circle_slack middle_poly_pos

end Sq17.WallCapacity
#print axioms Sq17.WallCapacity.wallPoly_excludes_axis
#print axioms Sq17.WallCapacity.circle_slack_excludes_axis
#print axioms Sq17.WallCapacity.wall_candidates_excluded
#print axioms Sq17.WallCapacity.corner_candidates_excluded
#print axioms Sq17.WallCapacity.outer_candidates_excluded
#print axioms Sq17.WallCapacity.middle_candidates_excluded
