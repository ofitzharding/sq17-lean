import Mathlib.Tactic
import Mathlib.Basic.Real.Basic

/-! Exact polynomial inequalities used by the hand-proved wall-capacity lemma.
This module does not yet formalize the separating-axis geometry. -/
namespace Sq17.WallCapacity

noncomputable def wallPoly (w d b : ℝ) : ℝ :=
  (1 - (d + 1 / 2) * b + b ^ 2 / 2) ^ 2 - (w - b / 2) ^ 2 * (1 - b ^ 2)

private theorem bernstein_pos (x c0 c1 c2 c3 c4 : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hc0 : 0 < c0) (hc1 : 0 < c1) (hc2 : 0 < c2) (hc3 : 0 < c3) (hc4 : 0 < c4) :
    0 < c0 * (1-x)^4 + 4*c1*x*(1-x)^3 + 6*c2*x^2*(1-x)^2 +
      4*c3*x^3*(1-x) + c4*x^4 := by
  by_cases hx : x = 0
  · subst x
    simpa using hc0
  · have hp : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
    have hm : 0 ≤ 1-x := sub_nonneg.mpr hx1
    have h0 : 0 ≤ c0 * (1-x)^4 := by positivity
    have h1 : 0 ≤ 4*c1*x*(1-x)^3 := by positivity
    have h2 : 0 ≤ 6*c2*x^2*(1-x)^2 := by positivity
    have h3 : 0 ≤ 4*c3*x^3*(1-x) := by positivity
    have h4 : 0 < c4*x^4 := by positivity
    linarith

private theorem corner_0 (b : ℝ) (hlo : 0 ≤ b) (hhi : b ≤ (1 / 2)) :
    0 < wallPoly (79 / 100) (79 / 100) b := by
  have ht0 : 0 ≤ 2*b-0 := by linarith
  have ht1 : 2*b-0 ≤ 1 := by linarith
  have h := bernstein_pos (2*b-0) (3759 / 10000) (3043 / 20000) (6599 / 120000) (777 / 40000) (117 / 10000)
    ht0 ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  unfold wallPoly
  ring

private theorem corner_1 (b : ℝ) (hlo : (1 / 2) ≤ b) (hhi : b ≤ 1) :
    0 < wallPoly (79 / 100) (79 / 100) b := by
  have ht0 : 0 ≤ 2*b-1 := by linarith
  have ht1 : 2*b-1 ≤ 1 := by linarith
  have h := bernstein_pos (2*b-1) (117 / 10000) (159 / 40000) (2891 / 120000) (383 / 10000) (441 / 10000)
    ht0 ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  unfold wallPoly
  ring

theorem corner_poly_pos (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 < wallPoly (79 / 100) (79 / 100) b := by
  by_cases h0 : b ≤ (1 / 2)
  · exact corner_0 b (by linarith) h0
  exact corner_1 b (by linarith) hb1

theorem corner_circle_slack :
    (0 : ℝ) < 1/4 - ((79 / 100)-1/2)^2 - ((79 / 100)-1/2)^2 := by norm_num

private theorem outer_0 (b : ℝ) (hlo : 0 ≤ b) (hhi : b ≤ (1 / 4)) :
    0 < wallPoly (529 / 750) (911 / 1000) b := by
  have ht0 : 0 ≤ 4*b-0 := by linarith
  have ht1 : 4*b-0 ≤ 1 := by linarith
  have h := bernstein_pos (4*b-0) (282659 / 562500) (3331919 / 9000000) (234709969 / 864000000) (28593139 / 144000000) (6941983 / 48000000)
    ht0 ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  unfold wallPoly
  ring

private theorem outer_1 (b : ℝ) (hlo : (1 / 4) ≤ b) (hhi : b ≤ (1 / 2)) :
    0 < wallPoly (529 / 750) (911 / 1000) b := by
  have ht0 : 0 ≤ 4*b-1 := by linarith
  have ht1 : 4*b-1 ≤ 1 := by linarith
  have h := bernstein_pos (4*b-1) (6941983 / 48000000) (13058759 / 144000000) (48297409 / 864000000) (4889189 / 144000000) (245807 / 12000000)
    ht0 ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  unfold wallPoly
  ring

private theorem outer_2 (b : ℝ) (hlo : (1 / 2) ≤ b) (hhi : b ≤ (3 / 4)) :
    0 < wallPoly (529 / 750) (911 / 1000) b := by
  have ht0 : 0 ≤ 4*b-2 := by linarith
  have ht1 : 4*b-2 ≤ 1 := by linarith
  have h := bernstein_pos (4*b-2) (245807 / 12000000) (1010179 / 144000000) (1749289 / 864000000) (82927 / 72000000) (286409 / 144000000)
    ht0 ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  unfold wallPoly
  ring

private theorem outer_3 (b : ℝ) (hlo : (3 / 4) ≤ b) (hhi : b ≤ 1) :
    0 < wallPoly (529 / 750) (911 / 1000) b := by
  have ht0 : 0 ≤ 4*b-3 := by linarith
  have ht1 : 4*b-3 ≤ 1 := by linarith
  have h := bernstein_pos (4*b-3) (286409 / 144000000) (101741 / 36000000) (4642609 / 864000000) (520067 / 72000000) (7921 / 1000000)
    ht0 ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  unfold wallPoly
  ring

theorem outer_poly_pos (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 < wallPoly (529 / 750) (911 / 1000) b := by
  by_cases h0 : b ≤ (1 / 4)
  · exact outer_0 b (by linarith) h0
  by_cases h1 : b ≤ (1 / 2)
  · exact outer_1 b (by linarith) h1
  by_cases h2 : b ≤ (3 / 4)
  · exact outer_2 b (by linarith) h2
  exact outer_3 b (by linarith) hb1

theorem outer_circle_slack :
    (0 : ℝ) < 1/4 - ((529 / 750)-1/2)^2 - ((911 / 1000)-1/2)^2 := by norm_num

private theorem middle_0 (b : ℝ) (hlo : 0 ≤ b) (hhi : b ≤ (1 / 4)) :
    0 < wallPoly (257 / 375) (93 / 100) b := by
  have ht0 : 0 ≤ 4*b-0 := by linarith
  have ht1 : 4*b-0 ≤ 1 := by linarith
  have h := bernstein_pos (4*b-0) (74576 / 140625) (1774807 / 4500000) (12635609 / 43200000) (31150567 / 144000000) (766027 / 4800000)
    ht0 ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  unfold wallPoly
  ring

private theorem middle_1 (b : ℝ) (hlo : (1 / 4) ≤ b) (hhi : b ≤ (1 / 2)) :
    0 < wallPoly (257 / 375) (93 / 100) b := by
  have ht0 : 0 ≤ 4*b-1 := by linarith
  have ht1 : 4*b-1 ≤ 1 := by linarith
  have h := bernstein_pos (4*b-1) (766027 / 4800000) (14811053 / 144000000) (14159503 / 216000000) (372377 / 9000000) (77891 / 3000000)
    ht0 ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  unfold wallPoly
  ring

private theorem middle_2 (b : ℝ) (hlo : (1 / 2) ≤ b) (hhi : b ≤ (3 / 4)) :
    0 < wallPoly (257 / 375) (93 / 100) b := by
  have ht0 : 0 ≤ 4*b-2 := by linarith
  have ht1 : 4*b-2 ≤ 1 := by linarith
  have h := bernstein_pos (4*b-2) (77891 / 3000000) (94969 / 9000000) (843919 / 216000000) (240719 / 144000000) (103849 / 72000000)
    ht0 ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  unfold wallPoly
  ring

private theorem middle_3 (b : ℝ) (hlo : (3 / 4) ≤ b) (hhi : b ≤ 1) :
    0 < wallPoly (257 / 375) (93 / 100) b := by
  have ht0 : 0 ≤ 4*b-3 := by linarith
  have ht1 : 4*b-3 ≤ 1 := by linarith
  have h := bernstein_pos (4*b-3) (103849 / 72000000) (174677 / 144000000) (645793 / 216000000) (78641 / 18000000) (49 / 10000)
    ht0 ht1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  unfold wallPoly
  ring

theorem middle_poly_pos (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 < wallPoly (257 / 375) (93 / 100) b := by
  by_cases h0 : b ≤ (1 / 4)
  · exact middle_0 b (by linarith) h0
  by_cases h1 : b ≤ (1 / 2)
  · exact middle_1 b (by linarith) h1
  by_cases h2 : b ≤ (3 / 4)
  · exact middle_2 b (by linarith) h2
  exact middle_3 b (by linarith) hb1

theorem middle_circle_slack :
    (0 : ℝ) < 1/4 - ((257 / 375)-1/2)^2 - ((93 / 100)-1/2)^2 := by norm_num

theorem nearest_endpoint (a b x : ℝ) (ha : a ≤ x) (hb : x ≤ b) :
    ∃ e : ℝ, (e = a ∨ e = b) ∧ 4 * (x-e)^2 ≤ (b-a)^2 := by
  by_cases h : 2*x ≤ a+b
  · refine ⟨a, Or.inl rfl, ?_⟩
    have hm : 0 ≤ (b-a-2*(x-a)) * (b-a+2*(x-a)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · refine ⟨b, Or.inr rfl, ?_⟩
    have hm : 0 ≤ (b-a-2*(b-x)) * (b-a+2*(b-x)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- The quantitative core of the four-corner obstruction, with arbitrary rectangle. -/
theorem rectangle_corner (a b c d x y : ℝ)
    (hx0 : a ≤ x) (hx1 : x ≤ b) (hy0 : c ≤ y) (hy1 : y ≤ d)
    (hdiag : (b-a)^2 + (d-c)^2 < 1) :
    ∃ u v : ℝ, (u = a ∨ u = b) ∧ (v = c ∨ v = d) ∧
      (x-u)^2 + (y-v)^2 < 1/4 := by
  obtain ⟨u, hu, hux⟩ := nearest_endpoint a b x hx0 hx1
  obtain ⟨v, hv, hvy⟩ := nearest_endpoint c d y hy0 hy1
  exact ⟨u, v, hu, hv, by nlinarith⟩

end Sq17.WallCapacity

#print axioms Sq17.WallCapacity.corner_poly_pos
#print axioms Sq17.WallCapacity.outer_poly_pos
#print axioms Sq17.WallCapacity.middle_poly_pos
#print axioms Sq17.WallCapacity.rectangle_corner
