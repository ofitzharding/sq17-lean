import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Algebraic mixed support bound on unit directions in the first quadrant.
The two linear sectors have only the wall-aligned and normal-aligned endpoints. -/
namespace Sq17.WallCapacity

private theorem unit_cone_sum (a b l m : ℝ) (hu : a^2+b^2 = 1)
    (ha : a ≤ 1) (hl : 0 ≤ l) (hm : 0 ≤ m)
    (hv : (l+m*a)^2+(m*b)^2 = 1) : 1 ≤ l+m := by
  have he : (l+m)^2-((l+m*a)^2+(m*b)^2) = 2*l*m*(1-a) := by
    calc
      _ = 2*l*m*(1-a)+m^2*(1-(a^2+b^2)) := by ring
      _ = _ := by rw [hu]; ring
  have hn : 0 ≤ 2*l*m*(1-a) := by positivity
  nlinarith

private theorem weighted_min (x y l m : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hl : 0 ≤ l) (hm : 0 ≤ m) (hs : 1 ≤ l+m) : min x y ≤ l*x+m*y := by
  have h₁ := mul_le_mul_of_nonneg_left (min_le_left x y) hl
  have h₂ := mul_le_mul_of_nonneg_left (min_le_right x y) hm
  have h₃ := mul_le_mul_of_nonneg_left hs (le_min hx hy)
  nlinarith

theorem mixed_support_first_quadrant (a b c s : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hu : a^2+b^2 = 1) (hv : c^2+s^2 = 1) :
    min (a+2*b) (1+a*b+b^2) ≤
      |a*c+b*s|+|b*c-a*s|+b*(|c|+|s|) := by
  have ha1 : a ≤ 1 := by nlinarith [sq_nonneg b]
  have hb1 : b ≤ 1 := by nlinarith [sq_nonneg a]
  have hcs : 0 ≤ a*c+b*s := add_nonneg (mul_nonneg ha hc) (mul_nonneg hb hs)
  rw [abs_of_nonneg hcs,abs_of_nonneg hc,abs_of_nonneg hs]
  have hx : 0 ≤ a+2*b := by positivity
  have hy : 0 ≤ 1+a*b+b^2 := by positivity
  by_cases hsector : a*s ≤ b*c
  · rw [abs_of_nonneg (sub_nonneg.mpr hsector)]
    by_cases hb0 : b = 0
    · subst b
      have haeq : a = 1 := by nlinarith
      have hseq : s = 0 := by nlinarith
      have hceq : c = 1 := by nlinarith
      simp [haeq,hseq,hceq]
    · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      let l := (b*c-a*s)/b
      let m := s/b
      have hl : 0 ≤ l := div_nonneg (sub_nonneg.mpr hsector) hb
      have hm : 0 ≤ m := div_nonneg hs hb
      have hc' : l+m*a = c := by dsimp [l,m]; field_simp; ring
      have hs' : m*b = s := by dsimp [m]; field_simp
      have hsum := unit_cone_sum a b l m hu ha1 hl hm (by rw [hc',hs']; exact hv)
      have hmin := weighted_min (a+2*b) (1+a*b+b^2) l m hx hy hl hm hsum
      have he : a*c+b*s+(b*c-a*s)+b*(c+s) = l*(a+2*b)+m*(1+a*b+b^2) := by
        calc
          _ = l*(a+2*b)+m*((a^2+b^2)+a*b+b^2) := by rw [←hc',←hs']; ring
          _ = _ := by rw [hu]
      rw [he]
      exact hmin
  · have hsector' : b*c ≤ a*s := le_of_not_ge hsector
    rw [abs_of_nonpos (sub_nonpos.mpr hsector')]
    have ha0 : a ≠ 0 := by intro he; subst a; nlinarith
    have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    let l := (a*s-b*c)/a
    let m := c/a
    have hl : 0 ≤ l := div_nonneg (sub_nonneg.mpr hsector') ha
    have hm : 0 ≤ m := div_nonneg hc ha
    have hs' : l+m*b = s := by dsimp [l,m]; field_simp; ring
    have hc' : m*a = c := by dsimp [m]; field_simp
    have hsum := unit_cone_sum b a l m (by linarith) hb1 hl hm
      (by rw [hs',hc']; linarith)
    have hmin := weighted_min (a+2*b) (1+a*b+b^2) l m hx hy hl hm hsum
    have he : a*c+b*s+ -(b*c-a*s)+b*(c+s) = l*(a+2*b)+m*(1+a*b+b^2) := by
      calc
        _ = l*(a+2*b)+m*((a^2+b^2)+a*b+b^2) := by rw [←hc',←hs']; ring
        _ = _ := by rw [hu]
    rw [he]
    exact hmin

def mixedSupportExpr (a b c s : ℝ) : ℝ :=
  |a*c+b*s|+|b*c-a*s|+b*(|c|+|s|)

theorem mixedSupportExpr_quarter_turn (a b c s : ℝ) :
    mixedSupportExpr a b (-s) c = mixedSupportExpr a b c s := by
  have h₁ : a*(-s)+b*c = b*c-a*s := by ring
  have h₂ : b*(-s)-a*c = -(a*c+b*s) := by ring
  simp only [mixedSupportExpr,h₁,h₂,abs_neg]
  ring

theorem mixedSupportExpr_neg (a b c s : ℝ) :
    mixedSupportExpr a b (-c) (-s) = mixedSupportExpr a b c s := by
  have h₁ : a*(-c)+b*(-s) = -(a*c+b*s) := by ring
  have h₂ : b*(-c)-a*(-s) = -(b*c-a*s) := by ring
  simp only [mixedSupportExpr,h₁,h₂,abs_neg]

theorem mixed_support_unit (a b c s : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : a^2+b^2 = 1) (hv : c^2+s^2 = 1) :
    min (a+2*b) (1+a*b+b^2) ≤
      |a*c+b*s|+|b*c-a*s|+b*(|c|+|s|) := by
  change min (a+2*b) (1+a*b+b^2) ≤ mixedSupportExpr a b c s
  by_cases hc : 0 ≤ c
  · by_cases hs : 0 ≤ s
    · exact mixed_support_first_quadrant a b c s ha hb hc hs hu hv
    · have h := mixed_support_first_quadrant a b (-s) c ha hb (by linarith) hc
        hu (by nlinarith)
      change _ ≤ mixedSupportExpr a b (-s) c at h
      rwa [mixedSupportExpr_quarter_turn] at h
  · by_cases hs : 0 ≤ s
    · have h := mixed_support_first_quadrant a b s (-c) ha hb hs (by linarith)
        hu (by nlinarith)
      change _ ≤ mixedSupportExpr a b s (-c) at h
      have he := mixedSupportExpr_quarter_turn a b s (-c)
      simp only [neg_neg] at he
      rwa [←he] at h
    · have h := mixed_support_first_quadrant a b (-c) (-s) ha hb (by linarith)
        (by linarith) hu (by nlinarith)
      change _ ≤ mixedSupportExpr a b (-c) (-s) at h
      rwa [mixedSupportExpr_neg] at h

/-- Only the vertical component of the separating normal needs a sign choice;
horizontal reflection is absorbed algebraically. -/
theorem mixed_support_normal (a b c s : ℝ) (hb : 0 ≤ b)
    (hu : a^2+b^2 = 1) (hv : c^2+s^2 = 1) :
    min (|a|+2*b) (1+|a| * b+b^2) ≤
      |a*c+b*s|+|b*c-a*s|+b*(|c|+|s|) := by
  by_cases ha : 0 ≤ a
  · simpa only [abs_of_nonneg ha] using mixed_support_unit a b c s ha hb hu hv
  · have h := mixed_support_unit (-a) b (-c) s (by linarith) hb (by nlinarith) (by nlinarith)
    have h₁ : (-a)*(-c)+b*s = a*c+b*s := by ring
    have h₂ : b*(-c)-(-a)*s = -(b*c-a*s) := by ring
    simpa only [abs_of_neg (lt_of_not_ge ha),h₁,h₂,abs_neg] using h

end Sq17.WallCapacity
#print axioms Sq17.WallCapacity.mixed_support_first_quadrant

#print axioms Sq17.WallCapacity.mixed_support_unit

#print axioms Sq17.WallCapacity.mixed_support_normal
