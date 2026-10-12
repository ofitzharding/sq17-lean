import Sq17Lean.WallSquareSupport
import Mathlib.Tactic.FieldSimp

/-! Necessity of the finite separating-axis test for actual unit squares.
The support function is linear between successive edge-normal directions. -/
namespace Sq17.WallCapacity

private theorem weighted_negative (l m X Y : ℝ)
    (hl : 0 ≤ l) (hm : 0 ≤ m) (hlm : 0 < l+m)
    (hX : X < 0) (hY : Y < 0) : l*X+m*Y < 0 := by
  have hx := mul_nonpos_of_nonneg_of_nonpos hl hX.le
  have hy := mul_nonpos_of_nonneg_of_nonpos hm hY.le
  by_cases hp : 0 < l
  · have h := mul_neg_of_pos_of_neg hp hX
    linarith
  · have hp' : 0 < m := by linarith
    have h := mul_neg_of_pos_of_neg hp' hY
    linarith

/-- In one quadrant only the two coordinate axes and the other square's
edge normal can maximize the sign of the separation gap. -/
theorem separation_first_quadrant (c s x y dx dy : ℝ)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hu : c^2+s^2=1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : 0 < x+y)
    (hgap : (x+y+((c*x+s*y)+|c*y-s*x|))/2 ≤ x*dx+y*dy) :
    (1+c+s)/2 ≤ dx ∨ (1+c+s)/2 ≤ dy ∨
      (1+c+s)/2 ≤ c*dx+s*dy := by
  by_contra hn
  push_neg at hn
  obtain ⟨hdx,hdy,hcs⟩ := hn
  by_cases hsector : c*y ≤ s*x
  · rw [abs_of_nonpos (sub_nonpos.mpr hsector)] at hgap
    by_cases hs0 : s=0
    · subst s
      have hc1 : c=1 := by nlinarith
      have hy0 : y=0 := by nlinarith
      subst c; subst y
      norm_num at hgap hdx hxy
      nlinarith
    · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
      let l := (s*x-c*y)/s
      let m := y/s
      have hl : 0 ≤ l := div_nonneg (sub_nonneg.mpr hsector) hs
      have hm : 0 ≤ m := div_nonneg hy hs
      have hex : l+m*c=x := by dsimp [l,m]; field_simp; ring
      have hey : m*s=y := by dsimp [m]; field_simp
      have hlm : 0 < l+m := by
        by_contra hh
        have hl0 : l=0 := by linarith
        have hm0 : m=0 := by linarith
        simp [hl0,hm0] at hex hey
        linarith
      have hn := weighted_negative l m (dx-(1+c+s)/2)
        (c*dx+s*dy-(1+c+s)/2) hl hm hlm (by linarith) (by linarith)
      have he : x*dx+y*dy-(x+y+((c*x+s*y)+ -(c*y-s*x)))/2 =
          l*(dx-(1+c+s)/2)+m*(c*dx+s*dy-(1+c+s)/2) := by
        calc
          _ = l*(dx-(1+c+s)/2)+m*(c*dx+s*dy-(1+c+s)/2)
              +m*(1-(c^2+s^2))/2 := by rw [←hex,←hey]; ring
          _ = _ := by rw [hu]; ring
      linarith
  · have hsector' : s*x ≤ c*y := le_of_not_ge hsector
    rw [abs_of_nonneg (sub_nonneg.mpr hsector')] at hgap
    have hc0 : c ≠ 0 := by intro he; subst c; nlinarith
    let l := (c*y-s*x)/c
    let m := x/c
    have hl : 0 ≤ l := div_nonneg (sub_nonneg.mpr hsector') hc
    have hm : 0 ≤ m := div_nonneg hx hc
    have hey : l+m*s=y := by dsimp [l,m]; field_simp; ring
    have hex : m*c=x := by dsimp [m]; field_simp
    have hlm : 0 < l+m := by
      by_contra hh
      have hl0 : l=0 := by linarith
      have hm0 : m=0 := by linarith
      simp [hl0,hm0] at hex hey
      linarith
    have hn := weighted_negative l m (dy-(1+c+s)/2)
      (c*dx+s*dy-(1+c+s)/2) hl hm hlm (by linarith) (by linarith)
    have he : x*dx+y*dy-(x+y+((c*x+s*y)+(c*y-s*x)))/2 =
        l*(dy-(1+c+s)/2)+m*(c*dx+s*dy-(1+c+s)/2) := by
      calc
        _ = l*(dy-(1+c+s)/2)+m*(c*dx+s*dy-(1+c+s)/2)
            +m*(1-(c^2+s^2))/2 := by rw [←hex,←hey]; ring
        _ = _ := by rw [hu]; ring
    linarith

/-- Four unoriented candidate axes, expressed in the first square's frame. -/
def AxisSeparated (c s dx dy : ℝ) : Prop :=
  (1+|c|+|s|)/2 ≤ |dx| ∨ (1+|c|+|s|)/2 ≤ |dy| ∨
  (1+|c|+|s|)/2 ≤ |c*dx+s*dy| ∨ (1+|c|+|s|)/2 ≤ |c*dy-s*dx|

private theorem axes_right_half (c s x y dx dy : ℝ)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hu : c^2+s^2=1)
    (hx : 0 ≤ x) (hxy : 0 < |x|+|y|)
    (hgap : (|x|+|y|)/2+squareSupport c s x y ≤ x*dx+y*dy) :
    AxisSeparated c s dx dy := by
  by_cases hy : 0 ≤ y
  · have hsum : 0 < x+y := by simpa [abs_of_nonneg hx,abs_of_nonneg hy] using hxy
    have hpos : 0 ≤ c*x+s*y := by positivity
    have hg : (x+y+((c*x+s*y)+|c*y-s*x|))/2 ≤ x*dx+y*dy := by
      simpa only [squareSupport, mul_comm x c, mul_comm y s, mul_comm y c,
        mul_comm x s, abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg hpos,
        add_div] using hgap
    rcases separation_first_quadrant c s x y dx dy hc hs hu hx hy hsum hg with h|h|h
    · exact Or.inl (by simpa [abs_of_nonneg hc,abs_of_nonneg hs] using h.trans (le_abs_self dx))
    · exact Or.inr (Or.inl (by simpa [abs_of_nonneg hc,abs_of_nonneg hs] using h.trans (le_abs_self dy)))
    · exact Or.inr (Or.inr (Or.inl (by simpa [abs_of_nonneg hc,abs_of_nonneg hs] using h.trans (le_abs_self (c*dx+s*dy)))))
  · have hy' : y ≤ 0 := le_of_not_ge hy
    have hny : 0 ≤ -y := neg_nonneg.mpr hy'
    have hsum : 0 < x+(-y) := by simpa [abs_of_nonneg hx,abs_of_nonpos hy',sub_eq_add_neg] using hxy
    have hpos : 0 ≤ s*x+c*(-y) := by positivity
    have he1 : x*c+y*s = -(s*(-y)-c*x) := by ring
    have he2 : y*c-x*s = -(s*x+c*(-y)) := by ring
    have hg : (x+(-y)+((s*x+c*(-y))+|s*(-y)-c*x|))/2 ≤ x*dx+(-y)*(-dy) := by
      dsimp [squareSupport] at hgap
      rw [he1,he2,abs_neg,abs_neg,abs_of_nonneg hpos,
        abs_of_nonneg hx,abs_of_nonpos hy'] at hgap
      nlinarith
    rcases separation_first_quadrant s c x (-y) dx (-dy) hs hc (by linarith)
      hx hny hsum hg with h|h|h
    · exact Or.inl (by rw [abs_of_nonneg hc,abs_of_nonneg hs]; linarith [le_abs_self dx])
    · exact Or.inr (Or.inl (by rw [abs_of_nonneg hc,abs_of_nonneg hs]; linarith [neg_le_abs dy]))
    · apply Or.inr ∘ Or.inr ∘ Or.inr
      rw [abs_of_nonneg hc,abs_of_nonneg hs]
      have he : s*dx+c*(-dy) = -(c*dy-s*dx) := by ring
      rw [he] at h
      linarith [neg_le_abs (c*dy-s*dx)]

private theorem abs_neg_sum (a b : ℝ) : |-a + -b| = |a+b| := by
  rw [show -a + -b = -(a+b) by ring,abs_neg]

private theorem abs_neg_difference (a b : ℝ) : |-a - -b| = |a-b| := by
  rw [show -a - -b = -(a-b) by ring,abs_neg]

private theorem axes_nonnegative_orientation (c s x y dx dy : ℝ)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hu : c^2+s^2=1)
    (hxy : 0 < |x|+|y|)
    (hgap : (|x|+|y|)/2+squareSupport c s x y ≤ x*dx+y*dy) :
    AxisSeparated c s dx dy := by
  by_cases hx : 0 ≤ x
  · exact axes_right_half c s x y dx dy hc hs hu hx hxy hgap
  · have h := axes_right_half c s (-x) (-y) (-dx) (-dy) hc hs hu
      (by linarith) (by simpa using hxy) (by simpa only [squareSupport,neg_mul,mul_neg,neg_neg,abs_neg,abs_neg_sum,abs_neg_difference] using hgap)
    simpa only [AxisSeparated,neg_mul,mul_neg,neg_neg,abs_neg,abs_neg_sum,abs_neg_difference] using h

private theorem axes_nonnegative_c (c s x y dx dy : ℝ)
    (hc : 0 ≤ c) (hu : c^2+s^2=1) (hxy : 0 < |x|+|y|)
    (hgap : (|x|+|y|)/2+squareSupport c s x y ≤ x*dx+y*dy) :
    AxisSeparated c s dx dy := by
  by_cases hs : 0 ≤ s
  · exact axes_nonnegative_orientation c s x y dx dy hc hs hu hxy hgap
  · have h := axes_nonnegative_orientation c (-s) x (-y) dx (-dy) hc
      (by linarith) (by nlinarith) (by simpa using hxy)
      (by simpa only [squareSupport,neg_mul,mul_neg,neg_neg,abs_neg,abs_neg_sum,abs_neg_difference] using hgap)
    simpa only [AxisSeparated,neg_mul,mul_neg,neg_neg,abs_neg,abs_neg_sum,abs_neg_difference] using h

/-- An arbitrary separating support normal implies one of four edge axes
separates. This is the algebraic finite-axis necessity theorem. -/
theorem support_implies_axis (c s x y dx dy : ℝ)
    (hu : c^2+s^2=1) (hxy : 0 < |x|+|y|)
    (hgap : (|x|+|y|)/2+squareSupport c s x y ≤ x*dx+y*dy) :
    AxisSeparated c s dx dy := by
  by_cases hc : 0 ≤ c
  · exact axes_nonnegative_c c s x y dx dy hc hu hxy hgap
  · have h := axes_nonnegative_c (-c) (-s) x y dx dy (by linarith)
      (by nlinarith) hxy
      (by simpa only [squareSupport,neg_mul,mul_neg,neg_neg,abs_neg,abs_neg_sum,abs_neg_difference] using hgap)
    simpa only [AxisSeparated,neg_mul,mul_neg,neg_neg,abs_neg,abs_neg_sum,abs_neg_difference] using h

#print axioms separation_first_quadrant
#print axioms support_implies_axis
end Sq17.WallCapacity
