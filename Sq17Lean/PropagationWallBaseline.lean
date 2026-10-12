import Sq17Lean.PropagationWallAngle

/-! Every actual unit square has coordinate width at least one. Combining this
baseline with a checked angle-row span strengthens wall bounds, including in
the translated container `[-d, S+d]²`. All wall-contact inequalities are closed. -/
namespace Sq17.Propagation

theorem abs_cos_add_abs_sin_ge_one (θ : ℝ) :
    1 ≤ |Real.cos θ| + |Real.sin θ| := by
  have hc := abs_nonneg (Real.cos θ)
  have hs := abs_nonneg (Real.sin θ)
  have hprod := mul_nonneg hc hs
  have hunit := Real.sin_sq_add_cos_sq θ
  have hc2 := sq_abs (Real.cos θ)
  have hs2 := sq_abs (Real.sin θ)
  nlinarith

theorem square_center_baseline_bounds (cx cy θ L : ℝ)
    (hfit : Sq17.sq cx cy (Real.cos θ) (Real.sin θ) ⊆ containerBox L) :
    1/2 ≤ cx ∧ cx ≤ L-1/2 ∧ 1/2 ≤ cy ∧ cy ≤ L-1/2 := by
  let a : ℝ := if 0 ≤ Real.cos θ then 1 else -1
  let b : ℝ := if 0 ≤ Real.sin θ then 1 else -1
  have ha : |a| ≤ 1 := by dsimp [a]; split <;> norm_num
  have hb : |b| ≤ 1 := by dsimp [b]; split <;> norm_num
  have hac : a * Real.cos θ = |Real.cos θ| := by
    dsimp [a]
    split <;> rename_i h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  have hbs : b * Real.sin θ = |Real.sin θ| := by
    dsimp [b]
    split <;> rename_i h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  have h := square_center_signed_bounds cx cy θ a b L ha hb hfit
  rw [hac, hbs] at h
  have hwidth := abs_cos_add_abs_sin_ge_one θ
  exact ⟨by linarith [h.1], by linarith [h.2.1],
    by linarith [h.2.2.1], by linarith [h.2.2.2]⟩

theorem WallRowCertificate.center_bounds_max (r : WallRowCertificate) (n : ℕ)
    (hc : r.check n = true) (cx cy θ L : ℝ)
    (hθ : θ ∈ Set.Icc (r.lo : ℝ) (r.hi : ℝ))
    (hfit : Sq17.sq cx cy (Real.cos θ) (Real.sin θ) ⊆ containerBox L) :
    max 1 (r.span : ℝ)/2 ≤ cx ∧ cx ≤ L-max 1 (r.span : ℝ)/2 ∧
    max 1 (r.span : ℝ)/2 ≤ cy ∧ cy ≤ L-max 1 (r.span : ℝ)/2 := by
  by_cases hs : (r.span : ℝ) ≤ 1
  · simpa only [max_eq_left hs] using square_center_baseline_bounds cx cy θ L hfit
  · simpa only [max_eq_right (le_of_not_ge hs)] using
      r.center_bounds n hc cx cy θ L hθ hfit

/-- Reject a polygon lying strictly beyond a necessary wall bound. The unit
width baseline remains available even when the checked row span is smaller. -/
def rationalStrongWallCheck (V : List (ℚ × ℚ)) (r : WallRowCertificate)
    (L : ℚ) (n : ℕ) : Bool :=
  r.check n && (rationalHalfPlane V (-1) 0 (-(max 1 r.span/2)) ||
    rationalHalfPlane V 1 0 (L-max 1 r.span/2) ||
    rationalHalfPlane V 0 (-1) (-(max 1 r.span/2)) ||
    rationalHalfPlane V 0 1 (L-max 1 r.span/2))

theorem rationalStrongWallCheck_sound (V : List (ℚ × ℚ)) (r : WallRowCertificate)
    (L : ℚ) (n : ℕ) (hc : rationalStrongWallCheck V r L n = true)
    (x : ℝ × ℝ) (hx : x ∈ convexHull ℝ (realPoint '' {p | p ∈ V}))
    (θ : ℝ) (hθ : θ ∈ Set.Icc (r.lo : ℝ) (r.hi : ℝ)) :
    ¬ Sq17.sq x.1 x.2 (Real.cos θ) (Real.sin θ) ⊆ containerBox L := by
  intro hfit
  have hb := Bool.and_eq_true_iff.mp hc
  have bounds := r.center_bounds_max n hb.1 x.1 x.2 θ L hθ hfit
  have hw : rationalHalfPlane V (-1) 0 (-(max 1 r.span/2)) = true ∨
      rationalHalfPlane V 1 0 (L-max 1 r.span/2) = true ∨
      rationalHalfPlane V 0 (-1) (-(max 1 r.span/2)) = true ∨
      rationalHalfPlane V 0 1 (L-max 1 r.span/2) = true := by
    simpa only [Bool.or_eq_true, or_assoc] using hb.2
  rcases hw with hw | hw | hw | hw
  all_goals
    have hv := rationalHalfPlane_sound _ _ _ _ hw x hx
    push_cast at hv
    norm_num at hv
    linarith

/-- Translation of both the square and its enclosing frame by `(d,d)`. -/
theorem square_fit_translate (cx cy ux uy S d : ℝ)
    (hfit : Sq17.sq cx cy ux uy ⊆
      {p | -d ≤ p.1 ∧ p.1 ≤ S+d ∧ -d ≤ p.2 ∧ p.2 ≤ S+d}) :
    Sq17.sq (cx+d) (cy+d) ux uy ⊆ containerBox (S+2*d) := by
  intro p hp
  have hp' : (p.1-d, p.2-d) ∈ Sq17.sq cx cy ux uy := by
    change |((p.1-d)-cx)*ux+((p.2-d)-cy)*uy| ≤ 1/2 ∧
      |((p.2-d)-cy)*ux-((p.1-d)-cx)*uy| ≤ 1/2
    have hx : (p.1-d)-cx = p.1-(cx+d) := by ring
    have hy : (p.2-d)-cy = p.2-(cy+d) := by ring
    rw [hx, hy]
    exact hp
  have h := hfit hp'
  change -d ≤ p.1-d ∧ p.1-d ≤ S+d ∧ -d ≤ p.2-d ∧ p.2-d ≤ S+d at h
  change 0 ≤ p.1 ∧ p.1 ≤ S+2*d ∧ 0 ≤ p.2 ∧ p.2 ≤ S+2*d
  exact ⟨by linarith [h.1], by linarith [h.2.1],
    by linarith [h.2.2.1], by linarith [h.2.2.2]⟩

theorem WallRowCertificate.center_bounds_max_translated (r : WallRowCertificate) (n : ℕ)
    (hc : r.check n = true) (cx cy θ S d : ℝ)
    (hθ : θ ∈ Set.Icc (r.lo : ℝ) (r.hi : ℝ))
    (hfit : Sq17.sq cx cy (Real.cos θ) (Real.sin θ) ⊆
      {p | -d ≤ p.1 ∧ p.1 ≤ S+d ∧ -d ≤ p.2 ∧ p.2 ≤ S+d}) :
    max 1 (r.span : ℝ)/2-d ≤ cx ∧ cx ≤ S+d-max 1 (r.span : ℝ)/2 ∧
    max 1 (r.span : ℝ)/2-d ≤ cy ∧ cy ≤ S+d-max 1 (r.span : ℝ)/2 := by
  have h := r.center_bounds_max n hc (cx+d) (cy+d) θ (S+2*d) hθ
    (square_fit_translate cx cy (Real.cos θ) (Real.sin θ) S d hfit)
  exact ⟨by linarith [h.1], by linarith [h.2.1],
    by linarith [h.2.2.1], by linarith [h.2.2.2]⟩

end Sq17.Propagation

#print axioms Sq17.Propagation.abs_cos_add_abs_sin_ge_one
#print axioms Sq17.Propagation.square_center_baseline_bounds
#print axioms Sq17.Propagation.WallRowCertificate.center_bounds_max
#print axioms Sq17.Propagation.rationalStrongWallCheck_sound
#print axioms Sq17.Propagation.square_fit_translate
#print axioms Sq17.Propagation.WallRowCertificate.center_bounds_max_translated
