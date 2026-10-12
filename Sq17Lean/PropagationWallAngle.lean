import Sq17Lean.PropagationWall
import Sq17Lean.PropagationWallSupport

/-! Angle-dependent necessary wall bounds from checked endpoint enclosures.
The coefficients select points of the actual unit square, rather than a
shrunken inner core. Closed row endpoints and legal wall contact are preserved. -/
namespace Sq17.Propagation

theorem square_center_signed_bounds (cx cy θ a b L : ℝ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hfit : Sq17.sq cx cy (Real.cos θ) (Real.sin θ) ⊆ containerBox L) :
    (a*Real.cos θ+b*Real.sin θ)/2 ≤ cx ∧
    cx ≤ L-(a*Real.cos θ+b*Real.sin θ)/2 ∧
    (a*Real.cos θ+b*Real.sin θ)/2 ≤ cy ∧
    cy ≤ L-(a*Real.cos θ+b*Real.sin θ)/2 := by
  have hsum : Real.cos θ*Real.cos θ+Real.sin θ*Real.sin θ = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hcross : Real.cos θ*Real.sin θ-Real.sin θ*Real.cos θ = 0 := by ring
  have hsupport : 1*(|Real.cos θ*Real.cos θ+Real.sin θ*Real.sin θ|+
      |Real.cos θ*Real.sin θ-Real.sin θ*Real.cos θ|) ≤ 1 := by
    rw [hsum, hcross]
    norm_num
  have hpoint (u v : ℝ) (hu : |u| ≤ 1) (hv : |v| ≤ 1) :
      corePoint cx cy (Real.cos θ) (Real.sin θ) 1 u v ∈ containerBox L :=
    hfit (corePoint_mem_sq cx cy (Real.cos θ) (Real.sin θ) 1 u v
      (Real.cos θ) (Real.sin θ) (by norm_num) hu hv hsupport)
  have hl := hpoint (-a) b (by simpa using ha) hb
  have hr := hpoint a (-b) ha (by simpa using hb)
  have hd := hpoint (-b) (-a) (by simpa using hb) (by simpa using ha)
  have ht := hpoint b a hb ha
  change 0 ≤ (corePoint cx cy (Real.cos θ) (Real.sin θ) 1 (-a) b).1 ∧ _ at hl
  change _ ∧ (corePoint cx cy (Real.cos θ) (Real.sin θ) 1 a (-b)).1 ≤ L ∧ _ at hr
  change _ ∧ _ ∧ 0 ≤ (corePoint cx cy (Real.cos θ) (Real.sin θ) 1 (-b) (-a)).2 ∧ _ at hd
  change _ ∧ _ ∧ _ ∧ (corePoint cx cy (Real.cos θ) (Real.sin θ) 1 b a).2 ≤ L at ht
  dsimp [corePoint] at hl hr hd ht
  exact ⟨by linarith [hl.1], by linarith [hr.2.1],
    by linarith [hd.2.2.1], by linarith [ht.2.2.2]⟩

structure WallRowCertificate where
  lo : ℚ
  hi : ℚ
  a : ℚ
  b : ℚ
  span : ℚ
  left : TrigBounds
  right : TrigBounds

def WallRowCertificate.check (r : WallRowCertificate) (n : ℕ) : Bool :=
  r.left.check n r.lo && r.right.check n r.hi && decide
    (|r.a| ≤ 1 ∧ |r.b| ≤ 1 ∧ 0 ≤ r.span ∧ r.lo ≤ r.hi ∧ r.hi-r.lo ≤ 1 ∧
      r.span ≤ (r.left.endpoint r.a r.b).dLo ∧
      r.span ≤ (r.right.endpoint r.a r.b).dLo)

theorem WallRowCertificate.span_sound (r : WallRowCertificate) (n : ℕ)
    (hc : r.check n = true) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (r.lo : ℝ) (r.hi : ℝ)) :
    (r.span : ℝ) ≤ (r.a : ℝ)*Real.cos θ+(r.b : ℝ)*Real.sin θ := by
  simp only [WallRowCertificate.check, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨hl,hr⟩,ha,hb,hd,horder,hwidth,hleft,hright⟩
  have hlower := (r.left.endpoint_sound n r.lo r.a r.b hl).1
  have hupper := (r.right.endpoint_sound n r.hi r.a r.b hr).1
  have hd' : 0 ≤ (r.span : ℝ) := by exact_mod_cast hd
  have horder' : (r.lo : ℝ) ≤ r.hi := by exact_mod_cast horder
  have hwidth' : (r.hi : ℝ)-r.lo ≤ 1 := by exact_mod_cast hwidth
  have hleft' : (r.span : ℝ) ≤ (r.left.endpoint r.a r.b).dLo := by exact_mod_cast hleft
  have hright' : (r.span : ℝ) ≤ (r.right.endpoint r.a r.b).dLo := by exact_mod_cast hright
  exact harmonic_lower_between r.a r.b r.span r.lo r.hi θ hd' horder'
    (by linarith [Real.pi_gt_three]) hθ (hleft'.trans hlower) (hright'.trans hupper)

theorem WallRowCertificate.center_bounds (r : WallRowCertificate) (n : ℕ)
    (hc : r.check n = true) (cx cy θ L : ℝ)
    (hθ : θ ∈ Set.Icc (r.lo : ℝ) (r.hi : ℝ))
    (hfit : Sq17.sq cx cy (Real.cos θ) (Real.sin θ) ⊆ containerBox L) :
    (r.span : ℝ)/2 ≤ cx ∧ cx ≤ L-(r.span : ℝ)/2 ∧
    (r.span : ℝ)/2 ≤ cy ∧ cy ≤ L-(r.span : ℝ)/2 := by
  have hs := r.span_sound n hc θ hθ
  have hb := hc
  simp only [WallRowCertificate.check, Bool.and_eq_true, decide_eq_true_eq] at hb
  have ha : |(r.a : ℝ)| ≤ 1 := by exact_mod_cast hb.2.1
  have hb' : |(r.b : ℝ)| ≤ 1 := by exact_mod_cast hb.2.2.1
  have h := square_center_signed_bounds cx cy θ r.a r.b L ha hb' hfit
  exact ⟨by linarith [h.1], by linarith [h.2.1],
    by linarith [h.2.2.1], by linarith [h.2.2.2]⟩

def rationalAngleWallCheck (V : List (ℚ × ℚ)) (r : WallRowCertificate)
    (L : ℚ) (n : ℕ) : Bool :=
  r.check n && (rationalHalfPlane V (-1) 0 (-(r.span/2)) ||
    rationalHalfPlane V 1 0 (L-r.span/2) ||
    rationalHalfPlane V 0 (-1) (-(r.span/2)) ||
    rationalHalfPlane V 0 1 (L-r.span/2))

theorem rationalAngleWallCheck_sound (V : List (ℚ × ℚ)) (r : WallRowCertificate)
    (L : ℚ) (n : ℕ) (hc : rationalAngleWallCheck V r L n = true)
    (x : ℝ × ℝ) (hx : x ∈ convexHull ℝ (realPoint '' {p | p ∈ V}))
    (θ : ℝ) (hθ : θ ∈ Set.Icc (r.lo : ℝ) (r.hi : ℝ)) :
    ¬ Sq17.sq x.1 x.2 (Real.cos θ) (Real.sin θ) ⊆ containerBox L := by
  intro hfit
  have hb := Bool.and_eq_true_iff.mp hc
  have bounds := r.center_bounds n hb.1 x.1 x.2 θ L hθ hfit
  have hw : rationalHalfPlane V (-1) 0 (-(r.span/2)) = true ∨
      rationalHalfPlane V 1 0 (L-r.span/2) = true ∨
      rationalHalfPlane V 0 (-1) (-(r.span/2)) = true ∨
      rationalHalfPlane V 0 1 (L-r.span/2) = true := by
    simpa only [Bool.or_eq_true, or_assoc] using hb.2
  rcases hw with hw | hw | hw | hw
  all_goals
    have hv := rationalHalfPlane_sound _ _ _ _ hw x hx
    push_cast at hv
    norm_num at hv
    linarith

end Sq17.Propagation

#print axioms Sq17.Propagation.square_center_signed_bounds
#print axioms Sq17.Propagation.WallRowCertificate.span_sound
#print axioms Sq17.Propagation.WallRowCertificate.center_bounds
#print axioms Sq17.Propagation.rationalAngleWallCheck_sound
