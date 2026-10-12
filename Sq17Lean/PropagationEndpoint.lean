import Sq17Lean.PropagationAngleRow

/-! Executable rational endpoint checks, with real square containment.
The supplied D/X intervals must still be established by certified trigonometric
enclosures. This module proves the checker's implication from those intervals. -/
namespace Sq17.Propagation

structure EndpointBounds where
  dLo : ℚ
  dHi : ℚ
  xLo : ℚ
  xHi : ℚ

def EndpointBounds.Holds (b : EndpointBounds) (D X : ℝ) : Prop :=
  (b.dLo : ℝ) ≤ D ∧ D ≤ b.dHi ∧ (b.xLo : ℝ) ≤ X ∧ X ≤ b.xHi

theorem mul_interval (a lo hi x : ℝ) (hx : lo ≤ x ∧ x ≤ hi) :
    min (a*lo) (a*hi) ≤ a*x ∧ a*x ≤ max (a*lo) (a*hi) := by
  by_cases ha : 0 ≤ a
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hx.1 ha),
      (mul_le_mul_of_nonneg_left hx.2 ha).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hx.2 (le_of_not_ge ha)),
      (mul_le_mul_of_nonpos_left hx.1 (le_of_not_ge ha)).trans (le_max_left _ _)⟩

/-- The exact signed interval arithmetic used by the endpoint checker. -/
def trigEndpointBounds (c s cl ch sl sh : ℚ) : EndpointBounds where
  dLo := min (c*cl) (c*ch) + min (s*sl) (s*sh)
  dHi := max (c*cl) (c*ch) + max (s*sl) (s*sh)
  xLo := min (c*sl) (c*sh) + min ((-s)*cl) ((-s)*ch)
  xHi := max (c*sl) (c*sh) + max ((-s)*cl) ((-s)*ch)

theorem trigEndpointBounds_sound (c s cl ch sl sh : ℚ) (θ : ℝ)
    (hc : (cl : ℝ) ≤ Real.cos θ ∧ Real.cos θ ≤ ch)
    (hs : (sl : ℝ) ≤ Real.sin θ ∧ Real.sin θ ≤ sh) :
    (trigEndpointBounds c s cl ch sl sh).Holds (coreD c s θ) (coreX c s θ) := by
  have d1 := mul_interval c cl ch (Real.cos θ) hc
  have d2 := mul_interval s sl sh (Real.sin θ) hs
  have x1 := mul_interval c sl sh (Real.sin θ) hs
  have x2 := mul_interval (-(s : ℝ)) cl ch (Real.cos θ) hc
  dsimp [EndpointBounds.Holds, trigEndpointBounds, coreD, coreX]
  push_cast
  simpa only [sub_eq_add_neg, neg_mul] using
    And.intro (add_le_add d1.1 d2.1) (And.intro (add_le_add d1.2 d2.2)
      (And.intro (add_le_add x1.1 x2.1) (add_le_add x1.2 x2.2)))

def rationalEndpointCheck (h : ℚ) (b : EndpointBounds) : Bool :=
  decide (0 ≤ h ∧ 0 < b.dLo ∧ b.dLo ≤ b.dHi ∧ b.xLo ≤ b.xHi ∧
    max |b.xLo| |b.xHi| ≤ b.dLo ∧ h * (b.dHi + max |b.xLo| |b.xHi|) ≤ 1)

theorem rationalEndpointCheck_sound (h : ℚ) (b : EndpointBounds) (D X : ℝ)
    (hc : rationalEndpointCheck h b = true) (hb : b.Holds D X) :
    0 ≤ (h : ℝ) ∧ |X| ≤ D ∧ (h : ℝ) * (|D| + |X|) ≤ 1 := by
  have hq : 0 ≤ h ∧ 0 < b.dLo ∧ b.dLo ≤ b.dHi ∧ b.xLo ≤ b.xHi ∧
      max |b.xLo| |b.xHi| ≤ b.dLo ∧ h * (b.dHi + max |b.xLo| |b.xHi|) ≤ 1 := by
    simpa only [rationalEndpointCheck, decide_eq_true_eq] using hc
  have hr : 0 ≤ (h : ℝ) ∧ 0 < (b.dLo : ℝ) ∧ (b.dLo : ℝ) ≤ b.dHi ∧
      (b.xLo : ℝ) ≤ b.xHi ∧ max |(b.xLo : ℝ)| |(b.xHi : ℝ)| ≤ b.dLo ∧
      (h : ℝ) * ((b.dHi : ℝ) + max |(b.xLo : ℝ)| |(b.xHi : ℝ)|) ≤ 1 := by
    exact_mod_cast hq
  rcases hb with ⟨hdl,hdh,hxl,hxh⟩
  have hx : |X| ≤ max |(b.xLo : ℝ)| |(b.xHi : ℝ)| := by
    apply abs_le.mpr
    exact ⟨(abs_le.mp (le_max_left |(b.xLo : ℝ)| |(b.xHi : ℝ)|)).1.trans hxl,
      hxh.trans (abs_le.mp (le_max_right |(b.xLo : ℝ)| |(b.xHi : ℝ)|)).2⟩
  refine ⟨hr.1, hx.trans (hr.2.2.2.2.1.trans hdl), ?_⟩
  rw [abs_of_pos (hr.2.1.trans_le hdl)]
  exact (mul_le_mul_of_nonneg_left (add_le_add hdh hx) hr.1).trans hr.2.2.2.2.2

def rationalAngleRowCheck (h lo hi : ℚ) (left right : EndpointBounds) : Bool :=
  decide (0 ≤ hi-lo ∧ hi-lo ≤ 1) &&
    (rationalEndpointCheck h left && rationalEndpointCheck h right)

/-- Accepted rational endpoint tests imply real core containment throughout
the row, provided the two D/X enclosures are correct. This replaces an
interval-wide geometric premise by four scalar bounds at each endpoint. -/
theorem rationalAngleRowCheck_sound (cx cy : ℝ) (c s h lo hi : ℚ)
    (left right : EndpointBounds)
    (hc : rationalAngleRowCheck h lo hi left right = true)
    (hl : left.Holds (coreD c s lo) (coreX c s lo))
    (hr : right.Holds (coreD c s hi) (coreX c s hi)) :
    ∀ θ ∈ Set.Icc (lo : ℝ) (hi : ℝ), core cx cy c s h ⊆
      Sq17.sq cx cy (Real.cos θ) (Real.sin θ) := by
  have hc' : decide (0 ≤ hi-lo ∧ hi-lo ≤ 1) = true ∧
      rationalEndpointCheck h left = true ∧ rationalEndpointCheck h right = true := by
    simpa only [rationalAngleRowCheck, Bool.and_eq_true_iff] using hc
  have hq : 0 ≤ hi-lo ∧ hi-lo ≤ 1 := of_decide_eq_true hc'.1
  have hw : (0 : ℝ) ≤ (hi : ℝ)-(lo : ℝ) ∧ (hi : ℝ)-(lo : ℝ) ≤ 1 := by
    exact_mod_cast hq
  have hleft := rationalEndpointCheck_sound h left _ _ hc'.2.1 hl
  have hright := rationalEndpointCheck_sound h right _ _ hc'.2.2 hr
  exact endpoint_core_contained cx cy c s h lo hi hleft.1 (sub_nonneg.mp hw.1)
    hw.2 hleft.2.1 hright.2.1 hleft.2.2 hright.2.2

-- Acceptance at a tight support bound; rejection of an oversized core and
-- rejection of an endpoint outside the permitted support cone.
example : rationalEndpointCheck 1 ⟨1,1,0,0⟩ = true := by
  norm_num [rationalEndpointCheck]
example : rationalEndpointCheck (101/100) ⟨1,1,0,0⟩ = false := by
  norm_num [rationalEndpointCheck]
example : rationalEndpointCheck (1/10) ⟨1,1,2,2⟩ = false := by
  norm_num [rationalEndpointCheck]

end Sq17.Propagation

#print axioms Sq17.Propagation.rationalEndpointCheck_sound
#print axioms Sq17.Propagation.rationalAngleRowCheck_sound
#print axioms Sq17.Propagation.trigEndpointBounds_sound
