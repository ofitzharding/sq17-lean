import Sq17Lean.PropagationAngleRow

/-! Endpoint lower bounds for a harmonic function throughout a short row.
This supplies the analytic ingredient for stronger angle-dependent wall cuts. -/
namespace Sq17.Propagation

/-- A nonnegative common endpoint lower bound persists throughout an interval
shorter than pi. No assumption about the signs of sine or cosine is needed. -/
theorem harmonic_lower_between (a b d lo hi θ : ℝ)
    (hd : 0 ≤ d) (horder : lo ≤ hi) (hwidth : hi-lo < Real.pi)
    (hθ : θ ∈ Set.Icc lo hi)
    (hlo : d ≤ a*Real.cos lo+b*Real.sin lo)
    (hhi : d ≤ a*Real.cos hi+b*Real.sin hi) :
    d ≤ a*Real.cos θ+b*Real.sin θ := by
  rcases horder.eq_or_lt with heq | hlt
  · have ht : θ = lo := by rcases hθ with ⟨h1,h2⟩; linarith
    simpa only [ht] using hlo
  have hden : 0 < Real.sin (hi-lo) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hlt) hwidth
  have hl : 0 ≤ Real.sin (hi-θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hθ.2) (by linarith [hθ.1])
  have hr : 0 ≤ Real.sin (θ-lo) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hθ.1) (by linarith [hθ.2])
  have hweights : Real.sin (hi-lo) ≤ Real.sin (hi-θ)+Real.sin (θ-lo) := by
    have h1 := mul_le_mul_of_nonneg_left (Real.cos_le_one (θ-lo)) hl
    have h2 := mul_le_mul_of_nonneg_right (Real.cos_le_one (hi-θ)) hr
    have heq : hi-lo = (hi-θ)+(θ-lo) := by ring
    rw [heq, Real.sin_add]
    nlinarith
  have identity : (a*Real.cos θ+b*Real.sin θ)*Real.sin (hi-lo) =
      (a*Real.cos lo+b*Real.sin lo)*Real.sin (hi-θ) +
      (a*Real.cos hi+b*Real.sin hi)*Real.sin (θ-lo) := by
    simp only [Real.sin_sub]
    ring
  have hle : d*Real.sin (hi-lo) ≤
      (a*Real.cos θ+b*Real.sin θ)*Real.sin (hi-lo) := by
    rw [identity]
    calc
      _ ≤ d*(Real.sin (hi-θ)+Real.sin (θ-lo)) :=
        mul_le_mul_of_nonneg_left hweights hd
      _ = d*Real.sin (hi-θ)+d*Real.sin (θ-lo) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hlo hl)
        (mul_le_mul_of_nonneg_right hhi hr)
  by_contra h
  have hlt := mul_lt_mul_of_pos_right (lt_of_not_ge h) hden
  linarith

end Sq17.Propagation

#print axioms Sq17.Propagation.harmonic_lower_between
