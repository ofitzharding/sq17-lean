import Sq17Lean.LocalRigidityGapGeometry

/-! A fixed corner witnessing a strictly negative base gap remains a
witness throughout a sufficiently small perturbation. Used to reject the
unwanted directed axes before selecting the contact rows. -/
namespace Sq17.LocalRigidity

private theorem trig_projection_bound (a b θ : ℝ) :
    |a*Real.cos θ+b*Real.sin θ| ≤ |a|+|b| := by
  have hc := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) (abs_nonneg a)
  have hs := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) (abs_nonneg b)
  have h := abs_add_le (a*Real.cos θ) (b*Real.sin θ)
  rw [abs_mul,abs_mul] at h
  nlinarith

theorem rotatingCornerGap_first_bound (α ω A B C D β ν e f q : ℝ)
    (hq : 0 ≤ q) (hω : |ω| ≤ q) (hν : |ν| ≤ q)
    (hA : |A| ≤ 10) (hB : |B| ≤ 10)
    (hC : |C| ≤ 2*q) (hD : |D| ≤ 2*q)
    (he : |e| ≤ 1/2) (hf : |f| ≤ 1/2) :
    |deriv (rotatingCornerGap α ω A B C D β ν e f) 0| ≤ 26*q := by
  let T := C*Real.cos α+D*Real.sin α
  let τ := -A*Real.sin α+B*Real.cos α
  let P := e*Real.sin (β-α)+f*Real.cos (β-α)
  have hT : |T| ≤ 4*q := by
    have h := trig_projection_bound C D α
    dsimp [T]; linarith
  have hτ : |τ| ≤ 20 := by
    have h := trig_projection_bound B (-A) α
    have heq : B*Real.cos α+(-A)*Real.sin α = τ := by dsimp [τ]; ring
    rw [heq,abs_neg] at h
    linarith
  have hP : |P| ≤ 1 := by
    have h := trig_projection_bound f e (β-α)
    have heq : f*Real.cos (β-α)+e*Real.sin (β-α) = P := by dsimp [P]; ring
    rw [heq] at h
    linarith
  have hτP : |τ-P| ≤ 21 := by
    have h := abs_sub_le τ 0 P
    simp only [sub_zero,zero_sub,abs_neg] at h
    linarith
  have h1 := mul_le_mul hω hτP (abs_nonneg _) hq
  have h2 := mul_le_mul hν hP (abs_nonneg _) hq
  rw [rotatingCornerGap_deriv_zero]
  change |T+ω*(τ-P)+ν*P| ≤ _
  calc
    _ ≤ |T+ω*(τ-P)|+|ν*P| := abs_add_le _ _
    _ ≤ (|T|+|ω*(τ-P)|)+|ν*P| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ 26*q := by rw [abs_mul,abs_mul]; linarith

/-- A finite strictly-negative base-corner certificate can exclude a
candidate axis uniformly. The proof derives its perturbation budget from
actual first/second derivatives of the moving-corner expression. -/
theorem rotatingCornerGap_stays_negative (α ω A B C D β ν e f q margin : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/2) (hω : |ω| ≤ q) (hν : |ν| ≤ q)
    (hA : |A| ≤ 10) (hB : |B| ≤ 10)
    (hC : |C| ≤ 2*q) (hD : |D| ≤ 2*q)
    (he : |e| ≤ 1/2) (hf : |f| ≤ 1/2)
    (hbase : rotatingCornerGap α ω A B C D β ν e f 0 ≤ -margin)
    (hmargin : 51*q < margin) :
    rotatingCornerGap α ω A B C D β ν e f 1 < 0 := by
  have hdiff : ContDiff ℝ 2 (rotatingCornerGap α ω A B C D β ν e f) := by
    rw [rotatingCornerGap_eq]
    exact rotatingGap_contDiff ..
  have hsecond : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      iteratedDeriv 2 (rotatingCornerGap α ω A B C D β ν e f) t ≤ 100*q^2 := by
    intro t ht
    exact (le_abs_self _).trans (rotatingCornerGap_curvature α ω A B C D β ν e f t q
      hq0 hq (by rw [abs_of_pos ht.1]; exact ht.2.le) hω hν hA hB hC hD he hf)
  have hu := segment_taylor_upper _ (100*q^2) hdiff hsecond
  have hl := rotatingCornerGap_first_bound α ω A B C D β ν e f q hq0 hω hν hA hB hC hD he hf
  have hd := le_abs_self (deriv (rotatingCornerGap α ω A B C D β ν e f) 0)
  have hs : q^2 ≤ q/2 := by nlinarith
  nlinarith

#print axioms rotatingCornerGap_first_bound
#print axioms rotatingCornerGap_stays_negative
end Sq17.LocalRigidity
