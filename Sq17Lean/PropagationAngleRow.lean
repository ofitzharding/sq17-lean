import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Convert
import Sq17Lean.PropagationGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Endpoint support tests imply containment throughout a closed angle row.
The connected checker restricts row width to at most 1, hence less than pi.
Rational Taylor enclosures of the endpoint values are a separate obligation. -/
namespace Sq17.Propagation

noncomputable def coreD (c s θ : ℝ) : ℝ := c * Real.cos θ + s * Real.sin θ
noncomputable def coreX (c s θ : ℝ) : ℝ := c * Real.sin θ - s * Real.cos θ
noncomputable def rowSupport (c s θ : ℝ) : ℝ := |coreD c s θ| + |coreX c s θ|

/-- A harmonic linear combination cannot become negative between nonnegative
endpoints separated by less than pi. The proof uses positive sine weights. -/
theorem harmonic_nonneg_between (a b lo hi θ : ℝ)
    (horder : lo < hi) (hwidth : hi-lo < Real.pi)
    (hθ : θ ∈ Set.Icc lo hi)
    (hlo : 0 ≤ a*Real.cos lo+b*Real.sin lo)
    (hhi : 0 ≤ a*Real.cos hi+b*Real.sin hi) :
    0 ≤ a*Real.cos θ+b*Real.sin θ := by
  have hden : 0 < Real.sin (hi-lo) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr horder) hwidth
  have hl : 0 ≤ Real.sin (hi-θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hθ.2) (by linarith [hθ.1])
  have hr : 0 ≤ Real.sin (θ-lo) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hθ.1) (by linarith [hθ.2])
  have identity : (a*Real.cos θ+b*Real.sin θ)*Real.sin (hi-lo) =
      (a*Real.cos lo+b*Real.sin lo)*Real.sin (hi-θ) +
      (a*Real.cos hi+b*Real.sin hi)*Real.sin (θ-lo) := by
    simp only [Real.sin_sub]
    ring
  exact nonneg_of_mul_nonneg_left
    (identity.symm ▸ add_nonneg (mul_nonneg hlo hl) (mul_nonneg hhi hr)) hden

theorem hasDerivAt_coreD (c s θ : ℝ) :
    HasDerivAt (coreD c s) (-coreX c s θ) θ := by
  convert ((Real.hasDerivAt_cos θ).const_mul c).add
    ((Real.hasDerivAt_sin θ).const_mul s) using 1
  · rfl
  · simp only [coreX]
    ring

theorem hasDerivAt_coreX (c s θ : ℝ) :
    HasDerivAt (coreX c s) (coreD c s θ) θ := by
  convert ((Real.hasDerivAt_sin θ).const_mul c).sub
    ((Real.hasDerivAt_cos θ).const_mul s) using 1
  · rfl
  · simp only [coreD]
    ring

/-- The endpoint cone checks used in `core_ok` hold throughout a row shorter
than pi. No normalization or exact midpoint assumption on the core is needed. -/
theorem row_cone (c s lo hi : ℝ) (horder : lo < hi)
    (hwidth : hi-lo < Real.pi)
    (hlo : |coreX c s lo| ≤ coreD c s lo)
    (hhi : |coreX c s hi| ≤ coreD c s hi) :
    ∀ θ ∈ Set.Icc lo hi,
      0 ≤ coreD c s θ + coreX c s θ ∧ 0 ≤ coreD c s θ - coreX c s θ := by
  have pl : 0 ≤ coreD c s lo + coreX c s lo := by
    linarith only [hlo, neg_le_abs (coreX c s lo)]
  have ph : 0 ≤ coreD c s hi + coreX c s hi := by
    linarith only [hhi, neg_le_abs (coreX c s hi)]
  have ml : 0 ≤ coreD c s lo - coreX c s lo := by
    linarith only [hlo, le_abs_self (coreX c s lo)]
  have mh : 0 ≤ coreD c s hi - coreX c s hi := by
    linarith only [hhi, le_abs_self (coreX c s hi)]
  have plus (t : ℝ) : coreD c s t + coreX c s t =
      (c-s)*Real.cos t+(c+s)*Real.sin t := by dsimp [coreD, coreX]; ring
  have minus (t : ℝ) : coreD c s t - coreX c s t =
      (c+s)*Real.cos t+(s-c)*Real.sin t := by dsimp [coreD, coreX]; ring
  intro θ hθ
  constructor
  · rw [plus]
    exact harmonic_nonneg_between (c-s) (c+s) lo hi θ horder hwidth hθ
      (by simpa only [plus] using pl) (by simpa only [plus] using ph)
  · rw [minus]
    exact harmonic_nonneg_between (c+s) (s-c) lo hi θ horder hwidth hθ
      (by simpa only [minus] using ml) (by simpa only [minus] using mh)

/-- The actual endpoint cone and support inequalities suffice for the whole
closed row, including its endpoints. This also handles a zero-width row. -/
theorem endpoint_support_row (c s h lo hi : ℝ) (hh : 0 ≤ h)
    (horder : lo ≤ hi) (hwidth : hi-lo < Real.pi)
    (hlo : |coreX c s lo| ≤ coreD c s lo)
    (hhi : |coreX c s hi| ≤ coreD c s hi)
    (hleft : h * rowSupport c s lo ≤ 1)
    (hright : h * rowSupport c s hi ≤ 1) :
    ∀ θ ∈ Set.Icc lo hi, h * rowSupport c s θ ≤ 1 := by
  rcases horder.eq_or_lt with heq | hlt
  · intro θ hθ
    have : θ = lo := by rcases hθ with ⟨h1,h2⟩; linarith
    simpa only [this] using hleft
  have hc := row_cone c s lo hi hlt hwidth hlo hhi
  have hpderiv (θ : ℝ) : HasDerivAt (fun t => coreD c s t + coreX c s t)
      (coreD c s θ - coreX c s θ) θ := by
    convert (hasDerivAt_coreD c s θ).add (hasDerivAt_coreX c s θ) using 1 <;> ring
  have hmderiv (θ : ℝ) : HasDerivAt (fun t => coreD c s t - coreX c s t)
      (-(coreD c s θ + coreX c s θ)) θ := by
    convert (hasDerivAt_coreD c s θ).sub (hasDerivAt_coreX c s θ) using 1 <;> ring
  have hpmono : MonotoneOn (fun t => coreD c s t + coreX c s t) (Set.Icc lo hi) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc lo hi)
      (continuous_iff_continuousAt.mpr (fun θ => (hpderiv θ).continuousAt)).continuousOn
      (fun θ _ => (hpderiv θ).hasDerivWithinAt)
    intro θ hθ
    exact (hc θ (interior_subset hθ)).2
  have hmanti : AntitoneOn (fun t => coreD c s t - coreX c s t) (Set.Icc lo hi) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc lo hi)
      (continuous_iff_continuousAt.mpr (fun θ => (hmderiv θ).continuousAt)).continuousOn
      (fun θ _ => (hmderiv θ).hasDerivWithinAt)
    intro θ hθ
    exact neg_nonpos.mpr (hc θ (interior_subset hθ)).1
  intro θ hθ
  have hp := hpmono hθ ⟨hlt.le,le_refl hi⟩ hθ.2
  have hm := hmanti ⟨le_refl lo,hlt.le⟩ hθ hθ.1
  have ep : coreD c s hi + coreX c s hi ≤ rowSupport c s hi :=
    add_le_add (le_abs_self _) (le_abs_self _)
  have em : coreD c s lo - coreX c s lo ≤ rowSupport c s lo := by
    exact add_le_add (le_abs_self _) (neg_le_abs _)
  have bp := (mul_le_mul_of_nonneg_left (hp.trans ep) hh).trans hright
  have bm := (mul_le_mul_of_nonneg_left (hm.trans em) hh).trans hleft
  have hd : 0 ≤ coreD c s θ := by
    have hcone := hc θ hθ
    linarith only [hcone.1, hcone.2]
  by_cases hx : 0 ≤ coreX c s θ
  · simpa only [rowSupport, abs_of_nonneg hd, abs_of_nonneg hx] using bp
  · simpa only [rowSupport, abs_of_nonneg hd, abs_of_nonpos (le_of_not_ge hx),
      sub_eq_add_neg] using bm

/-- Composition with the project's real square definition. -/
theorem endpoint_core_contained (cx cy c s h lo hi : ℝ) (hh : 0 ≤ h)
    (horder : lo ≤ hi) (hwidth : hi-lo ≤ 1)
    (hlo : |coreX c s lo| ≤ coreD c s lo)
    (hhi : |coreX c s hi| ≤ coreD c s hi)
    (hleft : h * rowSupport c s lo ≤ 1)
    (hright : h * rowSupport c s hi ≤ 1) :
    ∀ θ ∈ Set.Icc lo hi, core cx cy c s h ⊆
      Sq17.sq cx cy (Real.cos θ) (Real.sin θ) := by
  apply row_core_contained cx cy c s h lo hi hh
  exact endpoint_support_row c s h lo hi hh horder
    (by linarith [Real.pi_gt_three]) hlo hhi hleft hright

end Sq17.Propagation

#print axioms Sq17.Propagation.endpoint_support_row
#print axioms Sq17.Propagation.endpoint_core_contained
