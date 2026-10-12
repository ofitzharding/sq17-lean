import Sq17Lean.EndpointRoot

/-! A sharper enclosure of the SAME canonical endpoint root.

`EndpointRoot.coordinates` is known to lie within `radius = 10⁻¹²` of `midpoint`.
Its normalised position `q = (coordinates - midpoint)/radius` lies in the unit box
and, because both endpoint polynomials vanish there, the Newton identities make
`q` a fixed point of the normalised Newton map: `eval newton_k q = q_k`. The
coefficient-mass bound then gives `|q_k| ≤ mass newton_k`, far below 1.

No second root is introduced and existence/uniqueness is not re-proved. -/
namespace Sq17.EndpointRoot
open Sq17.PolynomialBox

theorem mass_newton0_le : mass newton0 ≤ 1/10000000 := by decide +kernel
theorem mass_newton1_le : mass newton1 ≤ 1/10000000 := by decide +kernel

/-- The canonical root is within `radius * mass newton_k` of the midpoint. -/
theorem coordinates_sharp :
    |coordinates.1 - (midpoint.1:ℝ)| ≤ (radius:ℝ) * (mass newton0 : ℝ) ∧
    |coordinates.2 - (midpoint.2:ℝ)| ≤ (radius:ℝ) * (mass newton1 : ℝ) := by
  obtain ⟨hbox, hf, hg⟩ := coordinates_spec
  have hr : (0:ℝ) < (radius:ℝ) := radius_pos
  have hr0 : (radius:ℝ) ≠ 0 := ne_of_gt hr
  have hb1 : |coordinates.1 - (midpoint.1:ℝ)| ≤ (radius:ℝ) := hbox.1
  have hb2 : |coordinates.2 - (midpoint.2:ℝ)| ≤ (radius:ℝ) := hbox.2
  let q : ℝ × ℝ := ((coordinates.1 - (midpoint.1:ℝ))/(radius:ℝ),
    (coordinates.2 - (midpoint.2:ℝ))/(radius:ℝ))
  have hT : ((midpoint.1:ℝ)+(radius:ℝ)*q.1, (midpoint.2:ℝ)+(radius:ℝ)*q.2) = coordinates := by
    ext
    · show (midpoint.1:ℝ)+(radius:ℝ)*((coordinates.1 - (midpoint.1:ℝ))/(radius:ℝ)) = coordinates.1
      field_simp
      ring
    · show (midpoint.2:ℝ)+(radius:ℝ)*((coordinates.2 - (midpoint.2:ℝ))/(radius:ℝ)) = coordinates.2
      field_simp
      ring
  have hqbox : q ∈ box := by
    constructor
    · show |(coordinates.1 - (midpoint.1:ℝ))/(radius:ℝ)| ≤ 1
      rw [abs_div, abs_of_pos hr, div_le_one hr]
      exact hb1
    · show |(coordinates.2 - (midpoint.2:ℝ))/(radius:ℝ)| ≤ 1
      rw [abs_div, abs_of_pos hr, div_le_one hr]
      exact hb2
  have e0 : eval newton0 q = q.1 := by
    rw [newton0_identity q, hT, hf, hg]
    simp
  have e1 : eval newton1 q = q.2 := by
    rw [newton1_identity q, hT, hf, hg]
    simp
  have b0 := eval_bound newton0 q hqbox
  have b1 := eval_bound newton1 q hqbox
  rw [e0] at b0
  rw [e1] at b1
  have a0 : |coordinates.1 - (midpoint.1:ℝ)| = (radius:ℝ) * |q.1| := by
    show _ = (radius:ℝ) * |(coordinates.1 - (midpoint.1:ℝ))/(radius:ℝ)|
    rw [abs_div, abs_of_pos hr]
    field_simp
  have a1 : |coordinates.2 - (midpoint.2:ℝ)| = (radius:ℝ) * |q.2| := by
    show _ = (radius:ℝ) * |(coordinates.2 - (midpoint.2:ℝ))/(radius:ℝ)|
    rw [abs_div, abs_of_pos hr]
    field_simp
  exact ⟨a0 ▸ mul_le_mul_of_nonneg_left b0 hr.le, a1 ▸ mul_le_mul_of_nonneg_left b1 hr.le⟩

/-- The canonical root is within `10⁻¹⁹` of the midpoint in each coordinate. -/
theorem coordinates_within :
    |coordinates.1 - (midpoint.1:ℝ)| ≤ 1/10000000000000000000 ∧
    |coordinates.2 - (midpoint.2:ℝ)| ≤ 1/10000000000000000000 := by
  have h := coordinates_sharp
  have m0 : (mass newton0 : ℝ) ≤ 1/10000000 := by
    have h0 := (Rat.cast_le (K := ℝ)).mpr mass_newton0_le
    push_cast at h0
    exact h0
  have m1 : (mass newton1 : ℝ) ≤ 1/10000000 := by
    have h1 := (Rat.cast_le (K := ℝ)).mpr mass_newton1_le
    push_cast at h1
    exact h1
  have hr : (radius:ℝ) = 1/1000000000000 := by norm_num [radius]
  rw [hr] at h
  constructor
  · calc |coordinates.1 - (midpoint.1:ℝ)| ≤ 1/1000000000000 * (mass newton0 : ℝ) := h.1
      _ ≤ 1/1000000000000 * (1/10000000) := by gcongr
      _ = 1/10000000000000000000 := by norm_num
  · calc |coordinates.2 - (midpoint.2:ℝ)| ≤ 1/1000000000000 * (mass newton1 : ℝ) := h.2
      _ ≤ 1/1000000000000 * (1/10000000) := by gcongr
      _ = 1/10000000000000000000 := by norm_num

end Sq17.EndpointRoot

#print axioms Sq17.EndpointRoot.coordinates_sharp
#print axioms Sq17.EndpointRoot.coordinates_within
