import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Sq17Lean.SquareBase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Sq17Lean.PropagationInvariant

/-!
Geometric core containment for the connected propagation checker, stated using
the project's actual `Sq17.sq` definition. The checker must still certify the
support bound throughout each angle interval. This module proves the geometric
implication of that bound; it does not assume core containment as an axiom.
-/
namespace Sq17.Propagation

noncomputable def corePoint (cx cy c s h a b : ℝ) : ℝ × ℝ :=
  (cx + h / 2 * (a * c - b * s), cy + h / 2 * (a * s + b * c))

def core (cx cy c s h : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ a b : ℝ, |a| ≤ 1 ∧ |b| ≤ 1 ∧ p = corePoint cx cy c s h a b}

theorem abs_linear_box (a b D X : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |a * D + b * X| ≤ |D| + |X| := by
  calc
    |a * D + b * X| ≤ |a * D| + |b * X| := abs_add_le _ _
    _ = |a| * |D| + |b| * |X| := by rw [abs_mul, abs_mul]
    _ ≤ |D| + |X| := by
      simpa only [one_mul] using add_le_add
        (mul_le_mul_of_nonneg_right ha (abs_nonneg D))
        (mul_le_mul_of_nonneg_right hb (abs_nonneg X))

/-- The support inequality checked for a row implies containment of every
point of its core in the corresponding real unit-square predicate. The core
direction need not be exactly normalized, matching the dyadic trace format. -/
theorem corePoint_mem_sq (cx cy c s h a b u v : ℝ)
    (hh : 0 ≤ h) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hsupport : h * (|c*u+s*v| + |c*v-s*u|) ≤ 1) :
    corePoint cx cy c s h a b ∈ Sq17.sq cx cy u v := by
  have hfirst := abs_linear_box a b (c*u+s*v) (c*v-s*u) ha hb
  have hsecond := abs_linear_box b (-a) (c*u+s*v) (c*v-s*u) hb (by simpa using ha)
  have hscale : 0 ≤ h/2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hfirst hscale
  have h2 := mul_le_mul_of_nonneg_left hsecond hscale
  change |((corePoint cx cy c s h a b).1-cx)*u +
      ((corePoint cx cy c s h a b).2-cy)*v| ≤ 1/2 ∧
    |((corePoint cx cy c s h a b).2-cy)*u -
      ((corePoint cx cy c s h a b).1-cx)*v| ≤ 1/2
  have hx : ((corePoint cx cy c s h a b).1-cx)*u +
      ((corePoint cx cy c s h a b).2-cy)*v =
      h/2*(a*(c*u+s*v)+b*(c*v-s*u)) := by dsimp [corePoint]; ring
  have hy : ((corePoint cx cy c s h a b).2-cy)*u -
      ((corePoint cx cy c s h a b).1-cx)*v =
      h/2*(b*(c*u+s*v)+(-a)*(c*v-s*u)) := by dsimp [corePoint]; ring
  rw [hx, hy, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ h/2)]
  have hbudget : h/2*(|c*u+s*v| + |c*v-s*u|) ≤ 1/2 := by
    nlinarith only [hsupport]
  exact ⟨h1.trans hbudget, h2.trans hbudget⟩

theorem core_subset_sq (cx cy c s h u v : ℝ) (hh : 0 ≤ h)
    (hsupport : h * (|c*u+s*v| + |c*v-s*u|) ≤ 1) :
    core cx cy c s h ⊆ Sq17.sq cx cy u v := by
  rintro p ⟨a, b, ha, hb, rfl⟩
  exact corePoint_mem_sq cx cy c s h a b u v hh ha hb hsupport

/-- Closed core containment suffices for transferring a strict interior
collision. It does not incorrectly exclude legal boundary contact. -/
theorem core_interior_subset (cx cy c s h u v : ℝ) (hh : 0 ≤ h)
    (hsupport : h * (|c*u+s*v| + |c*v-s*u|) ≤ 1) :
    interior (core cx cy c s h) ⊆ interior (Sq17.sq cx cy u v) :=
  interior_mono (core_subset_sq cx cy c s h u v hh hsupport)

/-- One support certificate valid for every angle in a closed row contains
the same core throughout that row, including its endpoints. -/
theorem row_core_contained (cx cy c s h lo hi : ℝ) (hh : 0 ≤ h)
    (hrow : ∀ θ ∈ Set.Icc lo hi,
      h * (|c*Real.cos θ+s*Real.sin θ| + |c*Real.sin θ-s*Real.cos θ|) ≤ 1) :
    ∀ θ ∈ Set.Icc lo hi, core cx cy c s h ⊆
      Sq17.sq cx cy (Real.cos θ) (Real.sin θ) := by
  intro θ hθ
  exact core_subset_sq cx cy c s h (Real.cos θ) (Real.sin θ) hh (hrow θ hθ)

/-- Strict core inequalities, with no normalization assumption on `(c,s)`. -/
def coreOpen (cx cy c s h : ℝ) : Set (ℝ × ℝ) :=
  {p | |(p.1-cx)*c+(p.2-cy)*s| < h*(c^2+s^2)/2 ∧
       |(p.2-cy)*c-(p.1-cx)*s| < h*(c^2+s^2)/2}

theorem coreOpen_isOpen (cx cy c s h : ℝ) : IsOpen (coreOpen cx cy c s h) := by
  change IsOpen ({p : ℝ × ℝ | |(p.1-cx)*c+(p.2-cy)*s| < h*(c^2+s^2)/2} ∩
    {p : ℝ × ℝ | |(p.2-cy)*c-(p.1-cx)*s| < h*(c^2+s^2)/2})
  apply IsOpen.inter <;> exact isOpen_lt (by fun_prop) (by fun_prop)

theorem coreOpen_subset_core (cx cy c s h : ℝ) (hh : 0 < h)
    (hn : 0 < c^2+s^2) : coreOpen cx cy c s h ⊆ core cx cy c s h := by
  rintro ⟨x,y⟩ ⟨hp, hq⟩
  have hd : 0 < h*(c^2+s^2) := mul_pos hh hn
  refine ⟨2*((x-cx)*c+(y-cy)*s)/(h*(c^2+s^2)),
    2*((y-cy)*c-(x-cx)*s)/(h*(c^2+s^2)), ?_, ?_, ?_⟩
  · rw [abs_div, abs_mul, abs_of_pos hd]
    norm_num
    apply (div_le_iff₀ hd).mpr
    change |(x-cx)*c+(y-cy)*s| < h*(c^2+s^2)/2 at hp
    linarith
  · rw [abs_div, abs_mul, abs_of_pos hd]
    norm_num
    apply (div_le_iff₀ hd).mpr
    change |(y-cy)*c-(x-cx)*s| < h*(c^2+s^2)/2 at hq
    linarith
  · apply Prod.ext <;> dsimp [corePoint]
    all_goals field_simp [ne_of_gt hh, ne_of_gt hn]
    all_goals ring

theorem coreOpen_subset_interior (cx cy c s h : ℝ) (hh : 0 < h)
    (hn : 0 < c^2+s^2) : coreOpen cx cy c s h ⊆ interior (core cx cy c s h) :=
  (coreOpen_isOpen cx cy c s h).subset_interior_iff.mpr
    (coreOpen_subset_core cx cy c s h hh hn)

/-- A strict rationally checkable core witness lies inside the true square,
provided the row support bound holds for that square's direction. -/
theorem coreOpen_subset_square_interior (cx cy c s h u v : ℝ)
    (hh : 0 < h) (hn : 0 < c^2+s^2)
    (hsupport : h * (|c*u+s*v| + |c*v-s*u|) ≤ 1) :
    coreOpen cx cy c s h ⊆ interior (Sq17.sq cx cy u v) :=
  (coreOpen_subset_interior cx cy c s h hh hn).trans
    (core_interior_subset cx cy c s h u v hh.le hsupport)

end Sq17.Propagation

#print axioms Sq17.Propagation.corePoint_mem_sq
#print axioms Sq17.Propagation.core_subset_sq
#print axioms Sq17.Propagation.core_interior_subset
#print axioms Sq17.Propagation.row_core_contained
#print axioms Sq17.Propagation.coreOpen_subset_square_interior
