import Mathlib.Analysis.Convex.Hull
import Mathlib.Basic.Real.Basic

/-!
Proof contracts for connected propagation certificates.
These are proved theorems about arbitrary pose domains, not a completed
formalization of the Python checker, trigonometric enclosures, or the n=17 result.
-/
namespace Sq17.Propagation

variable {Owner Pose : Type*}

/-- A hypothetical packing is represented by the current pose domains. -/
def Represents (D : Owner → Set Pose) (p : Owner → Pose) : Prop :=
  ∀ i, p i ∈ D i

/-- Replacing one domain preserves a packing if every removed pose conflicts
with every pose in another owner's current domain. -/
theorem pair_prune [DecidableEq Owner]
    (D : Owner → Set Pose) (p : Owner → Pose)
    (compatible : Pose → Pose → Prop) (i j : Owner) (after : Set Pose)
    (hrep : Represents D p) (hpair : compatible (p i) (p j))
    (hremove : ∀ x ∈ D i, x ∉ after → ∀ y ∈ D j, ¬ compatible x y) :
    Represents (Function.update D i after) p := by
  intro k
  by_cases hk : k = i
  · subst k
    simp only [Function.update_self]
    by_contra hx
    exact hremove (p i) (hrep i) hx (p j) (hrep j) hpair
  · simpa [Function.update_of_ne hk] using hrep k

/-- A point satisfying a necessary wall constraint survives a certified wall cut. -/
theorem wall_prune [DecidableEq Owner]
    (D : Owner → Set Pose) (p : Owner → Pose) (i : Owner)
    (after legal : Set Pose) (hrep : Represents D p) (hlegal : p i ∈ legal)
    (hremove : ∀ x ∈ D i, x ∉ after → x ∉ legal) :
    Represents (Function.update D i after) p := by
  intro k
  by_cases hk : k = i
  · subst k
    simp only [Function.update_self]
    by_contra hx
    exact hremove (p i) (hrep i) hx hlegal
  · simpa [Function.update_of_ne hk] using hrep k

/-- Every represented packing chooses a child of a covering branch. Closed
boundary poses may belong to both children; no strict split is assumed. -/
theorem branch_cover [DecidableEq Owner]
    (D : Owner → Set Pose) (p : Owner → Pose) (i : Owner)
    (left right : Set Pose) (hrep : Represents D p)
    (hcover : D i ⊆ left ∪ right) :
    Represents (Function.update D i left) p ∨
    Represents (Function.update D i right) p := by
  rcases hcover (hrep i) with hl | hr
  · left
    intro k
    by_cases hk : k = i
    · subst k; simpa using hl
    · simpa [Function.update_of_ne hk] using hrep k
  · right
    intro k
    by_cases hk : k = i
    · subst k; simpa using hr
    · simpa [Function.update_of_ne hk] using hrep k

/-- An empty owner is incompatible with representation of a complete packing. -/
theorem empty_owner (D : Owner → Set Pose) (p : Owner → Pose)
    (i : Owner) (hempty : D i = ∅) : ¬ Represents D p := by
  intro h
  have hi := h i
  rw [hempty] at hi
  exact hi

/-- The connected invariant is preserved across any finite sequence. -/
theorem chain_preserves (D : ℕ → Owner → Set Pose) (p : Owner → Pose)
    (hstart : Represents (D 0) p)
    (hstep : ∀ k, Represents (D k) p → Represents (D (k+1)) p) :
    ∀ k, Represents (D k) p := by
  intro k
  induction k with
  | zero => exact hstart
  | succ k ih => exact hstep k ih

/-- A certified incompatible subfamily excludes every larger family containing
it. This is the logical basis for reusing a small pattern across many orbits. -/
theorem subfamily_exclusion {Small Big : Type*}
    (D : Big → Set Pose) (embed : Small → Big) (hinj : Function.Injective embed)
    (compatible : Pose → Pose → Prop)
    (hsmall : ¬ ∃ p : Small → Pose,
      Represents (D ∘ embed) p ∧ ∀ i j, i ≠ j → compatible (p i) (p j)) :
    ¬ ∃ p : Big → Pose,
      Represents D p ∧ ∀ i j, i ≠ j → compatible (p i) (p j) := by
  rintro ⟨p, hrep, hpair⟩
  apply hsmall
  refine ⟨p ∘ embed, ?_, ?_⟩
  · intro i
    exact hrep (embed i)
  · intro i j hij
    exact hpair (embed i) (embed j) (fun h => hij (hinj h))

/-- Checking a strict affine inequality on vertices proves it throughout their
convex hull. This is the continuous step used by removed-piece certificates. -/
theorem strict_linear_on_hull
    (f : (ℝ × ℝ) →ₗ[ℝ] ℝ) (V : Set (ℝ × ℝ)) (b : ℝ)
    (hvertices : ∀ v ∈ V, b < f v) :
    ∀ x ∈ convexHull ℝ V, b < f x := by
  exact convexHull_min hvertices (convex_halfSpace_gt ⟨f.map_add, f.map_smul⟩ b)

/-- Convex removed pieces covered by a certified strict half-plane contain
no feasible centre on its opposite closed half-plane. -/
theorem removed_piece_disjoint
    (f : (ℝ × ℝ) →ₗ[ℝ] ℝ) (V : Set (ℝ × ℝ)) (b : ℝ)
    (hvertices : ∀ v ∈ V, b < f v) :
    Disjoint (convexHull ℝ V) {x | f x ≤ b} := by
  rw [Set.disjoint_left]
  intro x hx hlegal
  exact (not_lt_of_ge hlegal) (strict_linear_on_hull f V b hvertices x hx)

end Sq17.Propagation

#print axioms Sq17.Propagation.pair_prune
#print axioms Sq17.Propagation.wall_prune
#print axioms Sq17.Propagation.branch_cover
#print axioms Sq17.Propagation.empty_owner
#print axioms Sq17.Propagation.chain_preserves
#print axioms Sq17.Propagation.strict_linear_on_hull
#print axioms Sq17.Propagation.removed_piece_disjoint

#print axioms Sq17.Propagation.subfamily_exclusion
