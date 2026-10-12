import Sq17Lean.FiniteOrbitCoverCheck

/-! A separate finite certificate assigns each representative either to a
symmetry image of a small excluded pattern, or to an exact full-case roster.
This checks coverage and cell identities only. The geometric exclusion or
capture theorem for every referenced roster is a separate required proof. -/
namespace Sq17.RepresentativeCases
open Sq17.FiniteOrbitCover

inductive Assignment where
  | pattern (index : ℕ) (symmetry : Fin 8)
  | full (index : ℕ)
  deriving DecidableEq

def Matches (patterns fullCases : ℕ → List (Fin 24))
    (holes : List (Fin 24)) : Assignment → Prop
  | .pattern index g => patterns index ≠ [] ∧ (patterns index).Nodup ∧
      ∀ i ∈ patterns index, CellPermutation.perm g i ∈ holes.toFinsetᶜ
  | .full index => (fullCases index).length = 17 ∧ (fullCases index).Nodup ∧
      (fullCases index).toFinset = holes.toFinsetᶜ

instance (patterns fullCases : ℕ → List (Fin 24)) (holes : List (Fin 24))
    (a : Assignment) : Decidable (Matches patterns fullCases holes a) := by
  cases a <;> unfold Matches <;> infer_instance

inductive Certificate where
  | empty
  | node (assignment : Assignment) (left right : Certificate)

def Certificate.check (patterns fullCases : ℕ → List (Fin 24)) :
    RepTree → Certificate → Bool
  | .empty, .empty => true
  | .node _ holes left right, .node a cl cr =>
      decide (Matches patterns fullCases holes a) &&
      cl.check patterns fullCases left && cr.check patterns fullCases right
  | _, _ => false

def Certificate.Uses : Certificate → Assignment → Prop
  | .empty, _ => False
  | .node here left right, a => a = here ∨ left.Uses a ∨ right.Uses a

/-- Every table member is linked to one of the concrete assignments present
in the accepted certificate. No representative can disappear at an empty or
mismatched branch, and full-case rosters must match all occupied cells. -/
theorem Certificate.check_sound (patterns fullCases : ℕ → List (Fin 24))
    (tree : RepTree) (cert : Certificate)
    (hc : cert.check patterns fullCases tree = true) :
    ∀ holes, tree.Contains holes →
      ∃ a, cert.Uses a ∧ Matches patterns fullCases holes a := by
  induction tree generalizing cert with
  | empty =>
      intro holes hh
      exact False.elim hh
  | node key here left right il ir =>
      cases cert with
      | empty => simp [Certificate.check] at hc
      | node a cl cr =>
          have hn : Matches patterns fullCases here a ∧
              cl.check patterns fullCases left = true ∧
              cr.check patterns fullCases right = true := by
            simpa only [Certificate.check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hc
          intro holes hh
          rcases hh with rfl | hl | hr
          · exact ⟨a, Or.inl rfl, hn.1⟩
          · obtain ⟨b, hu, hm⟩ := il cl hn.2.1 holes hl
            exact ⟨b, Or.inr (Or.inl hu), hm⟩
          · obtain ⟨b, hu, hm⟩ := ir cr hn.2.2 holes hr
            exact ⟨b, Or.inr (Or.inr hu), hm⟩

end Sq17.RepresentativeCases

#print axioms Sq17.RepresentativeCases.Certificate.check_sound
