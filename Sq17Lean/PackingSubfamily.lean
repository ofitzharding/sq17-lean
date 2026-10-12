import Sq17Lean.SquareBase
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Choose
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Constructions.SumProd

/-! Selecting actual owners from an occupied-cell pattern. Cardinality and
injectivity are both required: mere inclusion of assigned cells is insufficient.
No finite case table or pattern exclusion is assumed to have been checked here. -/
namespace Sq17.PackingSubfamily

theorem occupied_has_owner {n : ℕ} (occupied : Finset (Fin 24))
    (hcard : occupied.card = n) (assign : Fin n → Fin 24)
    (hinj : Function.Injective assign) (hmem : ∀ i, assign i ∈ occupied)
    (cell : Fin 24) (hc : cell ∈ occupied) :
    ∃ i, assign i = cell := by
  have hs := Finset.surjOn_of_injOn_of_card_le assign
    (s := Finset.univ) (t := occupied)
    (fun i _ => hmem i) (fun i _ j _ h => hinj h)
    (by simpa only [Finset.card_univ, Fintype.card_fin, hcard] using Nat.le_refl n)
  obtain ⟨i, _, hi⟩ := hs hc
  exact ⟨i, hi⟩

/-- Any distinct subpattern of the occupied cells selects distinct actual
square owners, with the exact requested cell labels. -/
theorem select {n m : ℕ} (occupied : Finset (Fin 24))
    (hcard : occupied.card = n) (assign : Fin n → Fin 24)
    (hinj : Function.Injective assign) (hmem : ∀ i, assign i ∈ occupied)
    (pattern : Fin m → Fin 24) (hpattern : Function.Injective pattern)
    (hsub : ∀ i, pattern i ∈ occupied) :
    ∃ owner : Fin m → Fin n, Function.Injective owner ∧
      ∀ i, assign (owner i) = pattern i := by
  classical
  choose owner howner using fun i =>
    occupied_has_owner occupied hcard assign hinj hmem (pattern i) (hsub i)
  refine ⟨owner, ?_, howner⟩
  intro i j hij
  apply hpattern
  rw [← howner i, ← howner j, hij]

/-- Extract a geometric subpacking. Arbitrary cell regions permit either the
cover frame or translated trace cells without changing the combinatorial proof. -/
theorem select_packing {n m : ℕ} (occupied : Finset (Fin 24))
    (hcard : occupied.card = n) (assign : Fin n → Fin 24)
    (hinj : Function.Injective assign) (hmem : ∀ i, assign i ∈ occupied)
    (pattern : Fin m → Fin 24) (hpattern : Function.Injective pattern)
    (hsub : ∀ i, pattern i ∈ occupied)
    (region : Fin 24 → Set (ℝ × ℝ)) (box : Set (ℝ × ℝ))
    (p u : Fin n → ℝ × ℝ)
    (hc : ∀ i, p i ∈ region (assign i))
    (hu : ∀ i, (u i).1 ^ 2 + (u i).2 ^ 2 = 1)
    (hf : ∀ i, Sq17.sq (p i).1 (p i).2 (u i).1 (u i).2 ⊆ box)
    (hd : ∀ i j, i ≠ j → Disjoint
      (interior (Sq17.sq (p i).1 (p i).2 (u i).1 (u i).2))
      (interior (Sq17.sq (p j).1 (p j).2 (u j).1 (u j).2))) :
    ∃ owner : Fin m → Fin n, Function.Injective owner ∧
      (∀ i, p (owner i) ∈ region (pattern i)) ∧
      (∀ i, (u (owner i)).1 ^ 2 + (u (owner i)).2 ^ 2 = 1) ∧
      (∀ i, Sq17.sq (p (owner i)).1 (p (owner i)).2
        (u (owner i)).1 (u (owner i)).2 ⊆ box) ∧
      (∀ i j, i ≠ j → Disjoint
        (interior (Sq17.sq (p (owner i)).1 (p (owner i)).2
          (u (owner i)).1 (u (owner i)).2))
        (interior (Sq17.sq (p (owner j)).1 (p (owner j)).2
          (u (owner j)).1 (u (owner j)).2))) := by
  obtain ⟨owner, ho, ha⟩ := select occupied hcard assign hinj hmem pattern hpattern hsub
  refine ⟨owner, ho, ?_, fun i => hu (owner i), fun i => hf (owner i), ?_⟩
  · intro i
    rw [← ha i]
    exact hc (owner i)
  · intro i j hij
    exact hd (owner i) (owner j) (fun h => hij (ho h))

end Sq17.PackingSubfamily

#print axioms Sq17.PackingSubfamily.select_packing
