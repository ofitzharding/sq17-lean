import Sq17Lean.CellPermutation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Card

/-! A structural exhaustive-coverage theorem for a sharded finite orbit certificate.
A count alone is insufficient: every row must be valid, distinct, and connected
by an actual cell permutation to an entry of the supplied representative tree. -/
namespace Sq17.FiniteOrbitCover
open Sq17.CellPermutation

inductive RepTree where
  | empty
  | node (key : ℕ) (holes : List (Fin 24)) (left right : RepTree)

def RepTree.Contains : RepTree → List (Fin 24) → Prop
  | .empty, _ => False
  | .node _ here left right, holes => holes = here ∨ left.Contains holes ∨ right.Contains holes

def RepTree.find (key : ℕ) : RepTree → Option (List (Fin 24))
  | .empty => none
  | .node k holes left right =>
      if key = k then some holes else if key < k then left.find key else right.find key

theorem RepTree.find_sound (t : RepTree) (key : ℕ) (holes : List (Fin 24))
    (h : t.find key = some holes) : t.Contains holes := by
  induction t with
  | empty => simp [RepTree.find] at h
  | node k here left right il ir =>
    simp only [RepTree.find] at h
    split at h
    · simp only [Option.some.injEq] at h
      exact Or.inl h.symm
    · split at h
      · exact Or.inr (Or.inl (il h))
      · exact Or.inr (Or.inr (ir h))

structure Row where
  holes : List (Fin 24)
  symmetry : Fin 8
  representative : ℕ

def Row.occupied (r : Row) : Finset (Fin 24) := r.holes.toFinsetᶜ

def Row.tag (r : Row) : ℕ := ∑ i ∈ r.holes.toFinset, 2^i.val

def Row.check (t : RepTree) (r : Row) : Bool :=
  match t.find r.representative with
  | none => false
  | some holes => decide (r.holes.toFinset.card = 7 ∧
      r.holes.toFinset.map (cellEquiv r.symmetry).toEmbedding = holes.toFinset)

def Reaches (t : RepTree) (s : Finset (Fin 24)) : Prop :=
  ∃ g : Fin 8, ∃ holes : List (Fin 24), t.Contains holes ∧
    s.map (cellEquiv g).toEmbedding = holes.toFinsetᶜ

theorem map_complement (g : Fin 8) (s : Finset (Fin 24)) :
    sᶜ.map (cellEquiv g).toEmbedding = (s.map (cellEquiv g).toEmbedding)ᶜ := by
  rw [Finset.compl_eq_univ_sdiff, Finset.map_sdiff, Finset.map_univ_equiv,
    Finset.compl_eq_univ_sdiff]

theorem Row.check_sound (t : RepTree) (r : Row) (hc : r.check t = true) :
    r.occupied.card = 17 ∧ Reaches t r.occupied := by
  unfold Row.check at hc
  split at hc
  · contradiction
  · rename_i holes hf
    simp only [decide_eq_true_eq] at hc
    refine ⟨?_,r.symmetry,holes,t.find_sound r.representative holes hf,?_⟩
    · simp [Row.occupied, Finset.card_compl, hc.1]
    · unfold Row.occupied
      rw [map_complement, hc.2]

theorem tag_eq_of_occupied_eq (r s : Row) (h : r.occupied = s.occupied) : r.tag = s.tag := by
  have hh : r.holes.toFinset = s.holes.toFinset := compl_injective h
  unfold Row.tag
  rw [hh]

/-- Metadata enables small independently checked chunks and cheap theorem-level
composition. Half-open integer tag bounds distinguish neighbouring chunks. -/
structure GoodBlock (t : RepTree) (rows : List Row) (lo hi count : ℕ) : Prop where
  length : rows.length = count
  ordered : rows.Pairwise (fun a b => a.tag < b.tag)
  bounds : ∀ r ∈ rows, lo ≤ r.tag ∧ r.tag < hi
  valid : ∀ r ∈ rows, r.occupied.card = 17 ∧ Reaches t r.occupied

def blockCheck (t : RepTree) (rows : List Row) (lo hi count : ℕ) : Bool :=
  decide (rows.length = count) &&
  decide (rows.IsChain (fun a b => a.tag < b.tag)) &&
  rows.all (fun r => decide (lo ≤ r.tag ∧ r.tag < hi) && r.check t)

theorem blockCheck_sound (t : RepTree) (rows : List Row) (lo hi count : ℕ)
    (hc : blockCheck t rows lo hi count = true) : GoodBlock t rows lo hi count := by
  simp only [blockCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  refine ⟨hc.1.1,?_,?_,?_⟩
  · exact List.isChain_iff_pairwise.mp hc.1.2
  · intro r hr
    exact (hc.2 r hr).1
  · intro r hr
    exact r.check_sound t (hc.2 r hr).2

/-- Composition does not re-evaluate either chunk's arithmetic certificate. -/
theorem GoodBlock.append {t : RepTree} {xs ys : List Row} {lo mid upper hi nx ny : ℕ}
    (hx : GoodBlock t xs lo mid nx) (hy : GoodBlock t ys upper hi ny)
    (hsep : mid ≤ upper) (hlo : lo ≤ upper) (hhi : mid ≤ hi) : GoodBlock t (xs++ys) lo hi (nx+ny) := by
  refine ⟨by simp [hx.length,hy.length],?_,?_,?_⟩
  · rw [List.pairwise_append]
    refine ⟨hx.ordered,hy.ordered,?_⟩
    intro a ha b hb
    exact lt_of_lt_of_le (hx.bounds a ha).2 (hsep.trans (hy.bounds b hb).1)
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · have h := hx.bounds r hr
      exact ⟨h.1,lt_of_lt_of_le h.2 hhi⟩
    · have h := hy.bounds r hr
      exact ⟨hlo.trans h.1,h.2⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hx.valid r hr
    · exact hy.valid r hr

/-- An exhaustive cardinality argument applies only after validity, uniqueness
and actual orbit membership have all been proved. -/
theorem GoodBlock.exhaustive {t : RepTree} {rows : List Row} {lo hi : ℕ}
    (h : GoodBlock t rows lo hi 346104) :
    ∀ s : Finset (Fin 24), s.card = 17 → Reaches t s := by
  have hn : (rows.map Row.occupied).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    apply h.ordered.imp
    intro a b hab he
    have ht := tag_eq_of_occupied_eq a b he
    omega
  let covered := (rows.map Row.occupied).toFinset
  have hcount : covered.card = 346104 := by
    rw [List.toFinset_card_of_nodup hn, List.length_map, h.length]
  have hsub : covered ⊆ (Finset.univ : Finset (Fin 24)).powersetCard 17 := by
    intro s hs
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,(h.valid r hr).1⟩
  have htotal : ((Finset.univ : Finset (Fin 24)).powersetCard 17).card = 346104 := by
    rw [Finset.card_powersetCard]
    simp only [Finset.card_univ,Fintype.card_fin]
    decide +kernel
  have he : covered = (Finset.univ : Finset (Fin 24)).powersetCard 17 :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcount,htotal])
  intro s hs
  have hm : s ∈ covered := by rw [he]; exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hs⟩
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
  exact (h.valid r hr).2

end Sq17.FiniteOrbitCover

#print axioms Sq17.FiniteOrbitCover.blockCheck_sound
#print axioms Sq17.FiniteOrbitCover.GoodBlock.append
#print axioms Sq17.FiniteOrbitCover.GoodBlock.exhaustive
