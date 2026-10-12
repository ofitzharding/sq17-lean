import Sq17Lean.PropagationPolygonReplace

/-! Concrete finite row domains and checked binding to the live partner state.
These state lemmas do not assume correctness of a trace parser or exporter. -/
namespace Sq17.Propagation

structure PolygonRow where
  vertices : List (ℚ × ℚ)
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

def PolygonRow.region (r : PolygonRow) : Set AnglePose :=
  {p | p.center ∈ convexHull ℝ (realPoint '' {v | v ∈ r.vertices}) ∧
    p.angle ∈ Set.Icc (r.lo : ℝ) (r.hi : ℝ)}

def PolygonRow.ofCertificate (vertices : List (ℚ × ℚ))
    (r : CoreRowCertificate) : PolygonRow := ⟨vertices,r.lo,r.hi⟩

def rowsRegion (rows : List PolygonRow) : Set AnglePose :=
  {p | ∃ r ∈ rows, p ∈ r.region}

def stateDomains {Owner : Type*} (S : Owner → List PolygonRow) : Owner → Set AnglePose :=
  fun i => rowsRegion (S i)

def livePartnerCheck (rows : List PolygonRow)
    (partners : List PolygonPartnerCertificate) : Bool :=
  rows.all fun r => partners.any fun t => decide
    (r.vertices = t.vertices ∧ t.row.lo ≤ r.lo ∧ r.hi ≤ t.row.hi)

theorem livePartnerCheck_sound (rows : List PolygonRow)
    (partners : List PolygonPartnerCertificate)
    (hc : livePartnerCheck rows partners = true) :
    rowsRegion rows ⊆ polygonPartnerRegion partners := by
  intro p hp
  rcases hp with ⟨r,hr,hp⟩
  have hall := List.all_eq_true.mp hc
  rcases List.any_eq_true.mp (hall r hr) with ⟨t,ht,hcov⟩
  have hcov' : r.vertices = t.vertices ∧ t.row.lo ≤ r.lo ∧ r.hi ≤ t.row.hi :=
    of_decide_eq_true hcov
  refine ⟨t,ht,?_,?_,?_⟩
  · simpa only [← hcov'.1] using hp.1
  · exact (show (t.row.lo : ℝ) ≤ (r.lo : ℝ) by exact_mod_cast hcov'.2.1).trans hp.2.1
  · exact hp.2.2.trans (show (r.hi : ℝ) ≤ (t.row.hi : ℝ) by exact_mod_cast hcov'.2.2)

theorem rowsRegion_replace (preRows suffix : List PolygonRow) (r : PolygonRow) :
    rowsRegion (preRows ++ r :: suffix) = rowsRegion (preRows ++ suffix) ∪ r.region := by
  ext p
  simp only [rowsRegion, Set.mem_setOf_eq, List.mem_append, List.mem_cons, Set.mem_union]
  aesop

/-- Concrete row replacement preserves every represented packing. Source
selection is an exact list equality, and every live partner row is checked. -/
theorem polygonStateReplace_prune {Owner : Type*} [DecidableEq Owner]
    (S : Owner → List PolygonRow) (p : Owner → AnglePose) (i j : Owner)
    (preRows suffix : List PolygonRow) (before after removed kept : List (ℚ × ℚ))
    (r : CoreRowCertificate) (partners : List PolygonPartnerCertificate)
    (n : ℕ) (a b q : ℚ) (keepWitness : (ℚ × ℚ) → HullTriangleWitness)
    (hc : polygonReplaceCheck before after removed kept r partners n a b q
      keepWitness = true)
    (hsource : S i = preRows ++ PolygonRow.ofCertificate before r :: suffix)
    (hpartners : livePartnerCheck (S j) partners = true)
    (hrep : Represents (stateDomains S) p)
    (hpair : Disjoint (interior (p i).square) (interior (p j).square)) :
    Represents (stateDomains (Function.update S i
      (preRows ++ PolygonRow.ofCertificate after r :: suffix))) p := by
  have hs : stateDomains S i ⊆ rowsRegion (preRows ++ suffix) ∪ polygonRowRegion before r := by
    rw [stateDomains, hsource, rowsRegion_replace]
    exact Set.Subset.rfl
  have hp := polygonReplace_prune (stateDomains S) p i j (rowsRegion (preRows ++ suffix))
    before after removed kept r partners n a b q keepWitness hc hrep hpair hs
    (livePartnerCheck_sound (S j) partners hpartners)
  have heq : stateDomains (Function.update S i
      (preRows ++ PolygonRow.ofCertificate after r :: suffix)) =
      Function.update (stateDomains S) i (rowsRegion (preRows ++ suffix) ∪ polygonRowRegion after r) := by
    funext k
    by_cases h : k = i
    · subst k
      simp only [stateDomains, Function.update_self, rowsRegion_replace]
      rfl
    · simp only [stateDomains, Function.update_of_ne h]
  rw [heq]
  exact hp

end Sq17.Propagation

#print axioms Sq17.Propagation.livePartnerCheck_sound
#print axioms Sq17.Propagation.polygonStateReplace_prune
