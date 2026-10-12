import Sq17Lean.PropagationCutPrune
import Sq17Lean.PropagationHullTriangle

/-! Finite checked replacement of a row's center polygon. Both sides of the
cut are covered: removed poses collide, retained poses lie in the new polygon. -/
namespace Sq17.Propagation

def polygonReplaceCheck (before after removed kept : List (ℚ × ℚ))
    (r : CoreRowCertificate) (partners : List PolygonPartnerCertificate)
    (n : ℕ) (a b q : ℚ) (keepWitness : (ℚ × ℚ) → HullTriangleWitness) : Bool :=
  rationalClipCheck before removed a b q &&
  rationalClipCheck before kept (-a) (-b) (-q) &&
  kept.all (fun p => triangleHullCheck after p (keepWitness p)) &&
  polygonBatchCheck removed r partners n

/-- The unchecked generator supplies only finite data. No removed-piece or
retained-piece coverage premise is needed once this certificate accepts.
`rest` represents the owner's other live rows. -/
theorem polygonReplace_prune {Owner : Type*} [DecidableEq Owner]
    (D : Owner → Set AnglePose) (p : Owner → AnglePose) (i j : Owner)
    (rest : Set AnglePose) (before after removed kept : List (ℚ × ℚ))
    (r : CoreRowCertificate) (partners : List PolygonPartnerCertificate)
    (n : ℕ) (a b q : ℚ) (keepWitness : (ℚ × ℚ) → HullTriangleWitness)
    (hc : polygonReplaceCheck before after removed kept r partners n a b q
      keepWitness = true)
    (hrep : Represents D p)
    (hpair : Disjoint (interior (p i).square) (interior (p j).square))
    (hsource : D i ⊆ rest ∪ polygonRowRegion before r)
    (hpartner : D j ⊆ polygonPartnerRegion partners) :
    Represents (Function.update D i (rest ∪ polygonRowRegion after r)) p := by
  simp only [polygonReplaceCheck, Bool.and_eq_true] at hc
  rcases hc with ⟨⟨⟨hremove,hkeep⟩,htriangle⟩,hbatch⟩
  apply polygonBatch_prune D p i j _ removed r partners n hbatch hrep hpair
    ?_ hpartner
  intro z hz hnot
  rcases hsource hz with hr | hs
  · exact False.elim (hnot (Or.inl hr))
  · by_cases hcut : (a : ℝ)*z.center.1+(b : ℝ)*z.center.2 < (q : ℝ)
    · exact ⟨rationalClipCheck_sound before removed a b q hremove z.center hs.1 hcut,
        hs.2⟩
    · have hclosed : ((-a : ℚ) : ℝ)*z.center.1+((-b : ℚ) : ℝ)*z.center.2 ≤
          ((-q : ℚ) : ℝ) := by
        push_cast
        linarith
      have hkept := rationalClipCheck_sound_closed before kept (-a) (-b) (-q)
        hkeep z.center hs.1 hclosed
      have hafter := triangleHullCheck_list_sound kept after keepWitness htriangle hkept
      exact False.elim (hnot (Or.inr ⟨hafter,hs.2⟩))

end Sq17.Propagation

#print axioms Sq17.Propagation.polygonReplace_prune
