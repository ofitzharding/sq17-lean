import Sq17Lean.PropagationRationalClip
import Sq17Lean.PropagationPolygonPrune

/-! A checked geometric state transition: remove a strict half-plane portion
of one row after checking coverage and collision against the live partner. -/
namespace Sq17.Propagation

theorem polygonCut_prune {Owner : Type*} [DecidableEq Owner]
    (D : Owner → Set AnglePose) (p : Owner → AnglePose) (i j : Owner)
    (before candidates : List (ℚ × ℚ)) (r : CoreRowCertificate)
    (partners : List PolygonPartnerCertificate) (n : ℕ) (a b q : ℚ)
    (hclip : rationalClipCheck before candidates a b q = true)
    (hbatch : polygonBatchCheck candidates r partners n = true)
    (hrep : Represents D p)
    (hpair : Disjoint (interior (p i).square) (interior (p j).square))
    (hsource : D i ⊆ polygonRowRegion before r)
    (hpartner : D j ⊆ polygonPartnerRegion partners) :
    Represents (Function.update D i (D i ∩
      {z | (q : ℝ) ≤ (a : ℝ)*z.center.1+(b : ℝ)*z.center.2})) p := by
  apply polygonBatch_prune D p i j _ candidates r partners n hbatch hrep hpair
    ?_ hpartner
  intro z hz hremoved
  have hs := hsource hz
  have hcut : (a : ℝ)*z.center.1+(b : ℝ)*z.center.2 < (q : ℝ) := by
    apply lt_of_not_ge
    intro h
    exact hremoved ⟨hz,h⟩
  exact ⟨rationalClipCheck_sound before candidates a b q hclip z.center hs.1 hcut,
    hs.2⟩

end Sq17.Propagation

#print axioms Sq17.Propagation.polygonCut_prune
