import Sq17Lean.PropagationPolygonBatch

/-! Connect the finite polygon checker to preservation of an actual packing.
Coverage of the removed poses and of the live partner domain is explicit;
these premises must eventually be discharged by the concrete state checker. -/
namespace Sq17.Propagation

structure AnglePose where
  center : ℝ × ℝ
  angle : ℝ

def AnglePose.square (p : AnglePose) : Set (ℝ × ℝ) :=
  Sq17.sq p.center.1 p.center.2 (Real.cos p.angle) (Real.sin p.angle)

def polygonRowRegion (V : List (ℚ × ℚ)) (r : CoreRowCertificate) : Set AnglePose :=
  {p | p.center ∈ convexHull ℝ (realPoint '' {v | v ∈ V}) ∧
    p.angle ∈ Set.Icc (r.lo : ℝ) (r.hi : ℝ)}

def polygonPartnerRegion (partners : List PolygonPartnerCertificate) : Set AnglePose :=
  {p | ∃ t ∈ partners, p ∈ polygonRowRegion t.vertices t.row}

theorem polygonBatch_incompatible (V : List (ℚ × ℚ)) (r : CoreRowCertificate)
    (partners : List PolygonPartnerCertificate) (n : ℕ)
    (hc : polygonBatchCheck V r partners n = true)
    (p q : AnglePose) (hp : p ∈ polygonRowRegion V r)
    (hq : q ∈ polygonPartnerRegion partners) :
    ¬ Disjoint (interior p.square) (interior q.square) := by
  rcases hq with ⟨t, ht, hq⟩
  exact polygonBatchCheck_sound V r partners n hc t ht
    p.center q.center hp.1 hq.1 p.angle q.angle hp.2 hq.2

/-- A finite accepted batch supplies the geometric contradiction needed by
the generic pair-pruning invariant. The partner comes from the same live
domain represented by the packing. Coverage is required, not assumed silently. -/
theorem polygonBatch_prune {Owner : Type*} [DecidableEq Owner]
    (D : Owner → Set AnglePose) (p : Owner → AnglePose) (i j : Owner)
    (after : Set AnglePose) (V : List (ℚ × ℚ)) (r : CoreRowCertificate)
    (partners : List PolygonPartnerCertificate) (n : ℕ)
    (hc : polygonBatchCheck V r partners n = true)
    (hrep : Represents D p)
    (hpair : Disjoint (interior (p i).square) (interior (p j).square))
    (hremoved : ∀ q ∈ D i, q ∉ after → q ∈ polygonRowRegion V r)
    (hpartner : D j ⊆ polygonPartnerRegion partners) :
    Represents (Function.update D i after) p := by
  apply pair_prune D p
    (fun q z => Disjoint (interior q.square) (interior z.square)) i j after hrep hpair
  intro q hq hqa z hz hdisjoint
  exact polygonBatch_incompatible V r partners n hc q z
    (hremoved q hq hqa) (hpartner hz) hdisjoint

end Sq17.Propagation

#print axioms Sq17.Propagation.polygonBatch_prune
