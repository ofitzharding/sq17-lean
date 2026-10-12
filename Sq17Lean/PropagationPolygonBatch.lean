import Sq17Lean.PropagationPolygonCollision

/-! A finite collection of partner rows for a single removed polygon.
The geometric conclusion is unconditional after the finite checks. Connecting
the listed regions to a live trace state remains a separate obligation. -/
namespace Sq17.Propagation

structure PolygonPartnerCertificate where
  row : CoreRowCertificate
  vertices : List (ℚ × ℚ)
  witness : (ℚ × ℚ) → (ℚ × ℚ) → (ℚ × ℚ)

def PolygonPartnerCertificate.check (t : PolygonPartnerCertificate)
    (V : List (ℚ × ℚ)) (r : CoreRowCertificate) (n : ℕ) : Bool :=
  t.row.check n && rationalPolygonCollision V t.vertices
    r.c r.s r.side t.row.c t.row.s t.row.side t.witness

def polygonBatchCheck (V : List (ℚ × ℚ)) (r : CoreRowCertificate)
    (partners : List PolygonPartnerCertificate) (n : ℕ) : Bool :=
  r.check n && partners.all (fun t => t.check V r n)

theorem polygonBatchCheck_sound (V : List (ℚ × ℚ)) (r : CoreRowCertificate)
    (partners : List PolygonPartnerCertificate) (n : ℕ)
    (hc : polygonBatchCheck V r partners n = true)
    (t : PolygonPartnerCertificate) (ht : t ∈ partners)
    (x y : ℝ × ℝ)
    (hx : x ∈ convexHull ℝ (realPoint '' {p | p ∈ V}))
    (hy : y ∈ convexHull ℝ (realPoint '' {p | p ∈ t.vertices}))
    (θ φ : ℝ) (hθ : θ ∈ Set.Icc (r.lo : ℝ) (r.hi : ℝ))
    (hφ : φ ∈ Set.Icc (t.row.lo : ℝ) (t.row.hi : ℝ)) :
    ¬ Disjoint (interior (Sq17.sq x.1 x.2 (Real.cos θ) (Real.sin θ)))
      (interior (Sq17.sq y.1 y.2 (Real.cos φ) (Real.sin φ))) := by
  have hb := Bool.and_eq_true_iff.mp hc
  have hall : ∀ u ∈ partners, u.check V r n = true := by
    simpa only [List.all_eq_true] using hb.2
  have hu := Bool.and_eq_true_iff.mp (hall t ht)
  exact rationalPolygonCollision_sound V t.vertices r t.row n n t.witness
    hb.1 hu.1 hu.2 x y hx hy θ φ hθ hφ

end Sq17.Propagation

#print axioms Sq17.Propagation.polygonBatchCheck_sound
