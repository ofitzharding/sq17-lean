import Sq17Lean.PropagationCollision
import Sq17Lean.PropagationCoreCheck
import Mathlib.Analysis.Convex.Combination

/-! Finite strict-overlap witnesses extend to whole pairs of convex polygons.
Together with checked angle rows, this rules out every placement in the product
of the two polygons. Polygon coverage and trace-state transitions are separate
obligations; this module does not yet check an entire propagation trace. -/
namespace Sq17.Propagation

private theorem abs_combo_lt (x y r a b : ℝ) (hx : |x| < r) (hy : |y| < r)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : |a*x+b*y| < r := by
  calc
    |a*x+b*y| ≤ |a*x|+|b*y| := abs_add_le _ _
    _ = a*|x|+b*|y| := by rw [abs_mul, abs_mul, abs_of_pos ha, abs_of_pos hb]
    _ < a*r+b*r := add_lt_add (mul_lt_mul_of_pos_left hx ha) (mul_lt_mul_of_pos_left hy hb)
    _ = r := by rw [← add_mul, hab, one_mul]

theorem coreOpen_combo (x y p q : ℝ × ℝ) (c s h a b : ℝ)
    (hp : p ∈ coreOpen x.1 x.2 c s h) (hq : q ∈ coreOpen y.1 y.2 c s h)
    (ha : 0 < a) (hb : 0 < b) (hab : a+b=1) :
    a • p + b • q ∈ coreOpen (a*x.1+b*y.1) (a*x.2+b*y.2) c s h := by
  rcases hp with ⟨hp₁, hp₂⟩
  rcases hq with ⟨hq₁, hq₂⟩
  change |(a*p.1+b*q.1-(a*x.1+b*y.1))*c +
      (a*p.2+b*q.2-(a*x.2+b*y.2))*s| < h*(c^2+s^2)/2 ∧
    |(a*p.2+b*q.2-(a*x.2+b*y.2))*c -
      (a*p.1+b*q.1-(a*x.1+b*y.1))*s| < h*(c^2+s^2)/2
  constructor
  · convert abs_combo_lt _ _ _ a b hp₁ hq₁ ha hb hab using 1
    congr 1
    ring
  · convert abs_combo_lt _ _ _ a b hp₂ hq₂ ha hb hab using 1
    congr 1
    ring

def collisionRegion (c s h e f k : ℝ) : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  {xy | ∃ p, p ∈ coreOpen xy.1.1 xy.1.2 c s h ∧
             p ∈ coreOpen xy.2.1 xy.2.2 e f k}

/-- Mixing the centers and their respective witnesses preserves strict overlap.
The witness is allowed to vary with the center pair. -/
theorem collisionRegion_convex (c s h e f k : ℝ) :
    Convex ℝ (collisionRegion c s h e f k) := by
  apply convex_iff_forall_pos.mpr
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨p, hpx, hpy⟩
  rcases hy with ⟨q, hqx, hqy⟩
  exact ⟨a • p + b • q,
    coreOpen_combo x.1 y.1 p q c s h a b hpx hqx ha hb hab,
    coreOpen_combo x.2 y.2 p q e f k a b hpy hqy ha hb hab⟩

theorem rationalCoreWitness_mem_coreOpen (cx cy c s h : ℚ) (p : ℚ × ℚ)
    (hw : rationalCoreWitness cx cy c s h p = true) :
    realPoint p ∈ coreOpen cx cy c s h := by
  have hq : 0 < h ∧ 0 < c^2+s^2 ∧
      |(p.1-cx)*c+(p.2-cy)*s| < h*(c^2+s^2)/2 ∧
      |(p.2-cy)*c-(p.1-cx)*s| < h*(c^2+s^2)/2 := by
    simpa only [rationalCoreWitness, decide_eq_true_eq] using hw
  change |((p.1 : ℝ)-(cx : ℝ))*(c : ℝ)+((p.2 : ℝ)-(cy : ℝ))*(s : ℝ)| <
      (h : ℝ)*((c : ℝ)^2+(s : ℝ)^2)/2 ∧
    |((p.2 : ℝ)-(cy : ℝ))*(c : ℝ)-((p.1 : ℝ)-(cx : ℝ))*(s : ℝ)| <
      (h : ℝ)*((c : ℝ)^2+(s : ℝ)^2)/2
  exact_mod_cast hq.2.2

/-- The untrusted witness supplier is queried only on the finite vertex pairs.
Every pair is checked, including pairs involving boundary vertices. -/
def rationalPolygonCollision (V W : List (ℚ × ℚ)) (c s h e f k : ℚ)
    (witness : (ℚ × ℚ) → (ℚ × ℚ) → (ℚ × ℚ)) : Bool :=
  decide (0 < h ∧ 0 < c^2+s^2 ∧ 0 < k ∧ 0 < e^2+f^2) &&
    V.all (fun v => W.all (fun w =>
      rationalCollision v.1 v.2 c s h w.1 w.2 e f k (witness v w)))

theorem rationalPolygonCollision_centers (V W : List (ℚ × ℚ)) (c s h e f k : ℚ)
    (witness : (ℚ × ℚ) → (ℚ × ℚ) → (ℚ × ℚ))
    (hc : rationalPolygonCollision V W c s h e f k witness = true)
    (x y : ℝ × ℝ) (hx : x ∈ convexHull ℝ (realPoint '' {p | p ∈ V}))
    (hy : y ∈ convexHull ℝ (realPoint '' {p | p ∈ W})) :
    (x, y) ∈ collisionRegion c s h e f k := by
  have hall : ∀ v ∈ V, ∀ w ∈ W,
      rationalCollision v.1 v.2 c s h w.1 w.2 e f k (witness v w) = true := by
    have hb := (Bool.and_eq_true_iff.mp hc).2
    simpa only [List.all_eq_true] using hb
  have hv : (realPoint '' {p | p ∈ V}) ×ˢ (realPoint '' {p | p ∈ W}) ⊆
      collisionRegion (c : ℝ) s h e f k := by
    rintro ⟨v,w⟩ ⟨⟨v', hv', rfl⟩, ⟨w', hw', rfl⟩⟩
    have hp := Bool.and_eq_true_iff.mp (hall v' hv' w' hw')
    exact ⟨realPoint (witness v' w'),
      rationalCoreWitness_mem_coreOpen _ _ _ _ _ _ hp.1,
      rationalCoreWitness_mem_coreOpen _ _ _ _ _ _ hp.2⟩
  exact convexHull_min hv (collisionRegion_convex c s h e f k)
    (mk_mem_convexHull_prod hx hy)

/-- Checked rational vertex witnesses and checked angle rows imply genuine
square-interior overlap for every center pair in the two convex hulls, and every
angle pair in the two closed rows. No normalization assumption is needed. -/
theorem rationalPolygonCollision_sound (V W : List (ℚ × ℚ))
    (r t : CoreRowCertificate) (nr nt : ℕ)
    (witness : (ℚ × ℚ) → (ℚ × ℚ) → (ℚ × ℚ))
    (hr : r.check nr = true) (ht : t.check nt = true)
    (hc : rationalPolygonCollision V W r.c r.s r.side t.c t.s t.side witness = true)
    (x y : ℝ × ℝ) (hx : x ∈ convexHull ℝ (realPoint '' {p | p ∈ V}))
    (hy : y ∈ convexHull ℝ (realPoint '' {p | p ∈ W}))
    (θ φ : ℝ) (hθ : θ ∈ Set.Icc (r.lo : ℝ) (r.hi : ℝ))
    (hφ : φ ∈ Set.Icc (t.lo : ℝ) (t.hi : ℝ)) :
    ¬ Disjoint (interior (Sq17.sq x.1 x.2 (Real.cos θ) (Real.sin θ)))
      (interior (Sq17.sq y.1 y.2 (Real.cos φ) (Real.sin φ))) := by
  have hpos : (0 : ℚ) < r.side ∧ 0 < r.c^2+r.s^2 ∧
      0 < t.side ∧ 0 < t.c^2+t.s^2 := by
    have hp := (Bool.and_eq_true_iff.mp hc).1
    simpa only [decide_eq_true_eq] using hp
  have hposR : (0 : ℝ) < r.side ∧ 0 < (r.c : ℝ)^2+(r.s : ℝ)^2 ∧
      0 < (t.side : ℝ) ∧ 0 < (t.c : ℝ)^2+(t.s : ℝ)^2 := by exact_mod_cast hpos
  rcases rationalPolygonCollision_centers V W r.c r.s r.side t.c t.s t.side
      witness hc x y hx hy with ⟨p, hp, hq⟩
  apply Set.not_disjoint_iff.mpr
  refine ⟨p, ?_, ?_⟩
  · exact interior_mono (r.check_sound nr hr x.1 x.2 θ hθ)
      (coreOpen_subset_interior x.1 x.2 r.c r.s r.side hposR.1 hposR.2.1 hp)
  · exact interior_mono (t.check_sound nt ht y.1 y.2 φ hφ)
      (coreOpen_subset_interior y.1 y.2 t.c t.s t.side hposR.2.2.1 hposR.2.2.2 hq)

end Sq17.Propagation

#print axioms Sq17.Propagation.collisionRegion_convex
#print axioms Sq17.Propagation.rationalPolygonCollision_sound
