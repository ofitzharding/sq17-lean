import Sq17Lean.PropagationGeometry
import Sq17Lean.PropagationRational

/-! An executable strict-overlap witness and its real-geometric soundness.
Angle-row support certificates remain premises; this does not yet implement
the trace checker or certify every point in a removed polygon. -/
namespace Sq17.Propagation

def rationalCoreWitness (cx cy c s h : ℚ) (p : ℚ × ℚ) : Bool :=
  decide (0 < h ∧ 0 < c^2+s^2 ∧
    |(p.1-cx)*c+(p.2-cy)*s| < h*(c^2+s^2)/2 ∧
    |(p.2-cy)*c-(p.1-cx)*s| < h*(c^2+s^2)/2)

/-- The rational checker places its witness strictly inside the true square
whenever the core support bound for that square is certified. -/
theorem rationalCoreWitness_sound (cx cy c s h : ℚ) (p : ℚ × ℚ)
    (u v : ℝ) (hw : rationalCoreWitness cx cy c s h p = true)
    (hsupport : (h : ℝ) * (|(c : ℝ)*u+(s : ℝ)*v| +
      |(c : ℝ)*v-(s : ℝ)*u|) ≤ 1) :
    realPoint p ∈ interior (Sq17.sq cx cy u v) := by
  have hq : 0 < h ∧ 0 < c^2+s^2 ∧
      |(p.1-cx)*c+(p.2-cy)*s| < h*(c^2+s^2)/2 ∧
      |(p.2-cy)*c-(p.1-cx)*s| < h*(c^2+s^2)/2 := by
    simpa only [rationalCoreWitness, decide_eq_true_eq] using hw
  have hh : (0 : ℝ) < h := by exact_mod_cast hq.1
  have hn : (0 : ℝ) < (c : ℝ)^2+(s : ℝ)^2 := by exact_mod_cast hq.2.1
  apply coreOpen_subset_square_interior cx cy c s h u v hh hn hsupport
  change |((p.1 : ℝ)-(cx : ℝ))*(c : ℝ)+((p.2 : ℝ)-(cy : ℝ))*(s : ℝ)| <
      (h : ℝ)*((c : ℝ)^2+(s : ℝ)^2)/2 ∧
    |((p.2 : ℝ)-(cy : ℝ))*(c : ℝ)-((p.1 : ℝ)-(cx : ℝ))*(s : ℝ)| <
      (h : ℝ)*((c : ℝ)^2+(s : ℝ)^2)/2
  exact_mod_cast hq.2.2

def rationalCollision (cx cy c s h dx dy e f k : ℚ) (p : ℚ × ℚ) : Bool :=
  rationalCoreWitness cx cy c s h p && rationalCoreWitness dx dy e f k p

/-- A common strict core witness proves genuine interior overlap. Merely
touching along an edge or vertex cannot satisfy this certificate. -/
theorem rationalCollision_sound (cx cy c s h dx dy e f k : ℚ) (p : ℚ × ℚ)
    (u v w z : ℝ)
    (hc : rationalCollision cx cy c s h dx dy e f k p = true)
    (hsupport : (h : ℝ) * (|(c : ℝ)*u+(s : ℝ)*v| +
      |(c : ℝ)*v-(s : ℝ)*u|) ≤ 1)
    (ksupport : (k : ℝ) * (|(e : ℝ)*w+(f : ℝ)*z| +
      |(e : ℝ)*z-(f : ℝ)*w|) ≤ 1) :
    ¬ Disjoint (interior (Sq17.sq cx cy u v))
      (interior (Sq17.sq dx dy w z)) := by
  have hw := Bool.and_eq_true_iff.mp hc
  exact Set.not_disjoint_iff.mpr ⟨realPoint p,
    rationalCoreWitness_sound cx cy c s h p u v hw.1 hsupport,
    rationalCoreWitness_sound dx dy e f k p w z hw.2 ksupport⟩

-- Kernel-checked controls: genuine overlap, boundary contact, and a
-- degenerate direction. No native evaluation is used here.
example : rationalCollision 0 0 1 0 1 (1/2) 0 1 0 1 (1/4, 0) = true := by
  norm_num [rationalCollision, rationalCoreWitness]
example : rationalCollision 0 0 1 0 1 1 0 1 0 1 (1/2, 0) = false := by
  norm_num [rationalCollision, rationalCoreWitness]
example : rationalCoreWitness 0 0 0 0 1 (0, 0) = false := by
  norm_num [rationalCoreWitness]

end Sq17.Propagation

#print axioms Sq17.Propagation.rationalCoreWitness_sound
#print axioms Sq17.Propagation.rationalCollision_sound
