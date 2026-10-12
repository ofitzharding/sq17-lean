import Sq17Lean.PropagationEndpoint
import Sq17Lean.PropagationTrig

/-! A complete rational checker for one angle-row core-containment certificate.
Its soundness theorem has no trigonometric or geometric certificate premises.
This is one component of the global propagation checker, not that whole checker. -/
namespace Sq17.Propagation

structure TrigBounds where
  cosLo : ℚ
  cosHi : ℚ
  sinLo : ℚ
  sinHi : ℚ

def TrigBounds.check (b : TrigBounds) (n : ℕ) (x : ℚ) : Bool :=
  rationalCosEnclosure n x b.cosLo b.cosHi &&
  rationalSinEnclosure n x b.sinLo b.sinHi

def TrigBounds.endpoint (b : TrigBounds) (c s : ℚ) : EndpointBounds :=
  trigEndpointBounds c s b.cosLo b.cosHi b.sinLo b.sinHi

theorem TrigBounds.endpoint_sound (b : TrigBounds) (n : ℕ) (x c s : ℚ)
    (hc : b.check n x = true) :
    (b.endpoint c s).Holds (coreD c s x) (coreX c s x) := by
  have ht := Bool.and_eq_true_iff.mp hc
  exact trigEndpointBounds_sound c s b.cosLo b.cosHi b.sinLo b.sinHi x
    (rationalCosEnclosure_sound n x b.cosLo b.cosHi ht.1)
    (rationalSinEnclosure_sound n x b.sinLo b.sinHi ht.2)

structure CoreRowCertificate where
  lo : ℚ
  hi : ℚ
  c : ℚ
  s : ℚ
  side : ℚ
  left : TrigBounds
  right : TrigBounds

def CoreRowCertificate.check (r : CoreRowCertificate) (degree : ℕ := 44) : Bool :=
  r.left.check degree r.lo && (r.right.check degree r.hi &&
    rationalAngleRowCheck r.side r.lo r.hi (r.left.endpoint r.c r.s) (r.right.endpoint r.c r.s))

/-- Acceptance of a finite rational certificate guarantees the core lies
inside every real unit square at an angle in its row. No exact direction
normalization or generator correctness is assumed. -/
theorem CoreRowCertificate.check_sound (r : CoreRowCertificate) (n : ℕ)
    (hc : r.check n = true) (cx cy : ℝ) :
    ∀ θ ∈ Set.Icc (r.lo : ℝ) (r.hi : ℝ), core cx cy r.c r.s r.side ⊆
      Sq17.sq cx cy (Real.cos θ) (Real.sin θ) := by
  have h := Bool.and_eq_true_iff.mp hc
  have h' := Bool.and_eq_true_iff.mp h.2
  exact rationalAngleRowCheck_sound cx cy r.c r.s r.side r.lo r.hi
    (r.left.endpoint r.c r.s) (r.right.endpoint r.c r.s) h'.2
    (r.left.endpoint_sound n r.lo r.c r.s h.1)
    (r.right.endpoint_sound n r.hi r.c r.s h'.1)

end Sq17.Propagation

#print axioms Sq17.Propagation.CoreRowCertificate.check_sound
