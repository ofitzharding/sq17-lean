import Sq17Lean.CaptureTableFast
import Sq17Lean.HalfPlaneTable

/-! Equivalence of the isolated core-only table checker to the existing checked
core/wall certificates. This module does not change any frozen definitions. -/
namespace Sq17.Propagation.HalfPlaneState.CaptureTableFast
open scoped BigOperators

 theorem absQ_eq (x : ℚ) : absQ x = |x| := by
  by_cases hx : 0 ≤ x
  · simp [absQ, hx, abs_of_nonneg hx]
  · simp [absQ, hx, abs_of_neg (lt_of_not_ge hx)]

 theorem factorial_eq (n : Nat) : factorial n = n.factorial := by
  induction n with
  | zero => simp [factorial]
  | succ n ih => simp [factorial, Nat.factorial_succ, ih]

 theorem power_eq (x : ℚ) (n : Nat) : power x n = x^n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp [power, pow_succ, ih]

 theorem coeff_eq (n : Nat) : coeff n = Sq17.Propagation.trigCoeff n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [coeff, Sq17.Propagation.trigCoeff, ih]

 theorem taylorSum_eq (x : ℚ) (n : Nat) : taylorSum x n =
    (∑ k ∈ Finset.range n, (Sq17.Propagation.trigCoeff k).1*x^k/(k.factorial:ℚ),
     ∑ k ∈ Finset.range n, (Sq17.Propagation.trigCoeff k).2*x^k/(k.factorial:ℚ)) := by
  induction n with
  | zero => simp [taylorSum]
  | succ n ih =>
    simp [taylorSum, ih, Finset.sum_range_succ, power_eq, factorial_eq, coeff_eq,
      mul_div_assoc]

 theorem remainder_eq (n : Nat) (x : ℚ) :
    remainder n x = Sq17.Propagation.trigRemainder n x := by
  simp [remainder, power_eq, factorial_eq, absQ_eq, Sq17.Propagation.trigRemainder]

 def Bounds.toTrig (b : Bounds) : TrigBounds := ⟨b.cosLo,b.cosHi,b.sinLo,b.sinHi⟩
 def Endpoint.toEndpoint (b : Endpoint) : EndpointBounds := ⟨b.dLo,b.dHi,b.xLo,b.xHi⟩

 theorem trigCheck_eq (n : Nat) (x : ℚ) (b : Bounds) :
    trigCheck n x b = b.toTrig.check n x := by
  apply Bool.eq_iff_iff.mpr
  unfold trigCheck TrigBounds.check rationalCosEnclosure rationalSinEnclosure
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  simp only [taylorSum_eq, remainder_eq, cosTaylor, sinTaylor, Bounds.toTrig]
  tauto


 theorem endpoint_eq (c s : ℚ) (b : Bounds) :
    (endpoint c s b).toEndpoint = b.toTrig.endpoint c s := by
  rfl

 theorem endpoint_dLo_eq (c s : ℚ) (b : Bounds) :
    (endpoint c s b).dLo = (b.toTrig.endpoint c s).dLo := rfl

 theorem endpointCheck_eq (h : ℚ) (b : Endpoint) :
    endpointCheck h b = rationalEndpointCheck h b.toEndpoint := by
  simp [endpointCheck, rationalEndpointCheck, Endpoint.toEndpoint, absQ_eq]

 theorem wallDir_eq (e : Entry) : wallDir e = HalfPlaneState.wallDir e := rfl

 theorem entryCheck_eq (n : Nat) (e : Entry) (b : Bounds × Bounds) :
    entryCheck n e b = entryOK n e (b.1.toTrig,b.2.toTrig) := by
  apply Bool.eq_iff_iff.mpr
  unfold entryCheck entryOK CoreRowCertificate.check WallRowCertificate.check rationalAngleRowCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  simp only [Entry.core, Entry.wallRow, trigCheck_eq, endpointCheck_eq,
    endpoint_eq, endpoint_dLo_eq, wallDir_eq, absQ_eq]
  tauto


 theorem entryCheck_valid (n : Nat) (e : Entry) (b : Bounds × Bounds)
    (h : entryCheck n e b = true) : e.Valid n := by
  have hc : entryOK n e (b.1.toTrig,b.2.toTrig) = true := by
    rw [← entryCheck_eq]
    exact h
  simp only [entryOK, Bool.and_eq_true] at hc
  exact ⟨⟨e.core b.1.toTrig b.2.toTrig, hc.1, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨e.wallRow b.1.toTrig b.2.toTrig, hc.2, rfl, rfl, rfl⟩⟩

 theorem tableValid_of_checks (n : Nat) (old current : Array Entry)
    (ids : Array Nat) (B : Array (Bounds × Bounds))
    (hold : TableValid old n)
    (hinherited : inheritedCheck old current ids = true)
    (hfresh : freshCheck n current ids.size B = true) : TableValid current n := by
  intro k e hk
  have hkt : k < current.size := by
    by_contra hn
    rw [Array.getElem?_eq_none (not_lt.mp hn)] at hk
    simp at hk
  simp only [inheritedCheck, Bool.and_eq_true] at hinherited
  simp only [freshCheck, Bool.and_eq_true] at hfresh
  by_cases hki : k < ids.size
  · have hi := List.all_eq_true.mp hinherited.2 k (List.mem_range.mpr hki)
    cases hid : ids[k]? with
    | none => simp [hid] at hi
    | some j =>
      cases ho : old[j]? with
      | none => simp [hid, hk, ho] at hi
      | some f =>
        have hef : e = f := by simpa [hid, hk, ho] using hi
        subst e
        exact hold j f ho
  · have hle : ids.size ≤ k := Nat.le_of_not_lt hki
    have hj : k-ids.size < current.size-ids.size := by omega
    have key : ids.size+(k-ids.size) = k := by omega
    have hi := List.all_eq_true.mp hfresh.2 (k-ids.size) (List.mem_range.mpr hj)
    cases hb : B[k-ids.size]? with
    | none => simp [key, hk, hb] at hi
    | some b =>
      apply entryCheck_valid n e b
      simpa [key, hk, hb] using hi

 /-- The first chunk has no inherited prefix. -/
 theorem tableValid_initial (n : Nat) (T : Array Entry) (B : Array (Bounds × Bounds))
    (h : freshCheck n T 0 B = true) : TableValid T n := by
  apply tableValid_of_checks n #[] T #[] B
  · intro k e hk
    simp at hk
  · simp [inheritedCheck]
  · exact h

end Sq17.Propagation.HalfPlaneState.CaptureTableFast
