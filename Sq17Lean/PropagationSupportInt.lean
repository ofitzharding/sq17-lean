import Sq17Lean.PropagationSupportCollision

/-! Bounds-free integer support collision.

The existing `rationalSupportCollision` is handed four projection intervals per
polygon pair and re-checks every vertex against them in rational arithmetic. Here
the checker computes the projection extrema itself, on integer numerators over
explicit positive denominators, and compares cleared-denominator integers. No
interval data is supplied at all.

`intSupportCollision_sound` shows that acceptance implies the existing rational
check for explicit computed bounds, so every downstream soundness theorem applies
unchanged. -/
namespace Sq17.Propagation.IntSupport

def proj (a b : ℤ) (v : ℤ × ℤ) : ℤ := a*v.1+b*v.2

def minProj (a b : ℤ) (v0 : ℤ × ℤ) (vs : List (ℤ × ℤ)) : ℤ :=
  vs.foldl (fun m v => min m (proj a b v)) (proj a b v0)

def maxProj (a b : ℤ) (v0 : ℤ × ℤ) (vs : List (ℤ × ℤ)) : ℤ :=
  vs.foldl (fun m v => max m (proj a b v)) (proj a b v0)

theorem foldl_min_spec (a b : ℤ) (vs : List (ℤ × ℤ)) (m : ℤ) :
    vs.foldl (fun m v => min m (proj a b v)) m ≤ m ∧
    ∀ v ∈ vs, vs.foldl (fun m v => min m (proj a b v)) m ≤ proj a b v := by
  induction vs generalizing m with
  | nil => exact ⟨le_refl _, by intro v hv; simp at hv⟩
  | cons w ws ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (min m (proj a b w))
    refine ⟨h1.trans (min_le_left _ _), ?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact h1.trans (min_le_right _ _)
    · exact h2 v hv

theorem foldl_max_spec (a b : ℤ) (vs : List (ℤ × ℤ)) (m : ℤ) :
    m ≤ vs.foldl (fun m v => max m (proj a b v)) m ∧
    ∀ v ∈ vs, proj a b v ≤ vs.foldl (fun m v => max m (proj a b v)) m := by
  induction vs generalizing m with
  | nil => exact ⟨le_refl _, by intro v hv; simp at hv⟩
  | cons w ws ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (max m (proj a b w))
    refine ⟨(le_max_left _ _).trans h1, ?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact (le_max_right _ _).trans h1
    · exact h2 v hv

theorem minProj_le {a b : ℤ} {v0 : ℤ × ℤ} {vs : List (ℤ × ℤ)} {v : ℤ × ℤ}
    (hv : v ∈ v0 :: vs) : minProj a b v0 vs ≤ proj a b v := by
  obtain ⟨h1, h2⟩ := foldl_min_spec a b vs (proj a b v0)
  rcases List.mem_cons.mp hv with rfl | hv
  · exact h1
  · exact h2 v hv

theorem le_maxProj {a b : ℤ} {v0 : ℤ × ℤ} {vs : List (ℤ × ℤ)} {v : ℤ × ℤ}
    (hv : v ∈ v0 :: vs) : proj a b v ≤ maxProj a b v0 vs := by
  obtain ⟨h1, h2⟩ := foldl_max_spec a b vs (proj a b v0)
  rcases List.mem_cons.mp hv with rfl | hv
  · exact h1
  · exact h2 v hv

/-- The rational point with integer numerators over the common denominator `pd`. -/
def toQ (pd : ℤ) (v : ℤ × ℤ) : ℚ × ℚ := ((v.1:ℚ)/pd, (v.2:ℚ)/pd)

theorem proj_toQ (A B ad pd : ℤ) (had : (ad:ℚ) ≠ 0) (hpd : (pd:ℚ) ≠ 0) (v : ℤ × ℤ) :
    ((A:ℚ)/ad)*(toQ pd v).1+((B:ℚ)/ad)*(toQ pd v).2 =
      ((proj A B v : ℤ) : ℚ)/((ad:ℚ)*pd) := by
  simp only [toQ, proj]
  push_cast
  field_simp

/-- One axis: both strict gap inequalities, with denominators cleared. -/
def axisOK (a b : ℤ) (V W : List (ℤ × ℤ)) (L T : ℤ) : Bool :=
  match V, W with
  | v0::vs, w0::ws =>
    decide ((maxProj a b w0 ws-minProj a b v0 vs)*L < T ∧
      (maxProj a b v0 vs-minProj a b w0 ws)*L < T)
  | _, _ => false

/-- The exact projection extrema, as the interval record the rational checker expects. -/
def axisBounds (a b : ℤ) (V W : List (ℤ × ℤ)) (d : ℚ) : SupportInterval :=
  match V, W with
  | v0::vs, w0::ws =>
    ⟨(minProj a b v0 vs : ℚ)/d, (maxProj a b v0 vs : ℚ)/d,
     (minProj a b w0 ws : ℚ)/d, (maxProj a b w0 ws : ℚ)/d⟩
  | _, _ => ⟨0,0,0,0⟩

theorem axis_sound (A B ad pd L T : ℤ) (t : ℚ) (V W : List (ℤ × ℤ))
    (had : 0 < ad) (hpd : 0 < pd)
    (hT : ∀ x : ℤ, x*L < T → (x:ℚ)/((ad:ℚ)*pd) < t)
    (h : axisOK A B V W L T = true) :
    projectionIntervalCheck (V.map (toQ pd)) (W.map (toQ pd)) ((A:ℚ)/ad) ((B:ℚ)/ad) t
      (axisBounds A B V W ((ad:ℚ)*pd)) = true := by
  match V, W, h with
  | [], _, h => simp [axisOK] at h
  | _::_, [], h => simp [axisOK] at h
  | v0::vs, w0::ws, h =>
    have hadQ : (0:ℚ) < (ad:ℚ) := by exact_mod_cast had
    have hpdQ : (0:ℚ) < (pd:ℚ) := by exact_mod_cast hpd
    have hd : (0:ℚ) < (ad:ℚ)*pd := mul_pos hadQ hpdQ
    simp only [axisOK, decide_eq_true_eq] at h
    simp only [projectionIntervalCheck, axisBounds, Bool.and_eq_true, List.all_eq_true]
    refine ⟨⟨?_, ?_⟩, decide_eq_true ⟨?_, ?_⟩⟩
    · intro q hq
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hq
      rw [proj_toQ A B ad pd hadQ.ne' hpdQ.ne' v]
      apply decide_eq_true
      constructor
      · exact (div_le_div_iff_of_pos_right hd).mpr (by exact_mod_cast minProj_le hv)
      · exact (div_le_div_iff_of_pos_right hd).mpr (by exact_mod_cast le_maxProj hv)
    · intro q hq
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hq
      rw [proj_toQ A B ad pd hadQ.ne' hpdQ.ne' v]
      apply decide_eq_true
      constructor
      · exact (div_le_div_iff_of_pos_right hd).mpr (by exact_mod_cast minProj_le hv)
      · exact (div_le_div_iff_of_pos_right hd).mpr (by exact_mod_cast le_maxProj hv)
    · have h1 := hT _ h.1
      rw [← sub_div]
      push_cast at h1
      exact h1
    · have h2 := hT _ h.2
      rw [← sub_div]
      push_cast at h2
      exact h2

/-- Twice the cross term `|c e + s f| + |c f - s e|`, on numerators. -/
def crossNum (C S E F : ℤ) : ℤ := |C*E+S*F|+|C*F-S*E|

theorem cross_eq (C S cd E F ed : ℤ) (hcd : 0 < cd) (hed : 0 < ed) :
    |(C:ℚ)/cd*((E:ℚ)/ed)+(S:ℚ)/cd*((F:ℚ)/ed)|+|(C:ℚ)/cd*((F:ℚ)/ed)-(S:ℚ)/cd*((E:ℚ)/ed)| =
      ((crossNum C S E F : ℤ) : ℚ)/((cd:ℚ)*ed) := by
  have hcdQ : (0:ℚ) < (cd:ℚ) := by exact_mod_cast hcd
  have hedQ : (0:ℚ) < (ed:ℚ) := by exact_mod_cast hed
  have hp : (0:ℚ) < (cd:ℚ)*ed := mul_pos hcdQ hedQ
  have e1 : (C:ℚ)/cd*((E:ℚ)/ed)+(S:ℚ)/cd*((F:ℚ)/ed) = ((C:ℚ)*E+S*F)/((cd:ℚ)*ed) := by
    field_simp
  have e2 : (C:ℚ)/cd*((F:ℚ)/ed)-(S:ℚ)/cd*((E:ℚ)/ed) = ((C:ℚ)*F-S*E)/((cd:ℚ)*ed) := by
    field_simp
  rw [e1, e2, abs_div, abs_div, abs_of_pos hp, ← add_div]
  simp only [crossNum]
  push_cast
  rfl

def intSupportCollision (V W : List (ℤ × ℤ)) (pd C S cd H hd E F ed K kd : ℤ) : Bool :=
  let D := crossNum C S E F
  let L := 2*hd*cd*kd*ed
  let TA := (H*(C*C+S*S)*kd*ed+K*D*hd*cd)*pd
  let TB := (H*D*kd*ed+K*(E*E+F*F)*hd*cd)*pd
  decide (0<pd ∧ 0<cd ∧ 0<hd ∧ 0<ed ∧ 0<kd ∧ 0<H ∧ 0<C*C+S*S ∧ 0<K ∧ 0<E*E+F*F) &&
  axisOK C S V W L TA && axisOK (-S) C V W L TA &&
  axisOK E F V W L TB && axisOK (-F) E V W L TB

/-- The computed bounds handed to the rational checker. -/
def intBounds (V W : List (ℤ × ℤ)) (pd C S cd E F ed : ℤ) : Fin 4 → SupportInterval :=
  ![axisBounds C S V W ((cd:ℚ)*pd), axisBounds (-S) C V W ((cd:ℚ)*pd),
    axisBounds E F V W ((ed:ℚ)*pd), axisBounds (-F) E V W ((ed:ℚ)*pd)]

/-- Acceptance by the integer checker implies acceptance by the existing rational
checker, on the corresponding rational data and the computed bounds. -/
theorem intSupportCollision_sound (V W : List (ℤ × ℤ)) (pd C S cd H hd E F ed K kd : ℤ)
    (h : intSupportCollision V W pd C S cd H hd E F ed K kd = true) :
    rationalSupportCollision (V.map (toQ pd)) (W.map (toQ pd))
      ((C:ℚ)/cd) ((S:ℚ)/cd) ((H:ℚ)/hd) ((E:ℚ)/ed) ((F:ℚ)/ed) ((K:ℚ)/kd)
      (intBounds V W pd C S cd E F ed) = true := by
  simp only [intSupportCollision, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hpd, hcd, hhd, hed, hkd, hH, hCS, hK, hEF⟩, h0⟩, h1⟩, h2⟩, h3⟩ := h
  have hpdQ : (0:ℚ) < (pd:ℚ) := by exact_mod_cast hpd
  have hcdQ : (0:ℚ) < (cd:ℚ) := by exact_mod_cast hcd
  have hhdQ : (0:ℚ) < (hd:ℚ) := by exact_mod_cast hhd
  have hedQ : (0:ℚ) < (ed:ℚ) := by exact_mod_cast hed
  have hkdQ : (0:ℚ) < (kd:ℚ) := by exact_mod_cast hkd
  have hHQ : (0:ℚ) < (H:ℚ) := by exact_mod_cast hH
  have hKQ : (0:ℚ) < (K:ℚ) := by exact_mod_cast hK
  have hCSQ : (0:ℚ) < (C:ℚ)*C+S*S := by exact_mod_cast hCS
  have hEFQ : (0:ℚ) < (E:ℚ)*E+F*F := by exact_mod_cast hEF
  have hcross := cross_eq C S cd E F ed hcd hed
  set D : ℤ := crossNum C S E F with hD
  -- thresholds, with denominators cleared
  have hTA : ∀ x : ℤ, x*(2*hd*cd*kd*ed) < (H*(C*C+S*S)*kd*ed+K*D*hd*cd)*pd →
      (x:ℚ)/((cd:ℚ)*pd) <
        ((H:ℚ)/hd*(((C:ℚ)/cd)^2+((S:ℚ)/cd)^2)+(K:ℚ)/kd*
          (|(C:ℚ)/cd*((E:ℚ)/ed)+(S:ℚ)/cd*((F:ℚ)/ed)|+
           |(C:ℚ)/cd*((F:ℚ)/ed)-(S:ℚ)/cd*((E:ℚ)/ed)|))/2 := by
    intro x hx
    rw [hcross]
    have hxQ : (x:ℚ)*(2*hd*cd*kd*ed) < ((H:ℚ)*(C*C+S*S)*kd*ed+K*D*hd*cd)*pd := by
      exact_mod_cast hx
    rw [div_lt_iff₀ (mul_pos hcdQ hpdQ)]
    have hpos : (0:ℚ) < 2*hd*cd*kd*ed := by positivity
    have key : ((H:ℚ)/hd*(((C:ℚ)/cd)^2+((S:ℚ)/cd)^2)+(K:ℚ)/kd*((D:ℚ)/((cd:ℚ)*ed)))/2*((cd:ℚ)*pd) =
        (((H:ℚ)*(C*C+S*S)*kd*ed+K*D*hd*cd)*pd)/(2*hd*cd*kd*ed) := by
      field_simp
    rw [key, lt_div_iff₀ hpos]
    exact hxQ
  have hTB : ∀ x : ℤ, x*(2*hd*cd*kd*ed) < (H*D*kd*ed+K*(E*E+F*F)*hd*cd)*pd →
      (x:ℚ)/((ed:ℚ)*pd) <
        ((H:ℚ)/hd*(|(C:ℚ)/cd*((E:ℚ)/ed)+(S:ℚ)/cd*((F:ℚ)/ed)|+
           |(C:ℚ)/cd*((F:ℚ)/ed)-(S:ℚ)/cd*((E:ℚ)/ed)|)+
          (K:ℚ)/kd*(((E:ℚ)/ed)^2+((F:ℚ)/ed)^2))/2 := by
    intro x hx
    rw [hcross]
    have hxQ : (x:ℚ)*(2*hd*cd*kd*ed) < ((H:ℚ)*D*kd*ed+K*(E*E+F*F)*hd*cd)*pd := by
      exact_mod_cast hx
    rw [div_lt_iff₀ (mul_pos hedQ hpdQ)]
    have hpos : (0:ℚ) < 2*hd*cd*kd*ed := by positivity
    have key : ((H:ℚ)/hd*((D:ℚ)/((cd:ℚ)*ed))+(K:ℚ)/kd*(((E:ℚ)/ed)^2+((F:ℚ)/ed)^2))/2*((ed:ℚ)*pd) =
        (((H:ℚ)*D*kd*ed+K*(E*E+F*F)*hd*cd)*pd)/(2*hd*cd*kd*ed) := by
      field_simp
    rw [key, lt_div_iff₀ hpos]
    exact hxQ
  have a0 := axis_sound C S cd pd _ _ _ V W hcd hpd hTA h0
  have a1 := axis_sound (-S) C cd pd _ _ _ V W hcd hpd hTA h1
  have a2 := axis_sound E F ed pd _ _ _ V W hed hpd hTB h2
  have a3 := axis_sound (-F) E ed pd _ _ _ V W hed hpd hTB h3
  have hposQ : (0:ℚ) < (H:ℚ)/hd ∧ 0 < ((C:ℚ)/cd)^2+((S:ℚ)/cd)^2 ∧ 0 < (K:ℚ)/kd ∧
      0 < ((E:ℚ)/ed)^2+((F:ℚ)/ed)^2 := by
    refine ⟨div_pos hHQ hhdQ, ?_, div_pos hKQ hkdQ, ?_⟩
    · have : ((C:ℚ)/cd)^2+((S:ℚ)/cd)^2 = ((C:ℚ)*C+S*S)/((cd:ℚ)*cd) := by field_simp
      rw [this]; exact div_pos hCSQ (mul_pos hcdQ hcdQ)
    · have : ((E:ℚ)/ed)^2+((F:ℚ)/ed)^2 = ((E:ℚ)*E+F*F)/((ed:ℚ)*ed) := by field_simp
      rw [this]; exact div_pos hEFQ (mul_pos hedQ hedQ)
  simp only [rationalSupportCollision, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨hposQ, ?_⟩
  intro i _
  fin_cases i
  · simpa [coreSupportAxes, coreSupportThresholds, intBounds] using a0
  · simpa [coreSupportAxes, coreSupportThresholds, intBounds, neg_div] using a1
  · simpa [coreSupportAxes, coreSupportThresholds, intBounds] using a2
  · simpa [coreSupportAxes, coreSupportThresholds, intBounds, neg_div] using a3

end Sq17.Propagation.IntSupport

#print axioms Sq17.Propagation.IntSupport.intSupportCollision_sound
