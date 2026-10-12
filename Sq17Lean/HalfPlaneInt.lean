import Sq17Lean.HalfPlanePrototype
import Sq17Lean.PropagationSupportInt
import Sq17Lean.HalfPlaneFast

/-! Integer half-plane collision check with no certificate data.

A domain is a list of integer half-planes `a*x+b*y ≤ q`. For a direction `t`, any
two constraints `u,v` with `t` in the cone of their normals give the bound
`t·x ≤ (l*u.q+m*v.q)/d`. The checker scans all ordered pairs of the list, keeps
the smallest bound it finds, and compares cleared-denominator integers. No bounds,
vertices or witness indices are supplied.

Soundness never uses that the list is sorted or irredundant: every bound found is
valid, a poor ordering can only make the check fail. Dropping a constraint from a
list enlarges its domain, so the producer may prune lists freely. -/
namespace Sq17.Propagation.HalfPlaneInt
open Sq17.Propagation.HalfPlanePrototype

theorem iabs_eq (a : ℤ) : iabs a = |a| := by
  unfold iabs
  split_ifs with h
  · exact (abs_of_nonneg h).symm
  · exact (abs_of_neg (not_le.mp h)).symm

theorem crossNum_eq (C S E F : ℤ) : crossNum C S E F = IntSupport.crossNum C S E F := by
  simp only [crossNum, IntSupport.crossNum, iabs_eq]

def IC.Holds (h : IC) (x : ℝ × ℝ) : Prop := (h.a:ℝ)*x.1+(h.b:ℝ)*x.2 ≤ (h.q:ℝ)

def Dom (hs : List IC) : Set (ℝ × ℝ) := {x | ∀ h ∈ hs, h.Holds x}

theorem dom_mono {hs ks : List IC} (h : ∀ k ∈ ks, k ∈ hs) : Dom hs ⊆ Dom ks :=
  fun _ hx k hk => hx k (h k hk)

/-- `o`, if present, is a valid upper bound `N/d` for `ta*x+tb*y` at `x`. -/
def Good (x : ℝ × ℝ) (ta tb : ℤ) (o : Option (ℤ × ℤ)) : Prop :=
  ∀ N d, o = some (N, d) → 0 < d ∧ (d:ℝ)*((ta:ℝ)*x.1+(tb:ℝ)*x.2) ≤ (N:ℝ)

theorem pairUpper_good (u v : IC) (ta tb : ℤ) (x : ℝ × ℝ)
    (hu : u.Holds x) (hv : v.Holds x) : Good x ta tb (pairUpper u v ta tb) := by
  intro N d h
  unfold pairUpper at h
  split_ifs at h with hc
  obtain ⟨hd, hl, hm⟩ := hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨hd, ?_⟩
  have hlR : (0:ℝ) ≤ (ta:ℝ)*v.b-v.a*tb := by exact_mod_cast hl
  have hmR : (0:ℝ) ≤ (u.a:ℝ)*tb-ta*u.b := by exact_mod_cast hm
  unfold IC.Holds at hu hv
  have hh := add_le_add (mul_le_mul_of_nonneg_left hu hlR) (mul_le_mul_of_nonneg_left hv hmR)
  push_cast
  linarith

theorem better_eq (p q : Option (ℤ × ℤ)) : better p q = p ∨ better p q = q := by
  cases p with
  | none => exact Or.inr rfl
  | some a =>
    cases q with
    | none => exact Or.inl rfl
    | some b =>
      obtain ⟨N1, d1⟩ := a
      obtain ⟨N2, d2⟩ := b
      simp only [better]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl

theorem better_good {x : ℝ × ℝ} {ta tb : ℤ} {p q : Option (ℤ × ℤ)}
    (hp : Good x ta tb p) (hq : Good x ta tb q) : Good x ta tb (better p q) := by
  rcases better_eq p q with h | h <;> rw [h] <;> assumption

theorem pairBoth_good (u v : IC) (ta tb : ℤ) (x : ℝ × ℝ)
    (hu : u.Holds x) (hv : v.Holds x) : Good x ta tb (pairBoth u v ta tb) := by
  unfold pairBoth
  split_ifs
  · exact pairUpper_good u v ta tb x hu hv
  · exact pairUpper_good v u ta tb x hv hu

theorem scanPairs_good (u : IC) (ta tb : ℤ) (x : ℝ × ℝ) (hu : u.Holds x) :
    ∀ l : List IC, (∀ h ∈ l, h.Holds x) → Good x ta tb (scanPairs u ta tb l)
  | [], _ => by
    intro N d h
    simp [scanPairs] at h
  | v :: vs, hl => by
    simp only [scanPairs]
    have hv := hl v (by simp)
    exact better_good (pairBoth_good u v ta tb x hu hv)
      (scanPairs_good u ta tb x hu vs (fun h hh => hl h (List.mem_cons_of_mem _ hh)))

theorem findUpper_good : ∀ (hs : List IC) (ta tb : ℤ) (x : ℝ × ℝ), x ∈ Dom hs →
    Good x ta tb (findUpper hs ta tb)
  | [], _, _, _, _ => by
    intro N d h
    simp [findUpper] at h
  | u :: vs, ta, tb, x, hx => by
    simp only [findUpper]
    exact better_good
      (scanPairs_good u ta tb x (hx u (by simp)) vs (fun h hh => hx h (List.mem_cons_of_mem _ hh)))
      (findUpper_good vs ta tb x (fun h hh => hx h (List.mem_cons_of_mem _ hh)))

theorem gap_real (P Q N1 N2 d1 d2 L T : ℝ) (hd1 : 0 < d1) (hd2 : 0 < d2) (hL : 0 < L)
    (h1 : d1*P ≤ N1) (h2 : d2*(-Q) ≤ N2) (h : (N1*d2+N2*d1)*L < T*(d1*d2)) :
    (P-Q)*L < T := by
  have key : (P-Q)*(d1*d2) ≤ N1*d2+N2*d1 := by
    nlinarith [mul_le_mul_of_nonneg_right h1 hd2.le, mul_le_mul_of_nonneg_right h2 hd1.le]
  have h3 : (P-Q)*L*(d1*d2) < T*(d1*d2) := by
    calc (P-Q)*L*(d1*d2) = ((P-Q)*(d1*d2))*L := by ring
      _ ≤ (N1*d2+N2*d1)*L := mul_le_mul_of_nonneg_right key hL.le
      _ < T*(d1*d2) := h
  exact lt_of_mul_lt_mul_right h3 (mul_pos hd1 hd2).le

theorem gap_sound (ta tb : ℤ) (x y : ℝ × ℝ) (hi lo : Option (ℤ × ℤ)) (L T : ℤ)
    (hL : 0 < L) (hhi : Good y ta tb hi) (hlo : Good x (-ta) (-tb) lo)
    (h : gapOK hi lo L T = true) :
    (((ta:ℝ)*y.1+(tb:ℝ)*y.2)-((ta:ℝ)*x.1+(tb:ℝ)*x.2))*(L:ℝ) < (T:ℝ) := by
  match hi, lo, h, hhi, hlo with
  | some (N1, d1), some (N2, d2), h, hhi, hlo =>
    simp only [gapOK, decide_eq_true_eq] at h
    obtain ⟨hd1, h1⟩ := hhi N1 d1 rfl
    obtain ⟨hd2, h2⟩ := hlo N2 d2 rfl
    push_cast at h2
    have hR : (((N1:ℝ)*d2+N2*d1)*L) < (T:ℝ)*((d1:ℝ)*d2) := by exact_mod_cast h
    have hd1R : (0:ℝ) < d1 := by exact_mod_cast hd1
    have hd2R : (0:ℝ) < d2 := by exact_mod_cast hd2
    have hLR : (0:ℝ) < L := by exact_mod_cast hL
    exact gap_real _ _ _ _ _ _ _ _ hd1R hd2R hLR h1 (by linarith) hR

def Box.Good (bx : Box) (x : ℝ × ℝ) : Prop :=
  HalfPlaneInt.Good x 1 0 bx.xp ∧ HalfPlaneInt.Good x (-1) 0 bx.xm ∧
    HalfPlaneInt.Good x 0 1 bx.yp ∧ HalfPlaneInt.Good x 0 (-1) bx.ym

theorem mkBox_good (hs : List IC) (x : ℝ × ℝ) (hx : x ∈ Dom hs) : (mkBox hs).Good x :=
  ⟨findUpper_good hs 1 0 x hx, findUpper_good hs (-1) 0 x hx,
    findUpper_good hs 0 1 x hx, findUpper_good hs 0 (-1) x hx⟩

theorem selX_good (bx : Box) (x : ℝ × ℝ) (h : bx.Good x) (a N1 d1 : ℤ)
    (ho : selX bx a = some (N1, d1)) :
    0 < d1 ∧ (d1:ℝ)*((a:ℝ)*x.1) ≤ |(a:ℝ)| * (N1:ℝ) := by
  unfold selX at ho
  split_ifs at ho with ha
  · obtain ⟨hd, hb⟩ := h.1 N1 d1 ho
    refine ⟨hd, ?_⟩
    have haR : (0:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
    simp only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, add_zero] at hb
    rw [abs_of_nonneg haR]
    linarith [mul_le_mul_of_nonneg_left hb haR]
  · obtain ⟨hd, hb⟩ := h.2.1 N1 d1 ho
    refine ⟨hd, ?_⟩
    have haR : (a:ℝ) < 0 := by exact_mod_cast not_le.mp ha
    simp only [Int.cast_neg, Int.cast_one, Int.cast_zero, neg_mul, one_mul, zero_mul,
      add_zero] at hb
    rw [abs_of_neg haR]
    linarith [mul_le_mul_of_nonneg_left hb (neg_nonneg.mpr haR.le)]

theorem selY_good (bx : Box) (x : ℝ × ℝ) (h : bx.Good x) (b N2 d2 : ℤ)
    (ho : selY bx b = some (N2, d2)) :
    0 < d2 ∧ (d2:ℝ)*((b:ℝ)*x.2) ≤ |(b:ℝ)| * (N2:ℝ) := by
  unfold selY at ho
  split_ifs at ho with hb0
  · obtain ⟨hd, hb⟩ := h.2.2.1 N2 d2 ho
    refine ⟨hd, ?_⟩
    have hbR : (0:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb0
    simp only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, zero_add] at hb
    rw [abs_of_nonneg hbR]
    linarith [mul_le_mul_of_nonneg_left hb hbR]
  · obtain ⟨hd, hb⟩ := h.2.2.2 N2 d2 ho
    refine ⟨hd, ?_⟩
    have hbR : (b:ℝ) < 0 := by exact_mod_cast not_le.mp hb0
    simp only [Int.cast_neg, Int.cast_one, Int.cast_zero, neg_mul, one_mul, zero_mul,
      zero_add] at hb
    rw [abs_of_neg hbR]
    linarith [mul_le_mul_of_nonneg_left hb (neg_nonneg.mpr hbR.le)]

theorem boxUpper_good (bx : Box) (x : ℝ × ℝ) (h : bx.Good x) (a b : ℤ) :
    Good x a b (boxUpper bx a b) := by
  intro N d hN
  unfold boxUpper at hN
  rw [iabs_eq, iabs_eq] at hN
  split at hN
  · next N1 d1 N2 d2 h1 h2 =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hN
    obtain ⟨rfl, rfl⟩ := hN
    obtain ⟨hd1, hb1⟩ := selX_good bx x h a N1 d1 h1
    obtain ⟨hd2, hb2⟩ := selY_good bx x h b N2 d2 h2
    refine ⟨mul_pos hd1 hd2, ?_⟩
    have hd1R : (0:ℝ) < d1 := by exact_mod_cast hd1
    have hd2R : (0:ℝ) < d2 := by exact_mod_cast hd2
    push_cast
    linarith [mul_le_mul_of_nonneg_right hb1 hd2R.le, mul_le_mul_of_nonneg_right hb2 hd1R.le]
  · simp at hN

theorem axis_sound (S P : List IC) (bS bP : Box) (a b L T : ℤ) (hL : 0 < L)
    (h : axisOK S P bS bP a b L T = true) (x y : ℝ × ℝ) (hx : x ∈ Dom S) (hy : y ∈ Dom P)
    (hbx : bS.Good x) (hby : bP.Good y) :
    |(a:ℝ)*(y.1-x.1)+(b:ℝ)*(y.2-x.2)| * (L:ℝ) < (T:ℝ) := by
  simp only [axisOK, Bool.and_eq_true, Bool.or_eq_true] at h
  have h1 : (((a:ℝ)*y.1+(b:ℝ)*y.2)-((a:ℝ)*x.1+(b:ℝ)*x.2))*(L:ℝ) < (T:ℝ) := by
    rcases h.1 with hg | hg
    · exact gap_sound a b x y _ _ L T hL (boxUpper_good bP y hby a b)
        (boxUpper_good bS x hbx (-a) (-b)) hg
    · exact gap_sound a b x y _ _ L T hL (findUpper_good P a b y hy)
        (findUpper_good S (-a) (-b) x hx) hg
  have h2 : (((a:ℝ)*x.1+(b:ℝ)*x.2)-((a:ℝ)*y.1+(b:ℝ)*y.2))*(L:ℝ) < (T:ℝ) := by
    rcases h.2 with hg | hg
    · exact gap_sound a b y x _ _ L T hL (boxUpper_good bS x hbx a b)
        (boxUpper_good bP y hby (-a) (-b)) hg
    · exact gap_sound a b y x _ _ L T hL (findUpper_good S a b x hx)
        (findUpper_good P (-a) (-b) y hy) hg
  rcases abs_cases ((a:ℝ)*(y.1-x.1)+(b:ℝ)*(y.2-x.2)) with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he]; linarith
  · rw [he]; linarith

theorem cross_real (C S cd E F ed : ℤ) (hcd : 0 < cd) (hed : 0 < ed) :
    |(C:ℝ)/cd*((E:ℝ)/ed)+(S:ℝ)/cd*((F:ℝ)/ed)|+|(C:ℝ)/cd*((F:ℝ)/ed)-(S:ℝ)/cd*((E:ℝ)/ed)| =
      ((IntSupport.crossNum C S E F : ℤ) : ℝ)/((cd:ℝ)*ed) := by
  have hcdR : (0:ℝ) < (cd:ℝ) := by exact_mod_cast hcd
  have hedR : (0:ℝ) < (ed:ℝ) := by exact_mod_cast hed
  have hp : (0:ℝ) < (cd:ℝ)*ed := mul_pos hcdR hedR
  have e1 : (C:ℝ)/cd*((E:ℝ)/ed)+(S:ℝ)/cd*((F:ℝ)/ed) = ((C:ℝ)*E+S*F)/((cd:ℝ)*ed) := by
    field_simp
  have e2 : (C:ℝ)/cd*((F:ℝ)/ed)-(S:ℝ)/cd*((E:ℝ)/ed) = ((C:ℝ)*F-S*E)/((cd:ℝ)*ed) := by
    field_simp
  rw [e1, e2, abs_div, abs_div, abs_of_pos hp, ← add_div]
  simp only [IntSupport.crossNum]
  push_cast
  rfl

theorem no_sep (A z cd L T : ℝ) (hcd : 0 < cd) (hL : 0 < L) (hkey : A*cd*L = T)
    (hz : |z| * L < T) : ¬ A ≤ |z|/cd := by
  intro hs
  have h5 := mul_le_mul_of_nonneg_right hs (mul_pos hcd hL).le
  have h6 : |z| / cd * (cd*L) = |z| * L := by field_simp
  have h7 : A*(cd*L) = T := by rw [← hkey]; ring
  rw [h6, h7] at h5
  linarith

theorem collide_cores (S P : List IC) (bS bP : Box) (C Sn cd H hd E F ed K kd : ℤ)
    (hc : collide S P bS bP C Sn cd H hd E F ed K kd = true)
    (x y : ℝ × ℝ) (hx : x ∈ Dom S) (hy : y ∈ Dom P)
    (hbx : bS.Good x) (hby : bP.Good y) :
    ¬ Disjoint (interior (core x.1 x.2 ((C:ℝ)/cd) ((Sn:ℝ)/cd) ((H:ℝ)/hd)))
      (interior (core y.1 y.2 ((E:ℝ)/ed) ((F:ℝ)/ed) ((K:ℝ)/kd))) := by
  simp only [collide, crossNum_eq, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨hcd, hhd, hed, hkd, hH, hCS, hK, hEF⟩, h0⟩, h1⟩, h2⟩, h3⟩ := hc
  have hL : (0:ℤ) < 2*hd*cd*kd*ed := by positivity
  have hcdR : (0:ℝ) < (cd:ℝ) := by exact_mod_cast hcd
  have hhdR : (0:ℝ) < (hd:ℝ) := by exact_mod_cast hhd
  have hedR : (0:ℝ) < (ed:ℝ) := by exact_mod_cast hed
  have hkdR : (0:ℝ) < (kd:ℝ) := by exact_mod_cast hkd
  have hHR : (0:ℝ) < (H:ℝ) := by exact_mod_cast hH
  have hKR : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have hCSR : (0:ℝ) < (C:ℝ)*C+Sn*Sn := by exact_mod_cast hCS
  have hEFR : (0:ℝ) < (E:ℝ)*E+F*F := by exact_mod_cast hEF
  have hLR : (0:ℝ) < 2*(hd:ℝ)*cd*kd*ed := by positivity
  have a0 := axis_sound S P bS bP C Sn _ _ hL h0 x y hx hy hbx hby
  have a1 := axis_sound S P bS bP (-Sn) C _ _ hL h1 x y hx hy hbx hby
  have a2 := axis_sound S P bS bP E F _ _ hL h2 x y hx hy hbx hby
  have a3 := axis_sound S P bS bP (-F) E _ _ hL h3 x y hx hy hbx hby
  push_cast at a0 a1 a2 a3
  have hn : (0:ℝ) < ((C:ℝ)/cd)^2+((Sn:ℝ)/cd)^2 := by
    have e : ((C:ℝ)/cd)^2+((Sn:ℝ)/cd)^2 = ((C:ℝ)*C+Sn*Sn)/((cd:ℝ)*cd) := by field_simp
    rw [e]; exact div_pos hCSR (mul_pos hcdR hcdR)
  have hm : (0:ℝ) < ((E:ℝ)/ed)^2+((F:ℝ)/ed)^2 := by
    have e : ((E:ℝ)/ed)^2+((F:ℝ)/ed)^2 = ((E:ℝ)*E+F*F)/((ed:ℝ)*ed) := by field_simp
    rw [e]; exact div_pos hEFR (mul_pos hedR hedR)
  intro hdis
  have hsep := CoreSAT.core_disjoint_axis x y ((C:ℝ)/cd) ((Sn:ℝ)/cd) ((H:ℝ)/hd)
    ((E:ℝ)/ed) ((F:ℝ)/ed) ((K:ℝ)/kd) (div_pos hHR hhdR) hn (div_pos hKR hkdR) hm hdis
  unfold CoreSAT.RawAxisSeparated at hsep
  rw [cross_real C Sn cd E F ed hcd hed] at hsep
  rcases hsep with hs | hs | hs | hs
  · have e : (C:ℝ)/cd*(y.1-x.1)+(Sn:ℝ)/cd*(y.2-x.2) =
        ((C:ℝ)*(y.1-x.1)+Sn*(y.2-x.2))/cd := by ring
    rw [e, abs_div, abs_of_pos hcdR] at hs
    exact no_sep _ _ _ _ _ hcdR hLR (by field_simp) a0 hs
  · have e : (C:ℝ)/cd*(y.2-x.2)-(Sn:ℝ)/cd*(y.1-x.1) =
        (-(Sn:ℝ)*(y.1-x.1)+C*(y.2-x.2))/cd := by ring
    rw [e, abs_div, abs_of_pos hcdR] at hs
    exact no_sep _ _ _ _ _ hcdR hLR (by field_simp) a1 hs
  · have e : (E:ℝ)/ed*(y.1-x.1)+(F:ℝ)/ed*(y.2-x.2) =
        ((E:ℝ)*(y.1-x.1)+F*(y.2-x.2))/ed := by ring
    rw [e, abs_div, abs_of_pos hedR] at hs
    exact no_sep _ _ _ _ _ hedR hLR (by field_simp) a2 hs
  · have e : (E:ℝ)/ed*(y.2-x.2)-(F:ℝ)/ed*(y.1-x.1) =
        (-(F:ℝ)*(y.1-x.1)+E*(y.2-x.2))/ed := by ring
    rw [e, abs_div, abs_of_pos hedR] at hs
    exact no_sep _ _ _ _ _ hedR hLR (by field_simp) a3 hs

/-- The same conclusion for the actual unit squares over two certified angle rows. -/
theorem collide_sound (S P : List IC) (bS bP : Box) (r t : CoreRowCertificate) (nr nt : ℕ)
    (C Sn cd H hd E F ed K kd : ℤ)
    (hr : r.check nr = true) (ht : t.check nt = true)
    (hrc : r.c = (C:ℚ)/cd) (hrs : r.s = (Sn:ℚ)/cd) (hrh : r.side = (H:ℚ)/hd)
    (htc : t.c = (E:ℚ)/ed) (hts : t.s = (F:ℚ)/ed) (hth : t.side = (K:ℚ)/kd)
    (hc : collide S P bS bP C Sn cd H hd E F ed K kd = true)
    (x y : ℝ × ℝ) (hx : x ∈ Dom S) (hy : y ∈ Dom P)
    (hbx : bS.Good x) (hby : bP.Good y)
    (θ φ : ℝ) (hθ : θ ∈ Set.Icc (r.lo : ℝ) (r.hi : ℝ))
    (hφ : φ ∈ Set.Icc (t.lo : ℝ) (t.hi : ℝ)) :
    ¬ Disjoint (interior (Sq17.sq x.1 x.2 (Real.cos θ) (Real.sin θ)))
      (interior (Sq17.sq y.1 y.2 (Real.cos φ) (Real.sin φ))) := by
  intro hdis
  apply collide_cores S P bS bP C Sn cd H hd E F ed K kd hc x y hx hy hbx hby
  have h1 := r.check_sound nr hr x.1 x.2 θ hθ
  have h2 := t.check_sound nt ht y.1 y.2 φ hφ
  rw [hrc, hrs, hrh] at h1
  rw [htc, hts, hth] at h2
  push_cast at h1 h2
  exact hdis.mono (interior_mono h1) (interior_mono h2)

end Sq17.Propagation.HalfPlaneInt

#print axioms Sq17.Propagation.HalfPlaneInt.collide_sound
