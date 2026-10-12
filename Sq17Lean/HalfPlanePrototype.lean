import Sq17Lean.PropagationSupportCollision
import Sq17Lean.PropagationPolygonPrune
import Mathlib.Tactic.Linarith

/-! Experimental half-plane certificate backend. All finite checks use ordinary
kernel reduction. This module does not assert acceptance of a complete trace. -/
namespace Sq17.Propagation.HalfPlanePrototype

structure Constraint where
  a : ℚ
  b : ℚ
  q : ℚ
  deriving DecidableEq, Repr

def Constraint.Holds (h : Constraint) (x : ℝ × ℝ) : Prop :=
  (h.a : ℝ) * x.1 + (h.b : ℝ) * x.2 ≤ (h.q : ℝ)

def Domain (hs : List Constraint) : Set (ℝ × ℝ) :=
  {x | ∀ h ∈ hs, h.Holds x}

/-- Denominator-free two-constraint dual check. No optimizer is trusted. -/
def twoCheck (u v t : Constraint) : Bool :=
  let d := u.a * v.b - v.a * u.b
  let l := t.a * v.b - v.a * t.b
  let m := u.a * t.b - t.a * u.b
  decide (0 < d ∧ 0 ≤ l ∧ 0 ≤ m ∧ l*u.q + m*v.q ≤ d*t.q)

theorem twoCheck_sound (u v t : Constraint) (hc : twoCheck u v t = true)
    (x : ℝ × ℝ) (hu : u.Holds x) (hv : v.Holds x) : t.Holds x := by
  have hq : 0 < u.a*v.b-v.a*u.b ∧ 0 ≤ t.a*v.b-v.a*t.b ∧
      0 ≤ u.a*t.b-t.a*u.b ∧
      (t.a*v.b-v.a*t.b)*u.q+(u.a*t.b-t.a*u.b)*v.q ≤
        (u.a*v.b-v.a*u.b)*t.q := of_decide_eq_true hc
  have hr : (0 : ℝ) < (u.a : ℝ)*v.b-v.a*u.b ∧
      0 ≤ (t.a : ℝ)*v.b-v.a*t.b ∧ 0 ≤ (u.a : ℝ)*t.b-t.a*u.b ∧
      ((t.a : ℝ)*v.b-v.a*t.b)*u.q+((u.a : ℝ)*t.b-t.a*u.b)*v.q ≤
        ((u.a : ℝ)*v.b-v.a*u.b)*t.q := by exact_mod_cast hq
  unfold Constraint.Holds at *
  have hh := add_le_add (mul_le_mul_of_nonneg_left hu hr.2.1)
    (mul_le_mul_of_nonneg_left hv hr.2.2.1)
  have hid : ((t.a : ℝ)*v.b-v.a*t.b)*((u.a : ℝ)*x.1+u.b*x.2) +
      ((u.a : ℝ)*t.b-t.a*u.b)*((v.a : ℝ)*x.1+v.b*x.2) =
      ((u.a : ℝ)*v.b-v.a*u.b)*((t.a : ℝ)*x.1+t.b*x.2) := by ring
  rw [hid] at hh
  exact (mul_le_mul_iff_right₀ hr.1).mp (hh.trans hr.2.2.2)

structure Witness where
  first : ℕ
  second : ℕ
  deriving DecidableEq, Repr

def boundCheck (hs : List Constraint) (t : Constraint) (w : Witness) : Bool :=
  match hs[w.first]?, hs[w.second]? with
  | some u, some v => twoCheck u v t
  | _, _ => false

theorem boundCheck_sound (hs : List Constraint) (t : Constraint) (w : Witness)
    (hc : boundCheck hs t w = true) (x : ℝ × ℝ) (hx : x ∈ Domain hs) : t.Holds x := by
  unfold boundCheck at hc
  split at hc
  next u v hu hv =>
    exact twoCheck_sound u v t hc x
      (hx u (List.mem_of_getElem? hu)) (hx v (List.mem_of_getElem? hv))
  next => contradiction

/-- Every target half-plane has a checked implication from the source domain. -/
def coverCheck (source : List Constraint) (targets : List (Constraint × Witness)) : Bool :=
  targets.all fun t => boundCheck source t.1 t.2

theorem coverCheck_sound (source : List Constraint) (targets : List (Constraint × Witness))
    (hc : coverCheck source targets = true) : Domain source ⊆ Domain (targets.map Prod.fst) := by
  intro x hx t ht
  rcases List.mem_map.mp ht with ⟨tw,htw,rfl⟩
  exact boundCheck_sound source tw.1 tw.2 ((List.all_eq_true.mp hc) tw htw) x hx

/-- Checked transfer after adding a cut. This does not assume polygons are nested. -/
theorem cut_transfer (source : List Constraint) (cut : Constraint)
    (targets : List (Constraint × Witness))
    (hc : coverCheck (cut :: source) targets = true)
    (x : ℝ × ℝ) (hx : x ∈ Domain source) (hcut : cut.Holds x) :
    x ∈ Domain (targets.map Prod.fst) := by
  apply coverCheck_sound (cut :: source) targets hc
  intro h hh
  rcases List.mem_cons.mp hh with rfl | hh
  · exact hcut
  · exact hx h hh

end Sq17.Propagation.HalfPlanePrototype
#print axioms Sq17.Propagation.HalfPlanePrototype.twoCheck_sound
#print axioms Sq17.Propagation.HalfPlanePrototype.boundCheck_sound
#print axioms Sq17.Propagation.HalfPlanePrototype.cut_transfer

namespace Sq17.Propagation.HalfPlanePrototype

structure AxisCertificate where
  bounds : SupportInterval
  sourceLo : Witness
  sourceHi : Witness
  partnerLo : Witness
  partnerHi : Witness

def axisCheck (source partner : List Constraint) (a b threshold : ℚ)
    (cert : AxisCertificate) : Bool :=
  boundCheck source ⟨-a,-b,-cert.bounds.sourceLo⟩ cert.sourceLo &&
  boundCheck source ⟨a,b,cert.bounds.sourceHi⟩ cert.sourceHi &&
  boundCheck partner ⟨-a,-b,-cert.bounds.partnerLo⟩ cert.partnerLo &&
  boundCheck partner ⟨a,b,cert.bounds.partnerHi⟩ cert.partnerHi &&
  decide (cert.bounds.partnerHi-cert.bounds.sourceLo < threshold ∧
    cert.bounds.sourceHi-cert.bounds.partnerLo < threshold)

theorem axisCheck_sound (source partner : List Constraint) (a b threshold : ℚ)
    (cert : AxisCertificate) (hc : axisCheck source partner a b threshold cert = true)
    (x y : ℝ × ℝ) (hx : x ∈ Domain source) (hy : y ∈ Domain partner) :
    |(a : ℝ)*(y.1-x.1)+(b : ℝ)*(y.2-x.2)| < (threshold : ℝ) := by
  simp only [axisCheck,Bool.and_eq_true] at hc
  rcases hc with ⟨⟨⟨⟨hl,hu⟩,kl⟩,ku⟩,hg⟩
  have hsl := boundCheck_sound _ _ _ hl x hx
  have hsu := boundCheck_sound _ _ _ hu x hx
  have hpl := boundCheck_sound _ _ _ kl y hy
  have hpu := boundCheck_sound _ _ _ ku y hy
  have hgap : (cert.bounds.partnerHi : ℝ)-cert.bounds.sourceLo < threshold ∧
      (cert.bounds.sourceHi : ℝ)-cert.bounds.partnerLo < threshold := by
    exact_mod_cast (of_decide_eq_true hg :
      cert.bounds.partnerHi-cert.bounds.sourceLo < threshold ∧
      cert.bounds.sourceHi-cert.bounds.partnerLo < threshold)
  simp only [Constraint.Holds,Rat.cast_neg] at hsl hsu hpl hpu
  apply abs_lt.mpr
  constructor <;> linarith

def collisionCheck (source partner : List Constraint) (c s h e f k : ℚ)
    (cert : Fin 4 → AxisCertificate) : Bool :=
  decide (0 < h ∧ 0 < c^2+s^2 ∧ 0 < k ∧ 0 < e^2+f^2) &&
  (List.finRange 4).all (fun i => axisCheck source partner
    (coreSupportAxes c s e f i).1 (coreSupportAxes c s e f i).2
    (coreSupportThresholds c s h e f k i) (cert i))

theorem collisionCheck_cores (source partner : List Constraint) (c s h e f k : ℚ)
    (cert : Fin 4 → AxisCertificate)
    (hc : collisionCheck source partner c s h e f k cert = true)
    (x y : ℝ × ℝ) (hx : x ∈ Domain source) (hy : y ∈ Domain partner) :
    ¬ Disjoint (interior (core x.1 x.2 c s h))
      (interior (core y.1 y.2 e f k)) := by
  have hpQ : 0 < h ∧ 0 < c^2+s^2 ∧ 0 < k ∧ 0 < e^2+f^2 :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
  have hp : (0 : ℝ) < h ∧ 0 < (c : ℝ)^2+(s : ℝ)^2 ∧
      0 < (k : ℝ) ∧ 0 < (e : ℝ)^2+(f : ℝ)^2 := by exact_mod_cast hpQ
  have ha (i : Fin 4) := axisCheck_sound source partner
    (coreSupportAxes c s e f i).1 (coreSupportAxes c s e f i).2
    (coreSupportThresholds c s h e f k i) (cert i)
    ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).2) i (by simp)) x y hx hy
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  dsimp [coreSupportAxes,coreSupportThresholds] at h0 h1 h2 h3
  push_cast at h0 h1 h2 h3
  intro hd
  have hs := CoreSAT.core_disjoint_axis x y c s h e f k
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 hd
  have he1 : -(s : ℝ)*(y.1-x.1)+(c : ℝ)*(y.2-x.2) =
      (c : ℝ)*(y.2-x.2)-(s : ℝ)*(y.1-x.1) := by ring
  have he3 : -(f : ℝ)*(y.1-x.1)+(e : ℝ)*(y.2-x.2) =
      (e : ℝ)*(y.2-x.2)-(f : ℝ)*(y.1-x.1) := by ring
  rw [he1] at h1
  rw [he3] at h3
  rcases hs with hs|hs|hs|hs <;> linarith

theorem collisionCheck_sound (source partner : List Constraint)
    (r t : CoreRowCertificate) (nr nt : ℕ) (cert : Fin 4 → AxisCertificate)
    (hr : r.check nr = true) (ht : t.check nt = true)
    (hc : collisionCheck source partner r.c r.s r.side t.c t.s t.side cert = true)
    (x y : ℝ × ℝ) (hx : x ∈ Domain source) (hy : y ∈ Domain partner)
    (θ φ : ℝ) (hθ : θ ∈ Set.Icc (r.lo : ℝ) (r.hi : ℝ))
    (hφ : φ ∈ Set.Icc (t.lo : ℝ) (t.hi : ℝ)) :
    ¬ Disjoint (interior (Sq17.sq x.1 x.2 (Real.cos θ) (Real.sin θ)))
      (interior (Sq17.sq y.1 y.2 (Real.cos φ) (Real.sin φ))) := by
  intro hd
  apply collisionCheck_cores source partner r.c r.s r.side t.c t.s t.side cert hc x y hx hy
  exact hd.mono (interior_mono (r.check_sound nr hr x.1 x.2 θ hθ))
    (interior_mono (t.check_sound nt ht y.1 y.2 φ hφ))

end Sq17.Propagation.HalfPlanePrototype
#print axioms Sq17.Propagation.HalfPlanePrototype.collisionCheck_sound

namespace Sq17.Propagation.HalfPlanePrototype

def rowRegion (hs : List Constraint) (r : CoreRowCertificate) : Set AnglePose :=
  {p | p.center ∈ Domain hs ∧ p.angle ∈ Set.Icc (r.lo : ℝ) (r.hi : ℝ)}

structure Partner where
  constraints : List Constraint
  row : CoreRowCertificate
  cert : Fin 4 → AxisCertificate

def batchCheck (source : List Constraint) (r : CoreRowCertificate)
    (partners : List Partner) (n : ℕ) : Bool :=
  r.check n && partners.all (fun t => t.row.check n &&
    collisionCheck source t.constraints r.c r.s r.side t.row.c t.row.s t.row.side t.cert)

def partnerRegion (partners : List Partner) : Set AnglePose :=
  {p | ∃ t ∈ partners, p ∈ rowRegion t.constraints t.row}

theorem batchCheck_incompatible (source : List Constraint) (r : CoreRowCertificate)
    (partners : List Partner) (n : ℕ) (hc : batchCheck source r partners n = true)
    (p q : AnglePose) (hp : p ∈ rowRegion source r) (hq : q ∈ partnerRegion partners) :
    ¬ Disjoint (interior p.square) (interior q.square) := by
  rcases hq with ⟨t,ht,hq⟩
  have hh := Bool.and_eq_true_iff.mp hc
  have htcheck := Bool.and_eq_true_iff.mp ((List.all_eq_true.mp hh.2) t ht)
  exact collisionCheck_sound source t.constraints r t.row n n t.cert hh.1 htcheck.1
    htcheck.2 p.center q.center hp.1 hq.1 p.angle q.angle hp.2 hq.2

def Constraint.opposite (h : Constraint) : Constraint := ⟨-h.a,-h.b,-h.q⟩

/-- A complete pair cut over half-plane domains. All partner alternatives must
be covered; a successful single collision certificate is not enough. -/
theorem cut_preserves {Owner : Type*} [DecidableEq Owner]
    (D : Owner → Set AnglePose) (p : Owner → AnglePose) (i j : Owner)
    (rest : Set AnglePose) (source : List Constraint) (keep : Constraint)
    (r : CoreRowCertificate) (partners : List Partner) (n : ℕ)
    (hc : batchCheck (source ++ [keep.opposite]) r partners n = true)
    (hrep : Represents D p)
    (hpair : Disjoint (interior (p i).square) (interior (p j).square))
    (hsource : D i ⊆ rest ∪ rowRegion source r)
    (hpartner : D j ⊆ partnerRegion partners) :
    Represents (Function.update D i (rest ∪ rowRegion (source ++ [keep]) r)) p := by
  apply pair_prune D p (fun x y => Disjoint (interior x.square) (interior y.square))
    i j _ hrep hpair
  intro x hx hnot y hy hd
  rcases hsource hx with hxrest | hxrow
  · exact hnot (Or.inl hxrest)
  · have hn : ¬ keep.Holds x.center := by
      intro hk
      apply hnot
      right
      refine ⟨?_,hxrow.2⟩
      intro h hh
      rcases List.mem_append.mp hh with hh | hh
      · exact hxrow.1 h hh
      · have he : h = keep := by simpa using hh
        subst h
        exact hk
    have ho : keep.opposite.Holds x.center := by
      dsimp [Constraint.Holds,Constraint.opposite] at *
      push_cast
      push_neg at hn
      linarith
    apply batchCheck_incompatible (source ++ [keep.opposite]) r partners n hc x y ?_
      (hpartner hy) hd
    refine ⟨?_,hxrow.2⟩
    intro h hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hxrow.1 h hh
    · have he : h = keep.opposite := by simpa using hh
      subst h
      exact ho

def verticesCheck (vertices : List (ℚ × ℚ)) (hs : List Constraint) : Bool :=
  hs.all fun h => vertices.all fun v => decide (h.a*v.1+h.b*v.2 ≤ h.q)

theorem verticesCheck_sound (vertices : List (ℚ × ℚ)) (hs : List Constraint)
    (hc : verticesCheck vertices hs = true) :
    convexHull ℝ (realPoint '' {v | v ∈ vertices}) ⊆ Domain hs := by
  intro x hx h hh
  have hverts := List.all_eq_true.mp ((List.all_eq_true.mp hc) h hh)
  have hsub : convexHull ℝ (realPoint '' {v | v ∈ vertices}) ⊆
      {z | (h.a : ℝ)*z.1+(h.b : ℝ)*z.2 ≤ (h.q : ℝ)} := by
    apply convexHull_min ?_ (convex_halfSpace_le
      ⟨(dotMap (h.a : ℝ) (h.b : ℝ)).map_add,(dotMap (h.a : ℝ) (h.b : ℝ)).map_smul⟩ _)
    rintro _ ⟨v,hv,rfl⟩
    change (h.a : ℝ)*(v.1 : ℝ)+(h.b : ℝ)*(v.2 : ℝ) ≤ (h.q : ℝ)
    exact_mod_cast (of_decide_eq_true (hverts v hv) : h.a*v.1+h.b*v.2 ≤ h.q)
  exact hsub hx

end Sq17.Propagation.HalfPlanePrototype
#print axioms Sq17.Propagation.HalfPlanePrototype.cut_preserves
#print axioms Sq17.Propagation.HalfPlanePrototype.verticesCheck_sound
