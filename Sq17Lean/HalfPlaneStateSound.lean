import Sq17Lean.HalfPlaneState
import Sq17Lean.PropagationWallBaseline
import Sq17Lean.PropagationWallReplace

/-! Soundness of the half-plane trace checker.

If the table of angle rows is certified and the checker accepts a list of steps
ending with an owner that has no live row, then no packing is represented by the
initial state. The initial state is an explicit premise here; binding it to the
cell seeding is a separate step. -/
namespace Sq17.Propagation.HalfPlaneState
open Sq17.Propagation.HalfPlaneInt

/-- An entry is backed by a checked core row and a checked wall row. -/
def Entry.Valid (e : Entry) (n : ℕ) : Prop :=
  (∃ r : CoreRowCertificate, r.check n = true ∧ r.lo = e.lo ∧ r.hi = e.hi ∧
    r.c = (e.C:ℚ)/e.cd ∧ r.s = (e.S:ℚ)/e.cd ∧ r.side = (e.H:ℚ)/e.hd) ∧
  (∃ w : WallRowCertificate, w.check n = true ∧ w.lo = e.lo ∧ w.hi = e.hi ∧ w.span = e.span)

def TableValid (T : Array Entry) (n : ℕ) : Prop :=
  ∀ (k : ℕ) (e : Entry), T[k]? = some e → e.Valid n

def rowRegion (T : Array Entry) (r : HRow) : Set AnglePose :=
  {p | ∃ e, T[r.e]? = some e ∧ p.center ∈ Dom r.cons ∧ r.box.Good p.center ∧
    p.angle ∈ Set.Icc (e.lo:ℝ) (e.hi:ℝ)}

def rowsRegion (T : Array Entry) (rows : List HRow) : Set AnglePose :=
  {p | ∃ r ∈ rows, p ∈ rowRegion T r}

/-- Every owner's pose lies in one of its live rows. -/
def Rep (T : Array Entry) (S : HState) (p : ℕ → AnglePose) : Prop :=
  ∀ i, i < S.length → p i ∈ rowsRegion T (rowsOf S i)

def Packing (N : ℕ) (p : ℕ → AnglePose) : Prop :=
  ∀ i j, i < N → j < N → i ≠ j → Disjoint (interior (p i).square) (interior (p j).square)

def Fits (N : ℕ) (side shift : ℚ) (p : ℕ → AnglePose) : Prop :=
  ∀ i, i < N → (p i).square ⊆ traceContainer side shift

theorem dropBits_mem : ∀ (l : List IC) (m : ℕ) (c : IC), c ∈ dropBits l m → c ∈ l
  | [], _, c, h => by simp [dropBits] at h
  | a :: l, m, c, h => by
    simp only [dropBits] at h
    split_ifs at h
    · exact List.mem_cons_of_mem _ (dropBits_mem l (m/2) c h)
    · rcases List.mem_cons.mp h with h | h
      · rw [h]; simp
      · exact List.mem_cons_of_mem _ (dropBits_mem l (m/2) c h)

theorem rowsOf_lt {S : HState} {i k : ℕ} {r : HRow} (h : (rowsOf S i)[k]? = some r) :
    i < S.length := by
  by_contra hn
  have h0 : rowsOf S i = [] := by
    simp [rowsOf, List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hn)]
  rw [h0] at h
  simp at h

theorem length_splice (S : HState) (i k : ℕ) (new : List HRow) :
    (splice S i k new).length = S.length := by
  simp [splice]

theorem rowsOf_splice_self (S : HState) (i k : ℕ) (new : List HRow) (h : i < S.length) :
    rowsOf (splice S i k new) i =
      (rowsOf S i).take k ++ new ++ (rowsOf S i).drop (k+1) := by
  unfold splice
  generalize (rowsOf S i).take k ++ new ++ (rowsOf S i).drop (k+1) = v
  simp [rowsOf, List.getD_eq_getElem?_getD, h]

theorem rowsOf_splice_ne (S : HState) (i k : ℕ) (new : List HRow) (j : ℕ) (h : j ≠ i) :
    rowsOf (splice S i k new) j = rowsOf S j := by
  unfold splice
  generalize (rowsOf S i).take k ++ new ++ (rowsOf S i).drop (k+1) = v
  simp [rowsOf, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem rows_split : ∀ {rows : List HRow} {k : ℕ} {r : HRow}, rows[k]? = some r →
    rows = rows.take k ++ r :: rows.drop (k+1)
  | [], _, _, h => by simp at h
  | a :: t, 0, r, h => by
    rw [List.getElem?_cons_zero] at h
    cases h
    rfl
  | a :: t, k+1, r, h => by
    rw [List.getElem?_cons_succ] at h
    show a :: t = a :: (t.take k ++ r :: t.drop (k+1))
    rw [← rows_split h]

theorem mem_rowsRegion_append {T : Array Entry} {a b : List HRow} {p : AnglePose} :
    p ∈ rowsRegion T (a ++ b) ↔ p ∈ rowsRegion T a ∨ p ∈ rowsRegion T b := by
  constructor
  · rintro ⟨r, hr, hp⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact Or.inl ⟨r, hr, hp⟩
    · exact Or.inr ⟨r, hr, hp⟩
  · rintro (⟨r, hr, hp⟩ | ⟨r, hr, hp⟩)
    · exact ⟨r, List.mem_append.mpr (Or.inl hr), hp⟩
    · exact ⟨r, List.mem_append.mpr (Or.inr hr), hp⟩

/-- Replacing one row is sound when every pose of the owner in the old row lies
in the new rows. -/
theorem splice_sound (T : Array Entry) (S : HState) (i k : ℕ) (r : HRow) (new : List HRow)
    (p : ℕ → AnglePose) (hk : (rowsOf S i)[k]? = some r) (hrep : Rep T S p)
    (hkey : p i ∈ rowRegion T r → p i ∈ rowsRegion T new) :
    Rep T (splice S i k new) p := by
  intro j hj
  rw [length_splice] at hj
  by_cases hji : j = i
  · subst hji
    rw [rowsOf_splice_self S j k new hj]
    have h0 := hrep j hj
    have e := rows_split hk
    generalize rowsOf S j = rows at *
    rw [e] at h0
    rcases mem_rowsRegion_append.mp h0 with h1 | ⟨r', hr', hp⟩
    · exact mem_rowsRegion_append.mpr (Or.inl (mem_rowsRegion_append.mpr (Or.inl h1)))
    · rcases List.mem_cons.mp hr' with hr' | hr'
      · rw [hr'] at hp
        exact mem_rowsRegion_append.mpr (Or.inl (mem_rowsRegion_append.mpr (Or.inr (hkey hp))))
      · exact mem_rowsRegion_append.mpr (Or.inr ⟨r', hr', hp⟩)
  · rw [rowsOf_splice_ne S i k new j hji]
    exact hrep j hj

theorem collideRows_sound (T : Array Entry) (hT : TableValid T 44) (cons : List IC)
    (bx : Box) (es : Entry) (rows : List HRow) (ke : ℕ) (hes : T[ke]? = some es)
    (hc : collideRows T cons bx es rows = true)
    (x : AnglePose) (hx : x.center ∈ Dom cons) (hbx : bx.Good x.center)
    (hxa : x.angle ∈ Set.Icc (es.lo:ℝ) (es.hi:ℝ))
    (y : AnglePose) (hy : y ∈ rowsRegion T rows) :
    ¬ Disjoint (interior x.square) (interior y.square) := by
  obtain ⟨t, ht, et, het, hyc, hyb, hya⟩ := hy
  have h1 := List.all_eq_true.mp hc t ht
  simp only [het] at h1
  obtain ⟨⟨r, hr, hrlo, hrhi, hrc, hrs, hrh⟩, _⟩ := hT ke es hes
  obtain ⟨⟨r2, hr2, h2lo, h2hi, h2c, h2s, h2h⟩, _⟩ := hT t.e et het
  exact collide_sound cons t.cons bx t.box r r2 44 44 es.C es.S es.cd es.H es.hd
    et.C et.S et.cd et.H et.hd hr hr2 hrc hrs hrh h2c h2s h2h h1 x.center y.center hx hyc
    hbx hyb x.angle y.angle (by rw [hrlo, hrhi]; exact hxa) (by rw [h2lo, h2hi]; exact hya)

theorem wallOK_sound (e : Entry) (he : e.Valid 44) (side shift : ℚ) (c : IC)
    (hc : wallOK e.span side shift c = true) (x : AnglePose)
    (hang : x.angle ∈ Set.Icc (e.lo:ℝ) (e.hi:ℝ))
    (hfit : x.square ⊆ traceContainer side shift) : c.Holds x.center := by
  obtain ⟨_, w, hw, hlo, hhi, hspan⟩ := he
  have hb := w.center_bounds_max_translated 44 hw x.center.1 x.center.2 x.angle side shift
    (by rw [hlo, hhi]; exact hang) hfit
  rw [hspan] at hb
  simp only [wallOK, halfSpan_eq, Bool.or_eq_true, decide_eq_true_eq] at hc
  unfold IC.Holds
  rcases hc with ((⟨hb0, ha, hq⟩ | ⟨hb0, ha, hq⟩) | ⟨ha0, hbb, hq⟩) | ⟨ha0, hbb, hq⟩
  · have hqR : (c.a:ℝ)*(max 1 (e.span:ℝ)/2-shift) ≤ c.q := by exact_mod_cast hq
    have haR : (c.a:ℝ) ≤ 0 := by exact_mod_cast ha.le
    have hz : (c.b:ℝ) = 0 := by exact_mod_cast hb0
    rw [hz]
    linarith [mul_le_mul_of_nonpos_left hb.1 haR]
  · have hqR : (c.a:ℝ)*(side+shift-max 1 (e.span:ℝ)/2) ≤ c.q := by exact_mod_cast hq
    have haR : (0:ℝ) ≤ (c.a:ℝ) := by exact_mod_cast ha.le
    have hz : (c.b:ℝ) = 0 := by exact_mod_cast hb0
    rw [hz]
    linarith [mul_le_mul_of_nonneg_left hb.2.1 haR]
  · have hqR : (c.b:ℝ)*(max 1 (e.span:ℝ)/2-shift) ≤ c.q := by exact_mod_cast hq
    have hbR : (c.b:ℝ) ≤ 0 := by exact_mod_cast hbb.le
    have hz : (c.a:ℝ) = 0 := by exact_mod_cast ha0
    rw [hz]
    linarith [mul_le_mul_of_nonpos_left hb.2.2.1 hbR]
  · have hqR : (c.b:ℝ)*(side+shift-max 1 (e.span:ℝ)/2) ≤ c.q := by exact_mod_cast hq
    have hbR : (0:ℝ) ≤ (c.b:ℝ) := by exact_mod_cast hbb.le
    have hz : (c.a:ℝ) = 0 := by exact_mod_cast ha0
    rw [hz]
    linarith [mul_le_mul_of_nonneg_left hb.2.2.2 hbR]

theorem emptyOK_sound (cons : List IC) (h : emptyOK cons = true) (x : ℝ × ℝ) :
    x ∉ Dom cons := by
  intro hx
  simp only [emptyOK, List.any_eq_true] at h
  obtain ⟨c, hc, hm⟩ := h
  have hg := findUpper_good cons (-c.a) (-c.b) x hx
  split at hm
  · next N d heq =>
    obtain ⟨hd, hb⟩ := hg N d heq
    have hlt : N < -c.q*d := of_decide_eq_true hm
    have hcx := hx c hc
    unfold IC.Holds at hcx
    have hdR : (0:ℝ) < d := by exact_mod_cast hd
    have hltR : (N:ℝ) < -(c.q:ℝ)*d := by exact_mod_cast hlt
    push_cast at hb
    nlinarith [mul_le_mul_of_nonneg_left hcx hdR.le]
  · simp at hm

theorem run_sound (T : Array Entry) (hT : TableValid T 44) (side shift : ℚ)
    (S S' : HState) (st : Step) (p : ℕ → AnglePose)
    (h : st.run T side shift S = some S') (hrep : Rep T S p)
    (hpack : Packing S.length p) (hfit : Fits S.length side shift p) :
    Rep T S' p ∧ S'.length = S.length := by
  cases st with
  | cut i k j keep m =>
    simp only [Step.run] at h
    split at h
    · simp at h
    · next r hr =>
      split at h
      · simp at h
      · next es hes =>
        split_ifs at h with hc
        obtain ⟨hij, hj, hcol⟩ := hc
        simp only [Option.some.injEq] at h
        subst h
        have hi := rowsOf_lt hr
        refine ⟨splice_sound T S i k r _ p hr hrep ?_, length_splice _ _ _ _⟩
        rintro ⟨e, he, hcen, hbox, hang⟩
        have hee : e = es := by
          rw [hes] at he
          exact (Option.some.inj he).symm
        subst hee
        refine ⟨_, List.mem_singleton.mpr rfl, e, he, ?_⟩
        suffices hdom : (p i).center ∈ Dom (dropBits (keep :: r.cons) m) from
          ⟨hdom, mkBox_good _ _ hdom, hang⟩
        intro c hc'
        rcases List.mem_cons.mp (dropBits_mem _ _ _ hc') with hck | hmem
        · rw [hck]
          by_contra hnot
          have hopp : (p i).center ∈ Dom (⟨-keep.a, -keep.b, -keep.q⟩ :: r.cons) := by
            intro c2 hc2
            rcases List.mem_cons.mp hc2 with hc2 | hc2
            · rw [hc2]
              unfold IC.Holds at hnot ⊢
              have hlt := not_le.mp hnot
              push_cast
              linarith
            · exact hcen c2 hc2
          exact collideRows_sound T hT _ _ e (rowsOf S j) r.e he hcol (p i) hopp
            (mkBox_good _ _ hopp) hang (p j) (hrep j hj) (hpack i j hi hj hij)
        · exact hcen c hmem
  | kill i k j =>
    simp only [Step.run] at h
    split at h
    · simp at h
    · next r hr =>
      split at h
      · simp at h
      · next es hes =>
        split_ifs at h with hc
        obtain ⟨hij, hj, hcol⟩ := hc
        simp only [Option.some.injEq] at h
        subst h
        have hi := rowsOf_lt hr
        refine ⟨splice_sound T S i k r _ p hr hrep ?_, length_splice _ _ _ _⟩
        rintro ⟨e, he, hcen, hbox, hang⟩
        have hee : e = es := by
          rw [hes] at he
          exact (Option.some.inj he).symm
        subst hee
        exact absurd (hpack i j hi hj hij)
          (collideRows_sound T hT _ _ e (rowsOf S j) r.e he hcol (p i) hcen hbox hang (p j)
            (hrep j hj))
  | wall i k w m =>
    simp only [Step.run] at h
    split at h
    · simp at h
    · next r hr =>
      split at h
      · simp at h
      · next es hes =>
        split_ifs at h with hc
        simp only [Option.some.injEq] at h
        subst h
        have hi := rowsOf_lt hr
        refine ⟨splice_sound T S i k r _ p hr hrep ?_, length_splice _ _ _ _⟩
        rintro ⟨e, he, hcen, hbox, hang⟩
        have hee : e = es := by
          rw [hes] at he
          exact (Option.some.inj he).symm
        subst hee
        refine ⟨_, List.mem_singleton.mpr rfl, e, he, ?_⟩
        suffices hdom : (p i).center ∈ Dom (dropBits (w ++ r.cons) m) from
          ⟨hdom, mkBox_good _ _ hdom, hang⟩
        intro c hc'
        rcases List.mem_append.mp (dropBits_mem _ _ _ hc') with hw | hmem
        · exact wallOK_sound e (hT r.e e he) side shift c (List.all_eq_true.mp hc c hw) (p i)
            hang (hfit i hi)
        · exact hcen c hmem
  | split i k e1 e2 =>
    simp only [Step.run] at h
    split at h
    · simp at h
    · next r hr =>
      split at h
      · next a a1 a2 ha ha1 ha2 =>
        split_ifs at h with hc
        obtain ⟨h1, h2, h3⟩ := hc
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨splice_sound T S i k r _ p hr hrep ?_, length_splice _ _ _ _⟩
        rintro ⟨e, he, hcen, hbox, hang⟩
        have hee : e = a := by
          rw [ha] at he
          exact (Option.some.inj he).symm
        subst hee
        have h1R : (a1.lo:ℝ) ≤ (e.lo:ℝ) := by exact_mod_cast h1
        have h2R : (a2.lo:ℝ) ≤ (a1.hi:ℝ) := by exact_mod_cast h2
        have h3R : (e.hi:ℝ) ≤ (a2.hi:ℝ) := by exact_mod_cast h3
        by_cases hle : (p i).angle ≤ (a1.hi:ℝ)
        · exact ⟨⟨r.cons, r.box, e1⟩, by simp, a1, ha1, hcen, hbox,
            ⟨le_trans h1R hang.1, hle⟩⟩
        · exact ⟨⟨r.cons, r.box, e2⟩, by simp, a2, ha2, hcen, hbox,
            ⟨le_trans h2R (not_le.mp hle).le, le_trans hang.2 h3R⟩⟩
      · simp at h
  | dead i k =>
    simp only [Step.run] at h
    split at h
    · simp at h
    · next r hr =>
      split_ifs at h with hc
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨splice_sound T S i k r _ p hr hrep ?_, length_splice _ _ _ _⟩
      rintro ⟨e, he, hcen, hbox, hang⟩
      exact absurd hcen (emptyOK_sound r.cons hc _)

theorem runAll_sound (T : Array Entry) (hT : TableValid T 44) (side shift : ℚ) :
    ∀ (steps : List Step) (S S' : HState) (p : ℕ → AnglePose),
      runAll T side shift S steps = some S' → Rep T S p → Packing S.length p →
      Fits S.length side shift p → Rep T S' p ∧ S'.length = S.length
  | [], S, S', p, h, hrep, _, _ => by
    simp only [runAll, Option.some.injEq] at h
    subst h
    exact ⟨hrep, rfl⟩
  | st :: rest, S, S', p, h, hrep, hpack, hfit => by
    simp only [runAll] at h
    split at h
    · next S1 h1 =>
      obtain ⟨hr1, hl1⟩ := run_sound T hT side shift S S1 st p h1 hrep hpack hfit
      obtain ⟨hr2, hl2⟩ := runAll_sound T hT side shift rest S1 S' p h hr1
        (by rw [hl1]; exact hpack) (by rw [hl1]; exact hfit)
      exact ⟨hr2, hl2.trans hl1⟩
    · simp at h

/-- An accepted trace that ends with an owner without live rows excludes every
packing represented by the initial state. -/
theorem excludes_sound (T : Array Entry) (hT : TableValid T 44) (side shift : ℚ) (n : ℕ)
    (S : HState) (steps : List Step) (hn : n ≤ S.length)
    (h : excludes T side shift n S steps = true) :
    ¬ ∃ p : ℕ → AnglePose, Rep T S p ∧ Packing S.length p ∧ Fits S.length side shift p := by
  rintro ⟨p, hrep, hpack, hfit⟩
  simp only [excludes] at h
  split at h
  · next S' hS' =>
    obtain ⟨hr, hl⟩ := runAll_sound T hT side shift steps S S' p hS' hrep hpack hfit
    simp only [hasEmpty, List.any_eq_true, List.mem_range, List.isEmpty_iff] at h
    obtain ⟨i, hi, he⟩ := h
    obtain ⟨r, hr', _⟩ := hr i (by omega)
    rw [he] at hr'
    simp at hr'
  · simp at h

end Sq17.Propagation.HalfPlaneState

#print axioms Sq17.Propagation.HalfPlaneState.excludes_sound
