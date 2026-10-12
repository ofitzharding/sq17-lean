import Sq17Lean.HalfPlaneCoverFast
import Sq17Lean.HalfPlaneBranchComposition

/-! Soundness of the executable checkpoint cover check: it implies
`BranchComposition.CheckpointCover`, in the forms `excluded_of_split` consumes. -/
namespace Sq17.Propagation.HalfPlaneState
open Sq17.Propagation.HalfPlaneInt

theorem impliedOK_sound (cons : List IC) (c : IC) (h : impliedOK cons c = true)
    (x : ℝ × ℝ) (hx : x ∈ Dom cons) : c.Holds x := by
  have hg := findUpper_good cons c.a c.b x hx
  unfold impliedOK at h
  split at h
  · next N d heq =>
    obtain ⟨hd, hb⟩ := hg N d heq
    have hle : N ≤ c.q*d := of_decide_eq_true h
    have hdR : (0:ℝ) < d := by exact_mod_cast hd
    have hleR : (N:ℝ) ≤ (c.q:ℝ)*d := by exact_mod_cast hle
    unfold IC.Holds
    by_contra hnot
    have hlt := not_le.mp hnot
    nlinarith [mul_lt_mul_of_pos_left hlt hdR]
  · simp at h

theorem rowContains_sound (cons : List IC) (s : HRow) (h : rowContains cons s = true) :
    Dom cons ⊆ Dom s.cons := fun x hx c hc =>
  impliedOK_sound cons c (List.all_eq_true.mp h c hc) x hx

theorem coverRow_sound (U : Array Entry) (cons : List IC) (hi : ℚ) :
    ∀ (rows : List HRow) (lo : ℚ), coverRow U cons hi lo rows = true →
      ∀ θ : ℝ, θ ∈ Set.Icc (lo:ℝ) (hi:ℝ) →
        ∃ s ∈ rows, ∃ e, U[s.e]? = some e ∧ θ ∈ Set.Icc (e.lo:ℝ) (e.hi:ℝ) ∧
          rowContains cons s = true
  | [], _, h, _, _ => by simp [coverRow] at h
  | s :: rest, lo, h, θ, hθ => by
    have lift : (∃ t ∈ rest, ∃ e, U[t.e]? = some e ∧ θ ∈ Set.Icc (e.lo:ℝ) (e.hi:ℝ) ∧
        rowContains cons t = true) →
        ∃ t ∈ s :: rest, ∃ e, U[t.e]? = some e ∧ θ ∈ Set.Icc (e.lo:ℝ) (e.hi:ℝ) ∧
          rowContains cons t = true := by
      rintro ⟨t, ht, rest'⟩
      exact ⟨t, List.mem_cons_of_mem _ ht, rest'⟩
    simp only [coverRow] at h
    split at h
    · exact lift (coverRow_sound U cons hi rest lo h θ hθ)
    · next e he =>
      split_ifs at h with hc
      · obtain ⟨h1, h2, h3⟩ := hc
        have h1R : (e.lo:ℝ) ≤ (lo:ℝ) := by exact_mod_cast h1
        by_cases hright : θ ≤ (e.hi:ℝ)
        · exact ⟨s, by simp, e, he, ⟨h1R.trans hθ.1, hright⟩, h3⟩
        · rcases Bool.or_eq_true_iff.mp h with hstop | hnext
          · have hhi : (hi:ℝ) ≤ (e.hi:ℝ) := by exact_mod_cast of_decide_eq_true hstop
            exact (hright (hθ.2.trans hhi)).elim
          · exact lift (coverRow_sound U cons hi rest e.hi hnext θ
              ⟨(lt_of_not_ge hright).le, hθ.2⟩)
      · exact lift (coverRow_sound U cons hi rest lo h θ hθ)

/-- The guard a cover check certifies: centre constraints and angle bounds. -/
def GuardHolds (cut : List IC) (alo ahi : Option ℚ) (q : AnglePose) : Prop :=
  q.center ∈ Dom cut ∧ (∀ m, alo = some m → (m:ℝ) ≤ q.angle) ∧
    (∀ m, ahi = some m → q.angle ≤ (m:ℝ))

theorem clampLo_le (plo : ℚ) (alo : Option ℚ) (θ : ℝ) (h1 : (plo:ℝ) ≤ θ)
    (h2 : ∀ m, alo = some m → (m:ℝ) ≤ θ) : ((clampLo plo alo : ℚ) : ℝ) ≤ θ := by
  unfold clampLo
  cases alo with
  | none => exact h1
  | some m =>
    simp only
    split_ifs
    · exact h2 m rfl
    · exact h1

theorem le_clampHi (phi : ℚ) (ahi : Option ℚ) (θ : ℝ) (h1 : θ ≤ (phi:ℝ))
    (h2 : ∀ m, ahi = some m → θ ≤ (m:ℝ)) : θ ≤ ((clampHi phi ahi : ℚ) : ℝ) := by
  unfold clampHi
  cases ahi with
  | none => exact h1
  | some m =>
    simp only
    split_ifs
    · exact h2 m rfl
    · exact h1

theorem rowCheck_sound (T U : Array Entry) (childRows : List HRow) (cut : List IC)
    (alo ahi : Option ℚ) (r : HRow)
    (hboxes : ∀ s ∈ childRows, s.box = mkBox s.cons)
    (h : rowCheck T U childRows cut alo ahi r = true)
    (q : AnglePose) (hq : q ∈ rowRegion T r) (hg : GuardHolds cut alo ahi q) :
    q ∈ rowsRegion U childRows := by
  obtain ⟨e, he, hcen, _, hang⟩ := hq
  obtain ⟨hcut, hlo, hhi⟩ := hg
  unfold rowCheck at h
  rw [he] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  have hdom : q.center ∈ Dom (cut ++ r.cons) := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hcut c hc
    · exact hcen c hc
  have hθ : q.angle ∈ Set.Icc ((clampLo e.lo alo : ℚ) : ℝ) ((clampHi e.hi ahi : ℚ) : ℝ) :=
    ⟨clampLo_le e.lo alo q.angle hang.1 hlo, le_clampHi e.hi ahi q.angle hang.2 hhi⟩
  rcases h with (hempty | hempty) | hcover
  · have hR : ((clampHi e.hi ahi : ℚ) : ℝ) < ((clampLo e.lo alo : ℚ) : ℝ) := by
      exact_mod_cast hempty
    exact absurd (hθ.1.trans hθ.2) (not_le.mpr hR)
  · exact absurd hdom (emptyOK_sound _ hempty _)
  · obtain ⟨s, hs, e', he', hθ', hcont⟩ := coverRow_sound U _ _ childRows _ hcover q.angle hθ
    have hsdom := rowContains_sound _ s hcont hdom
    exact ⟨s, hs, e', he', hsdom, (hboxes s hs) ▸ mkBox_good _ _ hsdom, hθ'⟩

theorem coverCheck_sound (T U : Array Entry) (parent child : HState) (owner : ℕ)
    (cut : List IC) (alo ahi : Option ℚ)
    (h : coverCheck T U parent child owner cut alo ahi = true) :
    BranchComposition.CheckpointCover T U parent child owner (GuardHolds cut alo ahi) := by
  intro i hi q hq hguard
  have h1 := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h i (List.mem_range.mpr hi))
  have hboxes : ∀ s ∈ rowsOf child i, s.box = mkBox s.cons := fun s hs =>
    of_decide_eq_true (List.all_eq_true.mp h1.1 s hs)
  obtain ⟨r, hr, hqr⟩ := hq
  have h2 := List.all_eq_true.mp h1.2 r hr
  by_cases hio : i = owner
  · rw [if_pos hio] at h2
    exact rowCheck_sound T U _ cut alo ahi r hboxes h2 q hqr (hguard hio)
  · rw [if_neg hio] at h2
    exact rowCheck_sound T U _ [] none none r hboxes h2 q hqr
      ⟨fun c hc => by simp at hc, fun m hm => by simp at hm, fun m hm => by simp at hm⟩

/-- Weakening the guard: a cover for a weaker guard serves any stronger one. -/
theorem cover_mono (T U : Array Entry) (parent child : HState) (owner : ℕ)
    (g g' : AnglePose → Prop) (hgg : ∀ q, g' q → g q)
    (h : BranchComposition.CheckpointCover T U parent child owner g) :
    BranchComposition.CheckpointCover T U parent child owner g' :=
  fun i hi q hq hguard => h i hi q hq (fun hio => hgg q (hguard hio))

/-- The six branch guards, as `excluded_of_split` states them. Centre mids are
`n/d` with `d > 0`; angle mids are rationals. -/
theorem cover_x_le (T U : Array Entry) (parent child : HState) (owner : ℕ) (n d : ℤ)
    (hd : 0 < d) (h : coverCheck T U parent child owner [⟨d, 0, n⟩] none none = true) :
    BranchComposition.CheckpointCover T U parent child owner
      (fun q => q.center.1 ≤ (n:ℝ)/d) := by
  apply cover_mono T U parent child owner _ _ _ (coverCheck_sound T U parent child owner _ _ _ h)
  intro q hq
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  refine ⟨?_, fun m hm => by simp at hm, fun m hm => by simp at hm⟩
  intro c hc
  rw [List.mem_singleton.mp hc]
  show ((d:ℤ):ℝ)*q.center.1+((0:ℤ):ℝ)*q.center.2 ≤ ((n:ℤ):ℝ)
  have := (le_div_iff₀ hdR).mp hq
  push_cast
  linarith

theorem cover_x_ge (T U : Array Entry) (parent child : HState) (owner : ℕ) (n d : ℤ)
    (hd : 0 < d) (h : coverCheck T U parent child owner [⟨-d, 0, -n⟩] none none = true) :
    BranchComposition.CheckpointCover T U parent child owner
      (fun q => (n:ℝ)/d ≤ q.center.1) := by
  apply cover_mono T U parent child owner _ _ _ (coverCheck_sound T U parent child owner _ _ _ h)
  intro q hq
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  refine ⟨?_, fun m hm => by simp at hm, fun m hm => by simp at hm⟩
  intro c hc
  rw [List.mem_singleton.mp hc]
  show ((-d:ℤ):ℝ)*q.center.1+((0:ℤ):ℝ)*q.center.2 ≤ ((-n:ℤ):ℝ)
  have := (div_le_iff₀ hdR).mp hq
  push_cast
  linarith

theorem cover_y_le (T U : Array Entry) (parent child : HState) (owner : ℕ) (n d : ℤ)
    (hd : 0 < d) (h : coverCheck T U parent child owner [⟨0, d, n⟩] none none = true) :
    BranchComposition.CheckpointCover T U parent child owner
      (fun q => q.center.2 ≤ (n:ℝ)/d) := by
  apply cover_mono T U parent child owner _ _ _ (coverCheck_sound T U parent child owner _ _ _ h)
  intro q hq
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  refine ⟨?_, fun m hm => by simp at hm, fun m hm => by simp at hm⟩
  intro c hc
  rw [List.mem_singleton.mp hc]
  show ((0:ℤ):ℝ)*q.center.1+((d:ℤ):ℝ)*q.center.2 ≤ ((n:ℤ):ℝ)
  have := (le_div_iff₀ hdR).mp hq
  push_cast
  linarith

theorem cover_y_ge (T U : Array Entry) (parent child : HState) (owner : ℕ) (n d : ℤ)
    (hd : 0 < d) (h : coverCheck T U parent child owner [⟨0, -d, -n⟩] none none = true) :
    BranchComposition.CheckpointCover T U parent child owner
      (fun q => (n:ℝ)/d ≤ q.center.2) := by
  apply cover_mono T U parent child owner _ _ _ (coverCheck_sound T U parent child owner _ _ _ h)
  intro q hq
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  refine ⟨?_, fun m hm => by simp at hm, fun m hm => by simp at hm⟩
  intro c hc
  rw [List.mem_singleton.mp hc]
  show ((0:ℤ):ℝ)*q.center.1+((-d:ℤ):ℝ)*q.center.2 ≤ ((-n:ℤ):ℝ)
  have := (div_le_iff₀ hdR).mp hq
  push_cast
  linarith

theorem cover_angle_le (T U : Array Entry) (parent child : HState) (owner : ℕ) (m : ℚ)
    (h : coverCheck T U parent child owner [] none (some m) = true) :
    BranchComposition.CheckpointCover T U parent child owner (fun q => q.angle ≤ (m:ℝ)) := by
  apply cover_mono T U parent child owner _ _ _ (coverCheck_sound T U parent child owner _ _ _ h)
  intro q hq
  refine ⟨fun c hc => by simp at hc, fun m' hm => by simp at hm, fun m' hm => ?_⟩
  rw [← Option.some.inj hm]
  exact hq

theorem cover_angle_ge (T U : Array Entry) (parent child : HState) (owner : ℕ) (m : ℚ)
    (h : coverCheck T U parent child owner [] (some m) none = true) :
    BranchComposition.CheckpointCover T U parent child owner (fun q => (m:ℝ) ≤ q.angle) := by
  apply cover_mono T U parent child owner _ _ _ (coverCheck_sound T U parent child owner _ _ _ h)
  intro q hq
  refine ⟨fun c hc => by simp at hc, fun m' hm => ?_, fun m' hm => by simp at hm⟩
  rw [← Option.some.inj hm]
  exact hq

end Sq17.Propagation.HalfPlaneState

#print axioms Sq17.Propagation.HalfPlaneState.coverCheck_sound
#print axioms Sq17.Propagation.HalfPlaneState.cover_x_le
#print axioms Sq17.Propagation.HalfPlaneState.cover_angle_ge
