import Sq17Lean.HalfPlaneStateSound

/-! Certifying a table of angle rows.

Each entry is paired with rational enclosures of cosine and sine at its two
endpoints. The executable check builds the existing core-row and wall-row
certificates from the entry and runs their own checkers. -/
namespace Sq17.Propagation.HalfPlaneState

/-- Wall support direction of a row: `cos+sin` on nonnegative angles, `cos-sin` on
nonpositive angles, and none for a row that straddles zero. -/
def wallDir (e : Entry) : ℚ × ℚ :=
  if 0 ≤ e.lo then (1, 1) else if e.hi ≤ 0 then (1, -1) else (0, 0)

def Entry.core (e : Entry) (l r : TrigBounds) : CoreRowCertificate :=
  ⟨e.lo, e.hi, (e.C:ℚ)/e.cd, (e.S:ℚ)/e.cd, (e.H:ℚ)/e.hd, l, r⟩

def Entry.wallRow (e : Entry) (l r : TrigBounds) : WallRowCertificate :=
  ⟨e.lo, e.hi, (wallDir e).1, (wallDir e).2, e.span, l, r⟩

def entryOK (n : ℕ) (e : Entry) (b : TrigBounds × TrigBounds) : Bool :=
  (e.core b.1 b.2).check n && (e.wallRow b.1 b.2).check n

def tableOK (n : ℕ) (T : Array Entry) (B : Array (TrigBounds × TrigBounds)) : Bool :=
  (List.range T.size).all fun k =>
    match T[k]?, B[k]? with
    | some e, some b => entryOK n e b
    | _, _ => false

theorem tableOK_sound (T : Array Entry) (B : Array (TrigBounds × TrigBounds))
    (h : tableOK 44 T B = true) : TableValid T 44 := by
  intro k e hk
  have hlt : k < T.size := by
    by_contra hn
    rw [Array.getElem?_eq_none (not_lt.mp hn)] at hk
    simp at hk
  have h1 := List.all_eq_true.mp h k (List.mem_range.mpr hlt)
  rw [hk] at h1
  split at h1
  · next e' b he hb =>
    cases he
    simp only [entryOK, Bool.and_eq_true] at h1
    exact ⟨⟨e.core b.1 b.2, h1.1, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨e.wallRow b.1 b.2, h1.2, rfl, rfl, rfl⟩⟩
  · simp at h1

end Sq17.Propagation.HalfPlaneState

#print axioms Sq17.Propagation.HalfPlaneState.tableOK_sound
