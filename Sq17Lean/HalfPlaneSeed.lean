import Sq17Lean.HalfPlaneTable
import Sq17Lean.PropagationAngleNormalize

/-! Seeding a half-plane state from cell polygons, and the per-case statement.

The initial rows of an owner must cover the whole normalised angle range and each
row's half-planes must contain every vertex of the owner's cell polygon. Then any
seventeen unit squares with centres in the cell hulls are represented, and an
accepted trace excludes them. -/
namespace Sq17.Propagation.HalfPlaneState
open Sq17.Propagation.HalfPlaneInt

/-- The rows, in order, cover the closed angle interval `[lo,hi]`. -/
def angleCover (T : Array Entry) (lo hi : ℚ) : List HRow → Bool
  | [] => false
  | r :: rows =>
    match T[r.e]? with
    | some e => decide (e.lo ≤ lo) && (decide (hi ≤ e.hi) || angleCover T e.hi hi rows)
    | none => false

theorem angleCover_sound (T : Array Entry) : ∀ (rows : List HRow) (lo hi : ℚ),
    angleCover T lo hi rows = true → ∀ θ : ℝ, θ ∈ Set.Icc (lo:ℝ) (hi:ℝ) →
    ∃ r ∈ rows, ∃ e, T[r.e]? = some e ∧ θ ∈ Set.Icc (e.lo:ℝ) (e.hi:ℝ)
  | [], _, _, hc, _, _ => by simp [angleCover] at hc
  | r :: rows, lo, hi, hc, θ, hθ => by
    simp only [angleCover] at hc
    split at hc
    · next e he =>
      have hh := Bool.and_eq_true_iff.mp hc
      have hlo : (e.lo:ℝ) ≤ lo := by exact_mod_cast of_decide_eq_true hh.1
      by_cases hright : θ ≤ (e.hi:ℝ)
      · exact ⟨r, by simp, e, he, hlo.trans hθ.1, hright⟩
      · have hrest : angleCover T e.hi hi rows = true := by
          rcases Bool.or_eq_true_iff.mp hh.2 with hstop | hnext
          · have hhi : (hi:ℝ) ≤ e.hi := by exact_mod_cast of_decide_eq_true hstop
            exact (hright (hθ.2.trans hhi)).elim
          · exact hnext
        obtain ⟨s, hs, e', he', hs'⟩ :=
          angleCover_sound T rows e.hi hi hrest θ ⟨(lt_of_not_ge hright).le, hθ.2⟩
        exact ⟨s, List.mem_cons_of_mem r hs, e', he', hs'⟩
    · simp at hc

/-- Every vertex of the cell satisfies every constraint. -/
def cellInside (cell : List (ℚ × ℚ)) (cons : List IC) : Bool :=
  cons.all fun c => cell.all fun v => decide ((c.a:ℚ)*v.1+(c.b:ℚ)*v.2 ≤ c.q)

theorem cellInside_sound (cell : List (ℚ × ℚ)) (cons : List IC)
    (h : cellInside cell cons = true) :
    convexHull ℝ (realPoint '' {v | v ∈ cell}) ⊆ Dom cons := by
  intro x hx c hc
  have hverts := List.all_eq_true.mp ((List.all_eq_true.mp h) c hc)
  have hsub : convexHull ℝ (realPoint '' {v | v ∈ cell}) ⊆
      {z | (c.a:ℝ)*z.1+(c.b:ℝ)*z.2 ≤ (c.q:ℝ)} := by
    apply convexHull_min ?_ (convex_halfSpace_le
      ⟨(dotMap (c.a:ℝ) (c.b:ℝ)).map_add, (dotMap (c.a:ℝ) (c.b:ℝ)).map_smul⟩ _)
    rintro _ ⟨v, hv, rfl⟩
    change (c.a:ℝ)*(v.1:ℝ)+(c.b:ℝ)*(v.2:ℝ) ≤ (c.q:ℝ)
    exact_mod_cast (of_decide_eq_true (hverts v hv) : (c.a:ℚ)*v.1+(c.b:ℚ)*v.2 ≤ c.q)
  exact hsub hx

def seedOK (T : Array Entry) (lo hi : ℚ) (cell : List (ℚ × ℚ)) (rows : List HRow) : Bool :=
  angleCover T lo hi rows &&
    rows.all fun r => cellInside cell r.cons && decide (r.box = mkBox r.cons)

def stateSeedOK (T : Array Entry) (lo hi : ℚ) (cells : List (List (ℚ × ℚ))) (S : HState) : Bool :=
  (List.range S.length).all fun i => seedOK T lo hi (cells.getD i []) (rowsOf S i)

theorem stateSeedOK_sound (T : Array Entry) (lo hi : ℚ) (cells : List (List (ℚ × ℚ)))
    (S : HState) (h : stateSeedOK T lo hi cells S = true) (p : ℕ → AnglePose)
    (hcenter : ∀ i, i < S.length →
      (p i).center ∈ convexHull ℝ (realPoint '' {v | v ∈ cells.getD i []}))
    (hangle : ∀ i, i < S.length → (p i).angle ∈ Set.Icc (lo:ℝ) (hi:ℝ)) :
    Rep T S p := by
  intro i hlt
  have h1 := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h i (List.mem_range.mpr hlt))
  obtain ⟨r, hr, e, he, hθ⟩ := angleCover_sound T _ lo hi h1.1 (p i).angle (hangle i hlt)
  have h2 := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h1.2 r hr)
  have hdom := cellInside_sound _ _ h2.1 (hcenter i hlt)
  have hbox : r.box = mkBox r.cons := of_decide_eq_true h2.2
  exact ⟨r, hr, e, he, hdom, hbox ▸ mkBox_good _ _ hdom, hθ⟩

/-- Unit squares with centres in the cell hulls are represented by the seeded state. -/
theorem seed_unit_squares (T : Array Entry) (cells : List (List (ℚ × ℚ))) (S : HState)
    (h : stateSeedOK T (-initialAngleRadius) initialAngleRadius cells S = true)
    (c u : ℕ → ℝ × ℝ) (hunit : ∀ i, i < S.length → (u i).1^2+(u i).2^2 = 1)
    (hcenter : ∀ i, i < S.length →
      c i ∈ convexHull ℝ (realPoint '' {v | v ∈ cells.getD i []})) :
    ∃ p : ℕ → AnglePose, Rep T S p ∧
      ∀ i, i < S.length → (p i).square = Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2 := by
  have H : ∀ i, ∃ θ : ℝ, i < S.length →
      θ ∈ Set.Icc (-(initialAngleRadius:ℝ)) (initialAngleRadius:ℝ) ∧
      Sq17.sq (c i).1 (c i).2 (Real.cos θ) (Real.sin θ) =
        Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2 := by
    intro i
    by_cases hi : i < S.length
    · obtain ⟨θ, hθ, heq⟩ :=
        square_unit_direction_normalize_initial (c i).1 (c i).2 (u i).1 (u i).2 (hunit i hi)
      exact ⟨θ, fun _ => ⟨hθ, heq⟩⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose θ hθ using H
  refine ⟨fun i => ⟨c i, θ i⟩, ?_, fun i hi => (hθ i hi).2⟩
  apply stateSeedOK_sound T (-initialAngleRadius) initialAngleRadius cells S h
  · intro i hi
    exact hcenter i hi
  · intro i hi
    simpa only [Rat.cast_neg] using (hθ i hi).1

/-- The per-case statement: an accepted table, seed and trace leave no family of
`n` unit squares with centres in the given cell hulls, pairwise disjoint interiors,
inside the translated container. -/
theorem case_excluded (T : Array Entry) (B : Array (TrigBounds × TrigBounds))
    (side shift : ℚ) (n : ℕ) (cells : List (List (ℚ × ℚ))) (S : HState) (steps : List Step)
    (htable : tableOK 44 T B = true)
    (hseed : stateSeedOK T (-initialAngleRadius) initialAngleRadius cells S = true)
    (hlen : S.length = n)
    (hex : excludes T side shift n S steps = true)
    (c u : ℕ → ℝ × ℝ)
    (hunit : ∀ i, i < n → (u i).1^2+(u i).2^2 = 1)
    (hcenter : ∀ i, i < n → c i ∈ convexHull ℝ (realPoint '' {v | v ∈ cells.getD i []}))
    (hd : ∀ i j, i < n → j < n → i ≠ j → Disjoint
      (interior (Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2))
      (interior (Sq17.sq (c j).1 (c j).2 (u j).1 (u j).2)))
    (hfit : ∀ i, i < n →
      Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2 ⊆ traceContainer side shift) : False := by
  subst hlen
  obtain ⟨p, hrep, hsq⟩ := seed_unit_squares T cells S hseed c u hunit hcenter
  apply excludes_sound T (tableOK_sound T B htable) side shift S.length S steps le_rfl hex
  refine ⟨p, hrep, ?_, ?_⟩
  · intro i j hi hj hij
    rw [hsq i hi, hsq j hj]
    exact hd i j hi hj hij
  · intro i hi
    rw [hsq i hi]
    exact hfit i hi

end Sq17.Propagation.HalfPlaneState

#print axioms Sq17.Propagation.HalfPlaneState.case_excluded
