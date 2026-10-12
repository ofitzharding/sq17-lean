import Sq17Lean.HalfPlaneCover
import Sq17Lean.HalfPlaneRosterSeed
import Sq17Lean.HalfPlaneTable

/-! Glue for branch trees: one lemma per kind of tree node, so that a generated
tree file is a short list of applications. Nothing here certifies a concrete tree. -/
namespace Sq17.Propagation.HalfPlaneState
open Sq17.Propagation.HalfPlaneInt BranchComposition

theorem run_length (T : Array Entry) (side shift : ℚ) (S S' : HState) (st : Step)
    (h : st.run T side shift S = some S') : S'.length = S.length := by
  cases st with
  | cut i k j keep m =>
    simp only [Step.run] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split_ifs at h
        simp only [Option.some.injEq] at h
        subst h
        exact length_splice _ _ _ _
  | kill i k j =>
    simp only [Step.run] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split_ifs at h
        simp only [Option.some.injEq] at h
        subst h
        exact length_splice _ _ _ _
  | wall i k w m =>
    simp only [Step.run] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split_ifs at h
        simp only [Option.some.injEq] at h
        subst h
        exact length_splice _ _ _ _
  | split i k e1 e2 =>
    simp only [Step.run] at h
    split at h
    · simp at h
    · split at h
      · split_ifs at h
        simp only [Option.some.injEq] at h
        subst h
        exact length_splice _ _ _ _
      · simp at h
  | dead i k =>
    simp only [Step.run] at h
    split at h
    · simp at h
    · split_ifs at h
      simp only [Option.some.injEq] at h
      subst h
      exact length_splice _ _ _ _

theorem runAll_length (T : Array Entry) (side shift : ℚ) :
    ∀ (steps : List Step) (S S' : HState), runAll T side shift S steps = some S' →
      S'.length = S.length
  | [], S, S', h => by
    simp only [runAll, Option.some.injEq] at h
    subst h
    rfl
  | st :: rest, S, S', h => by
    simp only [runAll] at h
    split at h
    · next S1 h1 =>
      exact (runAll_length T side shift rest S1 S' h).trans (run_length T side shift S S1 st h1)
    · simp at h

/-- The final state of an accepted run, read back from the computation. -/
theorem runAll_final (T : Array Entry) (side shift : ℚ) (S : HState) (steps : List Step)
    (h : (runAll T side shift S steps).isSome = true) :
    runAll T side shift S steps = some ((runAll T side shift S steps).getD []) := by
  cases hr : runAll T side shift S steps with
  | none => rw [hr] at h; simp at h
  | some E => rfl

/-- A leaf: the trace ends with an owner that has no live row. -/
theorem leaf_excluded (T : Array Entry) (B : Array (TrigBounds × TrigBounds)) (S : HState)
    (side shift : ℚ) (n : ℕ) (steps : List Step) (hT : tableOK 44 T B = true)
    (hlen : S.length = n) (hex : excludes T side shift n S steps = true) :
    Excluded T S side shift := by
  subst hlen
  exact excluded_of_check T S side shift steps (tableOK_sound T B hT) hex

/-- An internal node: an accepted run to `E`, then a split of `E` into two children. -/
theorem split_excluded (T Tl Tr : Array Entry) (B : Array (TrigBounds × TrigBounds))
    (S E L R : HState) (side shift : ℚ) (n : ℕ) (steps : List Step) (owner : ℕ)
    (coordinate : AnglePose → ℝ) (mid : ℝ) (hT : tableOK 44 T B = true)
    (hrun : (runAll T side shift S steps).isSome = true)
    (hE : E = (runAll T side shift S steps).getD [])
    (hS : S.length = n) (hL : L.length = n) (hR : R.length = n)
    (cl : CheckpointCover T Tl E L owner (fun q => coordinate q ≤ mid))
    (cr : CheckpointCover T Tr E R owner (fun q => mid ≤ coordinate q))
    (el : Excluded Tl L side shift) (er : Excluded Tr R side shift) :
    Excluded T S side shift := by
  have hfin : runAll T side shift S steps = some E := hE ▸ runAll_final T side shift S steps hrun
  have hElen : E.length = n := (runAll_length T side shift steps S E hfin).trans hS
  exact excluded_of_run T S E side shift steps (tableOK_sound T B hT) hfin
    (excluded_of_split T Tl Tr E L R side shift owner coordinate mid
      (hL.trans hElen.symm) (hR.trans hElen.symm) cl cr el er)

/-- A reload: an accepted run to `E`, then a checkpoint that contains all of `E`. -/
theorem reload_excluded (T U : Array Entry) (B : Array (TrigBounds × TrigBounds))
    (S E C : HState) (side shift : ℚ) (n : ℕ) (steps : List Step)
    (hT : tableOK 44 T B = true)
    (hrun : (runAll T side shift S steps).isSome = true)
    (hE : E = (runAll T side shift S steps).getD [])
    (hS : S.length = n) (hC : C.length = n)
    (hcover : coverCheck T U E C 0 [] none none = true)
    (ec : Excluded U C side shift) : Excluded T S side shift := by
  have hfin : runAll T side shift S steps = some E := hE ▸ runAll_final T side shift S steps hrun
  have hElen : E.length = n := (runAll_length T side shift steps S E hfin).trans hS
  apply excluded_of_run T S E side shift steps (tableOK_sound T B hT) hfin
  intro p hr hp hf
  have hg : GuardHolds [] none none (p 0) :=
    ⟨fun c hc => by simp at hc, fun m hm => by simp at hm, fun m hm => by simp at hm⟩
  exact ec p (checkpoint_rep T U E C 0 _ (hC.trans hElen.symm)
      (coverCheck_sound T U E C 0 [] none none hcover) p hr hg)
    (by rw [hC, ← hElen]; exact hp) (by rw [hC, ← hElen]; exact hf)

/-- The root statement: an excluded seeded state leaves no family of unit squares
with centres in the translated named cells of the roster. -/
theorem tree_excluded (T : Array Entry) (side shift sigma : ℚ) (n : ℕ)
    (roster : Fin n → Fin 24) (S : HState)
    (hseed : stateSeedOK T (-initialAngleRadius) initialAngleRadius
      (rosterCells sigma (List.ofFn roster)) S = true)
    (hlen : S.length = n) (hex : Excluded T S side shift)
    (c u : Fin n → ℝ × ℝ)
    (hunit : ∀ i, (u i).1^2+(u i).2^2 = 1)
    (hcenter : ∀ i, c i ∈ CenteredOrbitFrame.shift (-(sigma:ℝ)) '' ExactCells.cell (roster i))
    (hd : ∀ i j, i ≠ j → Disjoint
      (interior (Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2))
      (interior (Sq17.sq (c j).1 (c j).2 (u j).1 (u j).2)))
    (hfit : ∀ i, Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2 ⊆ traceContainer side shift) :
    False := by
  obtain ⟨p, hrep, hsq⟩ := roster_represented T sigma n roster S hseed hlen c u hunit hcenter
  subst hlen
  apply hex p hrep
  · intro i j hi hj hij
    have h1 := hsq ⟨i, hi⟩
    have h2 := hsq ⟨j, hj⟩
    simp only at h1 h2
    rw [h1, h2]
    exact hd _ _ (fun h => hij (by simpa using congrArg Fin.val h))
  · intro i hi
    have h1 := hsq ⟨i, hi⟩
    simp only at h1
    rw [h1]
    exact hfit _

end Sq17.Propagation.HalfPlaneState

#print axioms Sq17.Propagation.HalfPlaneState.split_excluded
#print axioms Sq17.Propagation.HalfPlaneState.reload_excluded
#print axioms Sq17.Propagation.HalfPlaneState.tree_excluded
