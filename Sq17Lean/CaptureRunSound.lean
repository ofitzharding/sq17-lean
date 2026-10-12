import Sq17Lean.CaptureRunFast
import Sq17Lean.HalfPlaneStateSound

namespace Sq17.Propagation.HalfPlaneState

theorem runToCheck_eq (T : Array Entry) (side padding : ℚ) (S : HState)
    (steps : List Step) (E : HState)
    (h : runToCheck T side padding S steps E = true) :
    runAll T side padding S steps = some E := by
  unfold runToCheck at h
  split at h
  · next R he =>
    have hRE : R = E := of_decide_eq_true h
    simpa only [hRE] using he
  · simp at h

theorem rowsSameGeometry_sound (T U : Array Entry) : ∀ (rs ss : List HRow),
    rowsSameGeometry T U rs ss = true → rowsRegion T rs ⊆ rowsRegion U ss
  | [], _, _, _, hp => by obtain ⟨r, hr, _⟩ := hp; simp at hr
  | _ :: _, [], h, _, _ => by simp [rowsSameGeometry] at h
  | r :: rs, s :: ss, h, p, hp => by
    obtain ⟨hh, ht⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨heq, he⟩ := Bool.and_eq_true_iff.mp hh
    have heq' : r.cons = s.cons ∧ r.box = s.box := of_decide_eq_true heq
    obtain ⟨v, hv, hpose⟩ := hp
    rcases List.mem_cons.mp hv with hvr | hrest
    · subst v
      obtain ⟨e, het, hcons, hbox, hang⟩ := hpose
      rw [het] at he
      cases huf : U[s.e]? with
      | none => simp [huf] at he
      | some f =>
        have hef : e.lo = f.lo ∧ e.hi = f.hi := by simpa [huf] using he
        refine ⟨s, by simp, f, huf, ?_, ?_, ?_⟩
        · simpa only [heq'.1] using hcons
        · simpa only [heq'.2] using hbox
        · simpa only [hef.1, hef.2] using hang
    · obtain ⟨v, hv, hp⟩ := rowsSameGeometry_sound T U rs ss ht ⟨v, hrest, hpose⟩
      exact ⟨v, List.mem_cons_of_mem s hv, hp⟩

theorem sameGeometry_sound (T U : Array Entry) (S E : HState)
    (h : sameGeometry T U S E = true) (p : ℕ → AnglePose) (hr : Rep T S p) :
    Rep U E p ∧ E.length = S.length := by
  obtain ⟨hlen, hc⟩ := Bool.and_eq_true_iff.mp h
  have hlen' : E.length = S.length := of_decide_eq_true hlen
  refine ⟨?_, hlen'⟩
  intro i hi
  have hi' : i < S.length := by simpa only [hlen'] using hi
  exact rowsSameGeometry_sound T U _ _
    (List.all_eq_true.mp hc i (List.mem_range.mpr hi')) (hr i hi')

theorem open_segment_sound (T : Array Entry) (side padding : ℚ) (S E : HState)
    (steps : List Step) (hT : TableValid T 44)
    (h : runToCheck T side padding S steps E = true)
    (p : ℕ → AnglePose) (hr : Rep T S p) (hp : Packing S.length p)
    (hf : Fits S.length side padding p) : Rep T E p ∧ E.length = S.length :=
  runAll_sound T hT side padding steps S E p (runToCheck_eq T side padding S steps E h)
    hr hp hf

end Sq17.Propagation.HalfPlaneState

#print axioms Sq17.Propagation.HalfPlaneState.open_segment_sound
#print axioms Sq17.Propagation.HalfPlaneState.sameGeometry_sound
