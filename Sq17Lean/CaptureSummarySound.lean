import Sq17Lean.CaptureSummaryFast
import Sq17Lean.HalfPlaneCover

namespace Sq17.Propagation.HalfPlaneState.CaptureSummary
open Sq17.Propagation.HalfPlaneInt

def Target.Holds (t : Target) (p : AnglePose) : Prop :=
  p.angle ∈ Set.Icc (t.lo:ℝ) (t.hi:ℝ) ∧ p.center ∈ Dom t.cons

theorem rowCheck_sound (T : Array Entry) (target : Target) (r : HRow)
    (h : rowCheck T target r = true) (p : AnglePose) (hp : p ∈ rowRegion T r) :
    target.Holds p := by
  obtain ⟨e, he, hcen, _, hang⟩ := hp
  unfold rowCheck at h
  rw [he] at h
  obtain ⟨ha,hcons⟩ := Bool.and_eq_true_iff.mp h
  have ha' := of_decide_eq_true ha
  have hlo : (target.lo:ℝ) ≤ (e.lo:ℝ) := by exact_mod_cast ha'.1
  have hhi : (e.hi:ℝ) ≤ (target.hi:ℝ) := by exact_mod_cast ha'.2
  refine ⟨⟨hlo.trans hang.1,hang.2.trans hhi⟩,?_⟩
  intro c hc
  exact impliedOK_sound r.cons c (List.all_eq_true.mp hcons c hc) p.center hcen

theorem summaryCheck_sound (T : Array Entry) (S : HState) (targets : Array Target)
    (h : summaryCheck T S targets = true) (p : ℕ → AnglePose) (hp : Rep T S p) :
    ∀ i : Fin 17, (targets[i.val]!).Holds (p i.val) := by
  have h' := Bool.and_eq_true_iff.mp h
  have hlen := (of_decide_eq_true h'.1).1
  intro i
  have hi : i.val < S.length := by omega
  obtain ⟨r,hr,hp'⟩ := hp i.val hi
  have hi' := List.all_eq_true.mp h'.2 i.val (List.mem_range.mpr i.isLt)
  exact rowCheck_sound T _ r (List.all_eq_true.mp hi' r hr) _ hp'

end Sq17.Propagation.HalfPlaneState.CaptureSummary
#print axioms Sq17.Propagation.HalfPlaneState.CaptureSummary.summaryCheck_sound
