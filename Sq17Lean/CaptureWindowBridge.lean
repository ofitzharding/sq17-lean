import Sq17Lean.CaptureFamily
import Sq17Lean.CaptureSummaryTargets
import Sq17Lean.HalfPlaneWindowSeed
import Sq17Lean.CaptureOpenBridge

/-! The capture computation connects directly to the certified summary, retaining
actual target-box containment. No terminal polygon-hull inclusion is assumed.
The concrete OPEN certificate must supply `propagate` and `summary_checked`. -/
namespace Sq17.CaptureWindowBridge
open Propagation Propagation.HalfPlaneState CenteredOrbitFrame CaptureChart
open HalfPlaneFrameBounds HalfPlaneAssembly

open Sq17.CaptureOpenBridge

theorem side_eq_of_open_run (T U : Array Entry) (S E : HState)
    (windows : ℕ → ℚ × ℚ)
    (window_width : ∀ i : Fin 17, Real.pi/2 ≤ ((windows i.val).2:ℝ)-((windows i.val).1:ℝ))
    (seed_checked : windowSeedOK T windows
      (rosterCells terminalSigma (List.ofFn CaptureFamily.roster)) S = true)
    (initial_length : S.length = 17)
    (propagate : Propagates T U S E)
    (summary_checked : CaptureSummary.summaryCheck U E CaptureSummary.summaryTargets = true)
    (L : ℝ) (hL : L ≤ EndpointGeometry.side) (c u : Fin 17 → ℝ × ℝ)
    (hc : ∀ i, c i ∈ shift (-(terminalSigma:ℝ)) '' ExactCells.cell (CaptureFamily.roster i))
    (hu : ∀ i, (u i).1^2+(u i).2^2=1)
    (hf : ∀ i, Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2 ⊆ traceBox L terminalSigma)
    (hd : ∀ i j, i ≠ j → Disjoint
      (interior (Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2))
      (interior (Sq17.sq (c j).1 (c j).2 (u j).1 (u j).2))) :
    L = EndpointGeometry.side := by
  obtain ⟨p, hr, hs⟩ := roster_window_represented T terminalSigma 17 CaptureFamily.roster S windows
    seed_checked window_width initial_length c u hu hc
  have hp : Packing 17 p := by
    intro i j hi hj hij
    rw [hs ⟨i,hi⟩, hs ⟨j,hj⟩]
    exact hd _ _ (fun he => hij (congrArg Fin.val he))
  have hactual : ∀ i : Fin 17, (p i.val).square ⊆ traceBox L terminalSigma := by
    intro i
    rw [hs i]
    exact hf i
  have hheader : Fits 17 captureNeighbour.side captureNeighbour.padding p := by
    intro i hi
    have hb := capture_neighbour_bounds L hL
    exact Set.Subset.trans (hactual ⟨i,hi⟩) (frame_subset captureNeighbour L hb.1 hb.2)
  have he := propagate p hr hp hheader
  have hsummary := CaptureSummary.summaryCheck_pose U E summary_checked p he
  apply summary_pose_optimality L (fun i : Fin 17 => p i.val) hL hsummary hactual
  intro i j hij
  exact hp i.val j.val i.isLt j.isLt (fun he => hij (Fin.ext he))

/-- Instantiate the assembly skeleton's capture field with `False.elim` of this
result. It includes classifier case 1442's y reflection and owner reordering. -/
theorem classifier_capture_excluded (T U : Array Entry) (S E : HState)
    (windows : ℕ → ℚ × ℚ)
    (window_width : ∀ i : Fin 17, Real.pi/2 ≤ ((windows i.val).2:ℝ)-((windows i.val).1:ℝ))
    (seed_checked : windowSeedOK T windows
      (rosterCells terminalSigma (List.ofFn CaptureFamily.roster)) S = true)
    (initial_length : S.length = 17)
    (propagate : Propagates T U S E)
    (summary_checked : CaptureSummary.summaryCheck U E CaptureSummary.summaryTargets = true)
    (L : ℝ) (hL : L < EndpointGeometry.side) (holes : List (Fin 24))
    (P : RepresentativePacking holes L)
    (hroster : CaptureFamily.sourceRoster.toFinset = holes.toFinsetᶜ) : False := by
  obtain ⟨c,u,hc,hu,hf,hd⟩ := CaptureFamily.prepare L terminalSigma holes P hroster
  exact (ne_of_lt hL) (side_eq_of_open_run T U S E windows window_width seed_checked initial_length
    propagate summary_checked L hL.le c u hc hu hf hd)

end Sq17.CaptureWindowBridge
#print axioms Sq17.CaptureWindowBridge.classifier_capture_excluded
