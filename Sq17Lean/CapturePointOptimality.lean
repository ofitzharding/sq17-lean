import Sq17Lean.CapturePointBounds
import Sq17Lean.CaptureLocalOptimality

/-! A half-plane terminal need only establish the certified angle and projection
summary. There is no need to reconstruct the original terminal polygon hulls. -/
namespace Sq17.CaptureChart
open Sq17.Propagation Sq17.EndpointGeometry Sq17.EndpointIntervals
open Sq17.LocalPerturbation Sq17.RationalExpression
noncomputable section

/-- The exact per-owner summary consumed by the local optimality theorem. -/
def SummaryPoseBounds (p : Fin 17 → AnglePose) : Prop :=
  ∀ i, (terminalSummary i).angle.Holds (p i).angle ∧
    SummaryPointBands i (p i).center

theorem summary_angle_bounds (p : Fin 17 → AnglePose)
    (ha : ∀ i, (terminalSummary i).angle.Holds (p i).angle)
    (i : Fin 17) (hi : i ≠ 5) :
    |(p (owners i)).angle-baseAngle i| ≤ (1:ℝ)/10000000 := by
  have hp := ha (owners i)
  have h := terminalSummary_angle_checked i hi
  have hb := baseAngle_bounds i
  have h1 : ((baseAngleRange i).hi:ℝ)-(1:ℝ)/10000000 ≤
      ((terminalSummary (owners i)).angle.lo:ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr h.1
    push_cast at hh
    norm_num at hh ⊢
    exact hh
  have h2 : ((terminalSummary (owners i)).angle.hi:ℝ) ≤
      ((baseAngleRange i).lo:ℝ)+(1:ℝ)/10000000 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr h.2
    push_cast at hh
    norm_num at hh ⊢
    exact hh
  apply abs_le.mpr
  constructor <;> linarith [hp.1,hp.2,hb.1,hb.2]

theorem summary_coordinate_bounds (p : Fin 17 → AnglePose)
    (hs : SummaryPoseBounds p) :
    CoordinateBounds (chartCentres terminalSigma (fun i => (p i).center))
      (chartAngles (fun i => (p i).angle)) ((1:ℝ)/10000000) := by
  have hv := terminalSummary_pointBounds p (fun i => (hs i).2)
  constructor
  · exact summary_angle_bounds p (fun i => (hs i).1)
  · simpa [PointFunctionalBounds,functional,chartCentres,displacement] using
      abs_le.mpr hv.fifthY
  · simpa [PointFunctionalBounds,functional,chartCentres,displacement,transverse] using
      abs_le.mpr hv.eleventh
  · simpa [PointFunctionalBounds,functional,chartCentres,displacement,transverse] using
      abs_le.mpr hv.thirteenth
  · intro i h4 h5 h10 h12
    have hx := abs_le.mpr (hv.regular i h4 h5 h10 h12).1
    have hy := abs_le.mpr (hv.regular i h4 h5 h10 h12).2
    simpa [PointFunctionalBounds,functional,chartCentres,displacement] using And.intro hx hy

theorem summary_slider_box (L : ℝ) (p : Fin 17 → AnglePose)
    (hs : SummaryPoseBounds p) (hL : L ≤ side)
    (hfit : ∀ i, (p i).square ⊆ CenteredOrbitFrame.traceBox L terminalSigma) :
    LocalSlider.sliderBox (sliderA (chartCentres terminalSigma (fun i => (p i).center)))
      (sliderB (chartCentres terminalSigma (fun i => (p i).center)))
      (sliderZ (chartCentres terminalSigma (fun i => (p i).center))) := by
  have hv := terminalSummary_pointBounds p (fun i => (hs i).2)
  have htop : ∀ q ∈ poseSquare (chartCentres terminalSigma (fun i => (p i).center))
      (chartAngles (fun i => (p i).angle)) 4, q.1 ≤ side := by
    intro q hq
    have h := chart_pose_fit L terminalSigma (fun i => (p i).center)
      (fun i => (p i).angle) hfit 4 hq
    exact (chartBox_subset_endpoint hL h).2.1
  have ha0 := sliderA_nonnegative_of_fit _ _ htop
  have ha := hv.sliderA.2
  have hbb := hv.sliderB
  have hz := hv.sliderZ
  change 0 ≤ _ ∧ _ ≤ 1/4 ∧ -(1/2500) ≤ _ ∧ _ ≤ 1/12 ∧ -(1/8) ≤ _ ∧ _ ≤ 1/16
  simp only [PointFunctionalBounds,functional,chartCentres,turn,sliderA,sliderB,sliderZ,
    displacement,Prod.fst_sub,Prod.snd_sub,neg_mul,one_mul,zero_mul,mul_zero,add_zero,
    zero_add,sub_eq_add_neg,Prod.fst_add,Prod.snd_add,Prod.fst_neg,Prod.snd_neg,neg_div]
    at ha hbb hz ⊢
  exact ⟨ha0,ha,hbb.1,hbb.2,hz.1,hz.2⟩

/-- Direct summary-based local optimality. The global OPEN trace supplies `hs`;
the original packing reduction supplies the actual trace box and disjointness. -/
theorem summary_pose_optimality (L : ℝ) (p : Fin 17 → AnglePose)
    (hL : L ≤ side) (hs : SummaryPoseBounds p)
    (hfit : ∀ i, (p i).square ⊆ CenteredOrbitFrame.traceBox L terminalSigma)
    (hd : ∀ i j, i ≠ j →
      Disjoint (interior (p i).square) (interior (p j).square)) :
    L = side := by
  exact side_eq_of_local_capture L terminalSigma (fun i => (p i).center)
    (fun i => (p i).angle) hL hfit hd (summary_coordinate_bounds p hs)
    (summary_slider_box L p hs hL hfit)

end
end Sq17.CaptureChart
#print axioms Sq17.CaptureChart.summary_pose_optimality
