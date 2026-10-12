import Sq17Lean.CenteredOrbitFrame
import Sq17Lean.PropagationWallReplace
import Sq17Lean.EndpointSideSharp

/-! Header containment for every side up to the exact algebraic endpoint.
These rationals are the exact hexadecimal FULL1/FULL2 header values, not their
rounded decimal printouts. No trace acceptance is asserted here. -/
namespace Sq17.HalfPlaneFrameBounds
open CenteredOrbitFrame Propagation

structure Frame where
  side : ℚ
  padding : ℚ
  sigma : ℚ

def Frame.Lower (F : Frame) (L : ℝ) : Prop :=
  -(F.padding : ℝ) ≤ delta L - F.sigma

def Frame.Upper (F : Frame) (L : ℝ) : Prop :=
  delta L - F.sigma + L ≤ (F.side : ℝ) + F.padding

theorem frame_mono (F : Frame) (L M : ℝ) (hLM : L ≤ M)
    (frame_lower : F.Lower M) (frame_upper : F.Upper M) :
    F.Lower L ∧ F.Upper L := by
  dsimp [Frame.Lower, Frame.Upper, delta] at *
  constructor <;> linarith

theorem frame_subset (F : Frame) (L : ℝ)
    (frame_lower : F.Lower L) (frame_upper : F.Upper L) :
    traceBox L F.sigma ⊆ traceContainer F.side F.padding :=
  trace_subset_header L F.sigma F.side F.padding frame_lower frame_upper

def ordinary : Frame :=
  ⟨2632353982198055/562949953421312,
    4951760157141521/4951760157141521099596496896, 0⟩

def captureNeighbour : Frame :=
  ⟨5264178896829249/1125899906842624,
    4951760157141521/4951760157141521099596496896,
    8668243015428611/36893488147419103232⟩

theorem ordinary_bounds (L : ℝ) (hL : L ≤ EndpointGeometry.side) :
    ordinary.Lower L ∧ ordinary.Upper L := by
  apply frame_mono ordinary L (46755300936045510/10000000000000000)
    (hL.trans EndpointIntervals.side_decimal_bounds.2)
  · norm_num [Frame.Lower, ordinary, delta]
  · norm_num [Frame.Upper, ordinary, delta]

theorem capture_neighbour_bounds (L : ℝ) (hL : L ≤ EndpointGeometry.side) :
    captureNeighbour.Lower L ∧ captureNeighbour.Upper L := by
  apply frame_mono captureNeighbour L (46755300936045510/10000000000000000)
    (hL.trans EndpointIntervals.side_decimal_bounds.2)
  · norm_num [Frame.Lower, captureNeighbour, delta]
  · norm_num [Frame.Upper, captureNeighbour, delta]

end Sq17.HalfPlaneFrameBounds

#print axioms Sq17.HalfPlaneFrameBounds.ordinary_bounds
#print axioms Sq17.HalfPlaneFrameBounds.capture_neighbour_bounds
