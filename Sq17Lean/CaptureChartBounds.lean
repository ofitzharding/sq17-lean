import Sq17Lean.CaptureChartPacking
import Sq17Lean.EndpointAngleBounds
import Sq17Lean.FiniteAffineBounds

/-! The terminal-state interface is stated in terms of finite row endpoints
and vertices. It extends those inequalities to every represented pose, with
the exact chart frame and owner permutation. -/
namespace Sq17.CaptureChart
open Sq17.Propagation Sq17.EndpointGeometry Sq17.LocalPerturbation
noncomputable section

def functional (sigma : ℝ) (i : Fin 17) (A B : ℝ) (p : ℝ × ℝ) : ℝ :=
  A*((turn sigma p).1-(EndpointGeometry.centres i).1)+
  B*((turn sigma p).2-(EndpointGeometry.centres i).2)

theorem functional_affine (sigma : ℝ) (i : Fin 17) (A B : ℝ) (p : ℝ × ℝ) :
    functional sigma i A B p = -B*p.1+A*p.2+
      (B*(side+chartShift sigma-(EndpointGeometry.centres i).2)-
        A*(chartShift sigma+(EndpointGeometry.centres i).1)) := by
  unfold functional turn
  ring

theorem functional_bound_from_projection (sigma : ℝ) (i : Fin 17)
    (A B a b vlo vhi lo hi : ℝ) (p : ℝ × ℝ)
    (hx : |p.1| ≤ 5) (hy : |p.2| ≤ 5)
    (hv : vlo ≤ a*p.1+b*p.2 ∧ a*p.1+b*p.2 ≤ vhi)
    (hl : lo ≤ vlo+(B*(side+chartShift sigma-(EndpointGeometry.centres i).2)-
      A*(chartShift sigma+(EndpointGeometry.centres i).1))-5*(|-B-a|+|A-b|))
    (hu : vhi+(B*(side+chartShift sigma-(EndpointGeometry.centres i).2)-
      A*(chartShift sigma+(EndpointGeometry.centres i).1))+5*(|-B-a|+|A-b|) ≤ hi) :
    lo ≤ functional sigma i A B p ∧ functional sigma i A B p ≤ hi := by
  let C := B*(side+chartShift sigma-(EndpointGeometry.centres i).2)-
      A*(chartShift sigma+(EndpointGeometry.centres i).1)
  have h := affine_approx_bounds (-B) A C a b |-B-a| |A-b| 5 vlo vhi C C p
    (by norm_num) hx hy le_rfl le_rfl hv ⟨le_rfl,le_rfl⟩
  rw [functional_affine]
  dsimp [C] at h
  constructor <;> nlinarith [h.1,h.2]

def VertexBounds (S : Fin 17 → List PolygonRow) (sigma : ℝ) (i : Fin 17)
    (A B lo hi : ℝ) : Prop :=
  ∀ row ∈ S (owners i), ∀ v ∈ row.vertices,
    lo ≤ functional sigma i A B (realPoint v) ∧
    functional sigma i A B (realPoint v) ≤ hi

theorem vertexBounds_pose (S : Fin 17 → List PolygonRow) (sigma : ℝ)
    (p : Fin 17 → AnglePose) (hrep : Represents (stateDomains S) p)
    (i : Fin 17) (A B lo hi : ℝ) (hb : VertexBounds S sigma i A B lo hi) :
    lo ≤ functional sigma i A B (p (owners i)).center ∧
    functional sigma i A B (p (owners i)).center ≤ hi := by
  obtain ⟨row,hr,hp⟩ := hrep (owners i)
  simp only [VertexBounds,functional_affine] at hb
  simp only [functional_affine]
  exact affineHull_bounds row.vertices (-B) A
    (B*(side+chartShift sigma-(EndpointGeometry.centres i).2)-
      A*(chartShift sigma+(EndpointGeometry.centres i).1)) lo hi
    (hb row hr) _ hp.1

def angleRowsCheck (S : Fin 17 → List PolygonRow) (radius : ℚ) : Bool :=
  (List.finRange 17).all fun i => if i = 5 then true else
    (S (owners i)).all fun row => decide
      ((EndpointIntervals.baseAngleRange i).hi-radius ≤ row.lo ∧
        row.hi ≤ (EndpointIntervals.baseAngleRange i).lo+radius)

theorem angleRowsCheck_sound (S : Fin 17 → List PolygonRow) (radius : ℚ)
    (hc : angleRowsCheck S radius = true)
    (p : Fin 17 → AnglePose) (hrep : Represents (stateDomains S) p)
    (i : Fin 17) (hi : i ≠ 5) :
    |(p (owners i)).angle-baseAngle i| ≤ (radius:ℝ) := by
  have hi' := (List.all_eq_true.mp hc) i (List.mem_finRange i)
  simp only [if_neg hi] at hi'
  obtain ⟨row,hr,hp⟩ := hrep (owners i)
  have h := of_decide_eq_true ((List.all_eq_true.mp hi') row hr)
  have ha := EndpointIntervals.baseAngle_bounds i
  have h1 : ((EndpointIntervals.baseAngleRange i).hi:ℝ)-radius ≤ row.lo := by
    exact_mod_cast h.1
  have h2 : (row.hi:ℝ) ≤ ((EndpointIntervals.baseAngleRange i).lo:ℝ)+radius := by
    exact_mod_cast h.2
  apply abs_le.mpr
  constructor <;> linarith [hp.2.1,hp.2.2,ha.1,ha.2]

structure TerminalVertexBounds (S : Fin 17 → List PolygonRow) (sigma radius : ℝ) : Prop where
  fifthY : VertexBounds S sigma 4 0 1 (-radius) radius
  eleventh : VertexBounds S sigma 10 c s (-radius) radius
  thirteenth : VertexBounds S sigma 12 c s (-radius) radius
  regular : ∀ i, i ≠ 4 → i ≠ 5 → i ≠ 10 → i ≠ 12 →
    VertexBounds S sigma i 1 0 (-radius) radius ∧
    VertexBounds S sigma i 0 1 (-radius) radius
  sliderA : VertexBounds S sigma 4 (-1) 0 (-1) (1/4)
  sliderB : VertexBounds S sigma 10 s (-c) (-1/2500) (1/12)
  sliderZ : VertexBounds S sigma 12 (-s) c (-1/8) (1/16)

theorem terminal_coordinateBounds (S : Fin 17 → List PolygonRow) (sigma : ℝ)
    (radius : ℚ) (p : Fin 17 → AnglePose) (hrep : Represents (stateDomains S) p)
    (ha : angleRowsCheck S radius = true)
    (hv : TerminalVertexBounds S sigma radius) :
    CoordinateBounds (chartCentres sigma (fun i => (p i).center))
      (chartAngles (fun i => (p i).angle)) radius := by
  have hb := vertexBounds_pose S sigma p hrep
  constructor
  · exact angleRowsCheck_sound S radius ha p hrep
  · simpa [functional,chartCentres,displacement] using abs_le.mpr (hb _ _ _ _ _ hv.fifthY)
  · simpa [functional,chartCentres,displacement,transverse] using abs_le.mpr (hb _ _ _ _ _ hv.eleventh)
  · simpa [functional,chartCentres,displacement,transverse] using abs_le.mpr (hb _ _ _ _ _ hv.thirteenth)
  · intro i h4 h5 h10 h12
    have hx := abs_le.mpr (hb _ _ _ _ _ (hv.regular i h4 h5 h10 h12).1)
    have hy := abs_le.mpr (hb _ _ _ _ _ (hv.regular i h4 h5 h10 h12).2)
    simpa [functional,chartCentres,displacement] using And.intro hx hy

theorem terminal_sliderBox (S : Fin 17 → List PolygonRow) (sigma radius : ℝ)
    (p : Fin 17 → AnglePose) (hrep : Represents (stateDomains S) p)
    (hv : TerminalVertexBounds S sigma radius)
    (hfit : ∀ q ∈ poseSquare (chartCentres sigma (fun i => (p i).center))
      (chartAngles (fun i => (p i).angle)) 4, q.1 ≤ side) :
    LocalSlider.sliderBox (sliderA (chartCentres sigma (fun i => (p i).center)))
      (sliderB (chartCentres sigma (fun i => (p i).center)))
      (sliderZ (chartCentres sigma (fun i => (p i).center))) := by
  have hb := vertexBounds_pose S sigma p hrep
  have ha0 := sliderA_nonnegative_of_fit _ _ hfit
  have ha := (hb _ _ _ _ _ hv.sliderA).2
  have hbb := hb _ _ _ _ _ hv.sliderB
  have hz := hb _ _ _ _ _ hv.sliderZ
  change 0 ≤ _ ∧ _ ≤ 1/4 ∧ -(1/2500) ≤ _ ∧ _ ≤ 1/12 ∧ -(1/8) ≤ _ ∧ _ ≤ 1/16
  simp only [functional,chartCentres,turn,sliderA,sliderB,sliderZ,displacement,
    Prod.fst_sub,Prod.snd_sub,neg_mul,one_mul,zero_mul,mul_zero,add_zero,zero_add,
    sub_eq_add_neg,Prod.fst_add,Prod.snd_add,Prod.fst_neg,Prod.snd_neg,neg_div] at ha hbb hz ⊢
  exact ⟨ha0,ha,hbb.1,hbb.2,hz.1,hz.2⟩

end
end Sq17.CaptureChart
#print axioms Sq17.CaptureChart.terminal_coordinateBounds
#print axioms Sq17.CaptureChart.terminal_sliderBox
