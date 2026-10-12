import Sq17Lean.FiniteAffineBounds
import Sq17Lean.RationalExpression

/-! Compact finite summaries of a terminal owner domain. The checker binds
every source row and vertex to rational angle and projection intervals. -/
namespace Sq17.CaptureChart
open Sq17.Propagation Sq17.RationalExpression

structure ProjectionBand where
  a : ℚ
  b : ℚ
  bound : Interval
  deriving DecidableEq

def ProjectionBand.eval (b : ProjectionBand) (p : ℚ × ℚ) : ℚ := b.a*p.1+b.b*p.2
def ProjectionBand.check (b : ProjectionBand) (v : ℚ × ℚ) : Bool :=
  decide (b.bound.lo ≤ b.eval v ∧ b.eval v ≤ b.bound.hi)

structure OwnerSummary where
  angle : Interval
  bands : List ProjectionBand
  deriving DecidableEq

def OwnerSummary.check (s : OwnerSummary) (rows : List PolygonRow) : Bool :=
  rows.all fun row => decide (s.angle.lo ≤ row.lo ∧ row.hi ≤ s.angle.hi) &&
    row.vertices.all (fun v => s.bands.all (fun b => b.check v))

theorem OwnerSummary.check_vertices (s : OwnerSummary) (rows : List PolygonRow)
    (hc : s.check rows = true) (row : PolygonRow) (hr : row ∈ rows)
    (v : ℚ × ℚ) (hv : v ∈ row.vertices) (b : ProjectionBand) (hb : b ∈ s.bands) :
    b.bound.lo ≤ b.eval v ∧ b.eval v ≤ b.bound.hi := by
  have h := Bool.and_eq_true_iff.mp ((List.all_eq_true.mp hc) row hr)
  exact of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp h.2) v hv)) b hb)

theorem OwnerSummary.check_angle (s : OwnerSummary) (rows : List PolygonRow)
    (hc : s.check rows = true) (row : PolygonRow) (hr : row ∈ rows) :
    s.angle.lo ≤ row.lo ∧ row.hi ≤ s.angle.hi := by
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp ((List.all_eq_true.mp hc) row hr)).1

theorem OwnerSummary.check_vertex_real (s : OwnerSummary) (rows : List PolygonRow)
    (hc : s.check rows = true) (row : PolygonRow) (hr : row ∈ rows)
    (v : ℚ × ℚ) (hv : v ∈ row.vertices) (b : ProjectionBand) (hb : b ∈ s.bands) :
    b.bound.Holds ((b.a:ℝ)*(realPoint v).1+(b.b:ℝ)*(realPoint v).2) := by
  have h := s.check_vertices rows hc row hr v hv b hb
  simp only [ProjectionBand.eval] at h
  dsimp [Interval.Holds,realPoint]
  exact ⟨by exact_mod_cast h.1,by exact_mod_cast h.2⟩

theorem OwnerSummary.check_pose (s : OwnerSummary) (rows : List PolygonRow)
    (hc : s.check rows = true) (p : AnglePose) (hp : p ∈ rowsRegion rows) :
    s.angle.Holds p.angle ∧ ∀ b ∈ s.bands,
      b.bound.Holds ((b.a:ℝ)*p.center.1+(b.b:ℝ)*p.center.2) := by
  obtain ⟨row,hr,hp⟩ := hp
  have ha := s.check_angle rows hc row hr
  constructor
  · have hlo : (s.angle.lo:ℝ) ≤ row.lo := by exact_mod_cast ha.1
    have hhi : (row.hi:ℝ) ≤ s.angle.hi := by exact_mod_cast ha.2
    exact ⟨hlo.trans hp.2.1,hp.2.2.trans hhi⟩
  · intro b hb
    have h := affineHull_bounds row.vertices b.a b.b 0 b.bound.lo b.bound.hi
      (fun v hv => by
        have hv' := s.check_vertices rows hc row hr v hv b hb
        simp only [ProjectionBand.eval] at hv'
        simpa only [add_zero] using
          (show (b.bound.lo:ℝ) ≤ (b.a:ℝ)*(v.1:ℝ)+(b.b:ℝ)*(v.2:ℝ) ∧
            (b.a:ℝ)*(v.1:ℝ)+(b.b:ℝ)*(v.2:ℝ) ≤ (b.bound.hi:ℝ) by
              exact_mod_cast hv')) p.center hp.1
    simpa only [add_zero,Interval.Holds] using h

end Sq17.CaptureChart
#print axioms Sq17.CaptureChart.OwnerSummary.check_pose
