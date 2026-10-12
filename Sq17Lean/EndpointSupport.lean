import Sq17Lean.EndpointIntervals
import Sq17Lean.WallSquareSupport

namespace Sq17.EndpointGeometry
open Sq17.WallCapacity
noncomputable section

def baseDirection : Fin 3 → ℝ × ℝ := ![(1,0),(c,s),(d,-e)]
def directionKind : Fin 17 → Fin 3 := ![0,0,0,0,0,0,0,0,1,1,1,1,1,1,0,2,0]
def axes : Fin 6 → ℝ × ℝ := ![(1,0),(0,1),(c,s),(s,-c),(d,-e),(e,d)]
def axisKind : Fin 6 → Fin 3 := ![0,0,1,1,2,2]
def crossSupport : ℝ := (c*d-s*e+s*d+c*e)/2
def supportTable : Fin 3 → Fin 3 → ℝ := ![
  ![1/2,(c+s)/2,(d+e)/2],
  ![(c+s)/2,1/2,crossSupport],
  ![(d+e)/2,crossSupport,1/2]]

theorem directions_kind (i : Fin 17) : directions i = baseDirection (directionKind i) := by
  fin_cases i <;> rfl

theorem axes_unit (k : Fin 6) : (axes k).1^2+(axes k).2^2=1 := by
  fin_cases k <;> simp [axes,cs_unit,de_unit] <;> nlinarith [cs_unit,de_unit]

theorem support_table (j : Fin 3) (k : Fin 6) :
    squareSupport (baseDirection j).1 (baseDirection j).2 (axes k).1 (axes k).2 =
      supportTable j (axisKind k) := by
  have hc := cs_positive.1.le
  have hs := cs_positive.2.le
  have hd := de_positive.1.le
  have he := de_positive.2.le
  have hcs := cs_unit
  have hde := de_unit
  have hcross := EndpointIntervals.cross_positive.le
  have hsum : 0 ≤ c*e+s*d := add_nonneg (mul_nonneg hc he) (mul_nonneg hs hd)
  have habs (x : ℝ) : |x| = if 0 ≤ x then x else -x := by
    split_ifs with hx
    · exact abs_of_nonneg hx
    · exact abs_of_neg (lt_of_not_ge hx)
  fin_cases j <;> fin_cases k <;>
    norm_num [baseDirection,axes,axisKind,supportTable,crossSupport,squareSupport] <;>
    simp only [habs] <;> split_ifs <;> nlinarith

theorem square_support_table (i : Fin 17) (k : Fin 6) :
    squareSupport (directions i).1 (directions i).2 (axes k).1 (axes k).2 =
      supportTable (directionKind i) (axisKind k) := by
  rw [directions_kind]
  exact support_table _ _

def pairGap (i j : Fin 17) (k : Fin 6) : ℝ :=
  (axes k).1*((centres j).1-(centres i).1)+(axes k).2*((centres j).2-(centres i).2)-
    supportTable (directionKind i) (axisKind k)-supportTable (directionKind j) (axisKind k)

def wallGap (i : Fin 17) (k : Fin 4) : ℝ :=
  (![ (centres i).1,side-(centres i).1,(centres i).2,side-(centres i).2] k)-
    supportTable (directionKind i) 0

end
end Sq17.EndpointGeometry
#print axioms Sq17.EndpointGeometry.support_table
#print axioms Sq17.EndpointGeometry.square_support_table
