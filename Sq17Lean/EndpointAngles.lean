import Sq17Lean.EndpointGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Exact angle representatives for the rational endpoint directions. -/
namespace Sq17.EndpointGeometry
noncomputable section

theorem cos_twice_arctan (x : ℝ) :
    Real.cos (2*Real.arctan x) = (1-x*x)/(1+x*x) := by
  rw [Real.cos_two_mul,Real.cos_sq_arctan]
  have hx : 1+x^2 ≠ 0 := by positivity
  have hx' : 1+x*x ≠ 0 := by nlinarith [sq_nonneg x]
  field_simp
  <;> ring

theorem sin_twice_arctan (x : ℝ) :
    Real.sin (2*Real.arctan x) = 2*x/(1+x*x) := by
  have hc : Real.cos (Real.arctan x) ≠ 0 := (Real.cos_arctan_pos x).ne'
  have hs : Real.sin (Real.arctan x) = x*Real.cos (Real.arctan x) := by
    apply (div_eq_iff hc).mp
    simpa only [Real.tan_eq_sin_div_cos] using Real.tan_arctan x
  rw [Real.sin_two_mul,hs]
  calc
    _ = 2*x*(Real.cos (Real.arctan x)^2) := by ring
    _ = _ := by rw [Real.cos_sq_arctan];ring

def baseAngle : Fin 17 → ℝ := ![
  0,0,0,0,0,0,0,0,2*Real.arctan t,2*Real.arctan t,
  2*Real.arctan t,2*Real.arctan t,2*Real.arctan t,2*Real.arctan t,
  0,-(2*Real.arctan beta),0]

theorem baseAngle_direction (i : Fin 17) :
    (Real.cos (baseAngle i),Real.sin (baseAngle i)) = directions i := by
  fin_cases i <;> simp [baseAngle,directions,cos_twice_arctan,sin_twice_arctan,c,s,d,e]

#print axioms baseAngle_direction
end
end Sq17.EndpointGeometry
