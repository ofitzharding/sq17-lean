import Sq17Lean.ArctanCheck
import Sq17Lean.EndpointIntervals
import Sq17Lean.EndpointAngles

namespace Sq17.EndpointIntervals
open Sq17.EndpointGeometry Sq17.RationalExpression Sq17.ArctanCheck
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
def tArctanCert : Certificate := ⟨16,⟨(9051097332833/25000000000000),(36204389331533/100000000000000)⟩,⟨(17368189820411/50000000000000),(34736379641001/100000000000000)⟩⟩
theorem t_arctan_checked : tArctanCert.check = true := by decide +kernel
theorem t_arctan_bounds : (⟨(17368189820411/50000000000000),(34736379641001/100000000000000)⟩ : Interval).Holds (Real.arctan t) := by
  apply Certificate.check_sound tArctanCert t _ t_arctan_checked
  exact Interval.weaken tRange tArctanCert.input t (by decide +kernel) t_holds

def betaArctanCert : Certificate := ⟨16,⟨(33094867472173/100000000000000),(16547433736187/50000000000000)⟩,⟨(31960282846819/100000000000000),(31960282847001/100000000000000)⟩⟩
theorem beta_arctan_checked : betaArctanCert.check = true := by decide +kernel
theorem beta_arctan_bounds : (⟨(31960282846819/100000000000000),(31960282847001/100000000000000)⟩ : Interval).Holds (Real.arctan beta) := by
  apply Certificate.check_sound betaArctanCert beta _ beta_arctan_checked
  exact Interval.weaken betaRange betaArctanCert.input beta (by decide +kernel) beta_holds

def thetaRange : Interval := ⟨(17368189820411/25000000000000),(34736379641001/50000000000000)⟩
def phiRange : Interval := ⟨(-31960282847001/50000000000000),(-31960282846819/50000000000000)⟩
theorem theta_bounds : thetaRange.Holds (2*Real.arctan t) := by
  have h := t_arctan_bounds
  constructor <;> norm_num [thetaRange,Interval.Holds] at * <;> linarith

theorem phi_bounds : phiRange.Holds (-(2*Real.arctan beta)) := by
  have h := beta_arctan_bounds
  constructor <;> norm_num [phiRange,Interval.Holds] at * <;> linarith

def baseAngleRange : Fin 17 → Interval := ![
  ⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,
  thetaRange,thetaRange,thetaRange,thetaRange,thetaRange,thetaRange,
  ⟨0,0⟩,phiRange,⟨0,0⟩]

theorem baseAngle_bounds (i : Fin 17) : (baseAngleRange i).Holds (baseAngle i) := by
  fin_cases i <;> first
    | exact theta_bounds
    | exact phi_bounds
    | norm_num [baseAngleRange,baseAngle,Interval.Holds]

theorem theta_width : thetaRange.hi-thetaRange.lo ≤ 1/100000000000 := by decide +kernel
theorem phi_width : phiRange.hi-phiRange.lo ≤ 1/100000000000 := by decide +kernel

end Sq17.EndpointIntervals
#print axioms Sq17.EndpointIntervals.baseAngle_bounds
