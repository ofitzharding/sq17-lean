import Sq17Lean.LocalRigidityCurvature

/-! Uniform analytic curvature for the smooth signed contact-gap formulas.
The hypotheses below are concrete displacement, speed, and corner bounds;
there is no assumed derivative bound. -/
namespace Sq17.LocalRigidity

noncomputable def rotatingGap (α ω A B C D β ν E F t : ℝ) : ℝ :=
  trigAffine α ω A B C D t+trigAffine β ν E F 0 0 t-1/2

theorem rotatingGap_contDiff (α ω A B C D β ν E F : ℝ) :
    ContDiff ℝ 2 (rotatingGap α ω A B C D β ν E F) := by
  unfold rotatingGap trigAffine
  fun_prop

theorem rotatingGap_second (α ω A B C D β ν E F : ℝ) :
    iteratedDeriv 2 (rotatingGap α ω A B C D β ν E F) =
      fun t => trigAffineSecond α ω A B C D t+trigAffineSecond β ν E F 0 0 t := by
  have hd : deriv (rotatingGap α ω A B C D β ν E F) =
      fun t => trigAffineFirst α ω A B C D t+trigAffineFirst β ν E F 0 0 t := by
    apply funext; intro t
    exact (((trigAffine_hasDerivAt α ω A B C D t).add
      (trigAffine_hasDerivAt β ν E F 0 0 t)).sub_const (1/2)).deriv
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  rw [hd]
  apply funext; intro t
  exact ((trigAffineFirst_hasDerivAt α ω A B C D t).add
    (trigAffineFirst_hasDerivAt β ν E F 0 0 t)).deriv

private theorem affine_coord_bound (A C t q : ℝ)
    (hA : |A| ≤ 10) (hC : |C| ≤ 2*q) (ht : |t| ≤ 1) (hq : q ≤ 1/2) :
    |A+t*C| ≤ 11 := by
  have hm := mul_le_mul_of_nonneg_right ht (abs_nonneg C)
  have htC : |t*C| ≤ |C| := by rw [abs_mul]; simpa using hm
  have h := abs_add_le A (t*C)
  linarith

/-- The affine-centre portion has curvature at most 30q². -/
theorem centre_curvature_bound (α ω A B C D t q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/2) (ht : |t| ≤ 1)
    (hω : |ω| ≤ q) (hA : |A| ≤ 10) (hB : |B| ≤ 10)
    (hC : |C| ≤ 2*q) (hD : |D| ≤ 2*q) :
    |trigAffineSecond α ω A B C D t| ≤ 30*q^2 := by
  have ha := affine_coord_bound A C t q hA hC ht hq
  have hb := affine_coord_bound B D t q hB hD ht hq
  have hw : ω^2 ≤ q^2 := by
    have hh := mul_self_le_mul_self (abs_nonneg ω) hω
    nlinarith [sq_abs ω]
  have hm1 := mul_le_mul hw (show |A+t*C|+|B+t*D| ≤ 22 by linarith)
    (by positivity) (sq_nonneg q)
  have hm2 := mul_le_mul (show 2*|ω| ≤ 2*q by linarith)
    (show |C|+|D| ≤ 4*q by linarith) (by positivity) (by positivity)
  have h := trigAffine_second_bound α ω A B C D t
  nlinarith

/-- A unit-square corner in relative rotating coordinates has curvature
at most 4q² whenever its angular speed is at most 2q. -/
theorem corner_curvature_bound (β ν E F t q : ℝ)
    (hq : 0 ≤ q) (hν : |ν| ≤ 2*q) (hEF : |E|+|F| ≤ 1) :
    |trigAffineSecond β ν E F 0 0 t| ≤ 4*q^2 := by
  have hv : ν^2 ≤ 4*q^2 := by
    have hh := mul_self_le_mul_self (abs_nonneg ν) hν
    nlinarith [sq_abs ν]
  have hm := mul_le_mul hv hEF (by positivity) (by positivity)
  have h := trigAffine_second_bound β ν E F 0 0 t
  norm_num at h
  nlinarith

/-- A deliberately generous bound, sufficient at the captured radius1e-7. -/
theorem rotatingGap_curvature (α ω A B C D β ν E F t q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/2) (ht : |t| ≤ 1)
    (hω : |ω| ≤ q) (hν : |ν| ≤ 2*q)
    (hA : |A| ≤ 10) (hB : |B| ≤ 10)
    (hC : |C| ≤ 2*q) (hD : |D| ≤ 2*q) (hEF : |E|+|F| ≤ 1) :
    |iteratedDeriv 2 (rotatingGap α ω A B C D β ν E F) t| ≤ 100*q^2 := by
  rw [rotatingGap_second]
  have h1 := centre_curvature_bound α ω A B C D t q hq0 hq ht hω hA hB hC hD
  have h2 := corner_curvature_bound β ν E F t q hq0 hν hEF
  have hsum := abs_add_le (trigAffineSecond α ω A B C D t)
    (trigAffineSecond β ν E F 0 0 t)
  nlinarith [sq_nonneg q]

/-- For this explicit gap formula, tightness and endpoint feasibility now
imply the necessary Taylor row, with no remaining curvature hypothesis. -/
theorem rotatingGap_linear_lower (α ω A B C D β ν E F q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/2) (hω : |ω| ≤ q) (hν : |ν| ≤ 2*q)
    (hA : |A| ≤ 10) (hB : |B| ≤ 10)
    (hC : |C| ≤ 2*q) (hD : |D| ≤ 2*q) (hEF : |E|+|F| ≤ 1)
    (hbase : rotatingGap α ω A B C D β ν E F 0 = 0)
    (hfeasible : 0 ≤ rotatingGap α ω A B C D β ν E F 1) :
    -(100*q^2/2) ≤ deriv (rotatingGap α ω A B C D β ν E F) 0 := by
  apply segment_linear_lower _ 100 q (rotatingGap_contDiff ..) hbase hfeasible
  intro t ht
  apply rotatingGap_curvature α ω A B C D β ν E F t q hq0 hq
    (by rw [abs_of_pos ht.1]; exact ht.2.le) hω hν hA hB hC hD hEF

#print axioms rotatingGap_curvature
#print axioms rotatingGap_linear_lower
end Sq17.LocalRigidity
