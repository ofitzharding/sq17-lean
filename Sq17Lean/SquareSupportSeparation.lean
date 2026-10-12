import Sq17Lean.WallSquareSupport
import Mathlib.Analysis.Normed.Operator.Banach

/-! Sufficient support-gap certificates for closed unit-square containment
and disjoint interiors. Non-strict gaps allow legal contact. -/
namespace Sq17.WallCapacity

noncomputable def projection (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ+b • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem projection_apply (a b : ℝ) (z : ℝ × ℝ) : projection a b z = a*z.1+b*z.2 := rfl

theorem squareSupport_interior_upper (p z : ℝ × ℝ) (ux uy a b : ℝ)
    (hu : ux^2+uy^2=1) (hm : a^2+b^2=1)
    (hz : z ∈ interior (Sq17.sq p.1 p.2 ux uy)) :
    a*z.1+b*z.2 < a*p.1+b*p.2+squareSupport ux uy a b := by
  let f := projection a b
  have hf : Function.Surjective f := by
    intro t
    refine ⟨(a*t,b*t),?_⟩
    change a*(a*t)+b*(b*t)=t
    calc
      _ = (a^2+b^2)*t := by ring
      _ = t := by rw [hm]; ring
  have hsub : Sq17.sq p.1 p.2 ux uy ⊆ f ⁻¹' Set.Iic
      (a*p.1+b*p.2+squareSupport ux uy a b) :=
    fun z hz => squareSupport_upper p.1 p.2 ux uy a b hu z hz
  have h := interior_mono hsub hz
  rw [f.interior_preimage hf,interior_Iic] at h
  exact h

theorem support_gap_disjoint (p q : ℝ × ℝ) (ux uy vx vy a b : ℝ)
    (hu : ux^2+uy^2=1) (hv : vx^2+vy^2=1) (hm : a^2+b^2=1)
    (hgap : squareSupport ux uy a b+squareSupport vx vy a b ≤
      a*(q.1-p.1)+b*(q.2-p.2)) :
    Disjoint (interior (Sq17.sq p.1 p.2 ux uy))
      (interior (Sq17.sq q.1 q.2 vx vy)) := by
  apply Set.disjoint_left.mpr
  intro z hp hq
  have h1 := squareSupport_interior_upper p z ux uy a b hu hm hp
  have h2 := squareSupport_upper q.1 q.2 vx vy (-a) (-b) hv z (interior_subset hq)
  rw [squareSupport_neg] at h2
  nlinarith only [h1,h2,hgap]

theorem support_walls_contained (p : ℝ × ℝ) (ux uy L : ℝ)
    (hu : ux^2+uy^2=1)
    (hx0 : squareSupport ux uy 1 0 ≤ p.1)
    (hx1 : squareSupport ux uy 1 0 ≤ L-p.1)
    (hy0 : squareSupport ux uy 0 1 ≤ p.2)
    (hy1 : squareSupport ux uy 0 1 ≤ L-p.2) :
    Sq17.sq p.1 p.2 ux uy ⊆ {z | 0 ≤ z.1 ∧ z.1 ≤ L ∧ 0 ≤ z.2 ∧ z.2 ≤ L} := by
  intro z hz
  have h1 := squareSupport_upper p.1 p.2 ux uy 1 0 hu z hz
  have h2 := squareSupport_upper p.1 p.2 ux uy (-1) 0 hu z hz
  have h3 := squareSupport_upper p.1 p.2 ux uy 0 1 hu z hz
  have h4 := squareSupport_upper p.1 p.2 ux uy 0 (-1) hu z hz
  have hsx : squareSupport ux uy (-1) 0 = squareSupport ux uy 1 0 := by simpa using squareSupport_neg ux uy 1 0
  have hsy : squareSupport ux uy 0 (-1) = squareSupport ux uy 0 1 := by simpa using squareSupport_neg ux uy 0 1
  rw [hsx] at h2
  rw [hsy] at h4
  exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

end Sq17.WallCapacity
#print axioms Sq17.WallCapacity.support_gap_disjoint
#print axioms Sq17.WallCapacity.support_walls_contained
