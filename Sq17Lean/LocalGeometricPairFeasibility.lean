import Sq17Lean.LocalGeometricRows
import Sq17Lean.LocalPerturbationAxes
import Sq17Lean.LocalSliderContacts
import Sq17Lean.LocalSliderOffsets
import Sq17Lean.LocalRigidityParallelRows

namespace Sq17.LocalPerturbation
open Sq17.EndpointGeometry Sq17.LocalRigidity
noncomputable section

def cornerArm (i j : Fin 17) (k : Fin 8) (se sf : Bool) : ℝ :=
  let n := LocalSlider.optionNormal i j k
  let v := EndpointGeometry.directions (LocalSlider.optionOther i j k)
  tangentProjection n (LocalSlider.cornerSign se*v.1-LocalSlider.cornerSign sf*v.2,
    LocalSlider.cornerSign se*v.2+LocalSlider.cornerSign sf*v.1)

theorem movingCornerGap_derivative (a b z : ℝ) (h : Fin 45 → ℝ)
    (i j : Fin 17) (k : Fin 8) (se sf : Bool) :
    deriv (movingCornerGap a b z h i j k se sf) 0 = cornerRow a b z h i j k se sf := by
  have hn1 := congrArg Prod.fst (optionAngle_base i j k)
  have hn2 := congrArg Prod.snd (optionAngle_base i j k)
  have hv1 := congrArg Prod.fst (baseAngle_direction (LocalSlider.optionOther i j k))
  have hv2 := congrArg Prod.snd (baseAngle_direction (LocalSlider.optionOther i j k))
  simp only [Prod.fst,Prod.snd] at hn1 hn2 hv1 hv2
  rw [movingCornerGap,rotatingCornerGap_deriv_zero]
  simp only [Real.sin_sub,Real.cos_sub,hn1,hn2,hv1,hv2]
  simp only [cornerRow,normalTranslation,tangentProjection,Prod.fst_sub,Prod.snd_sub]
  ring

theorem cornerRow_lower {a b z q : ℝ} {h : Fin 45 → ℝ}
    (hbox : LocalSlider.sliderBox a b z) (hq0 : 0 ≤ q) (hq : q ≤ 1/2)
    (hh : ∀ k, |h k| ≤ q) (i j : Fin 17) (k : Fin 8) (se sf : Bool)
    (htight : LocalSlider.cornerGap a b z i j k se sf = 0)
    (hgap : supportGap a b z h i j k) :
    -(100*q^2/2) ≤ cornerRow a b z h i j k se sf := by
  have hdist := LocalSlider.pair_distances_le_ten hbox i j
  have htr := translation_difference_bounds h q hq0 hh i j
  have hb := rotatingCornerGap_linear_lower (optionAngle i j k)
    (angular h (LocalSlider.optionOwner i j k))
    ((LocalSlider.centres a b z j).1-(LocalSlider.centres a b z i).1)
    ((LocalSlider.centres a b z j).2-(LocalSlider.centres a b z i).2)
    ((translation h j).1-(translation h i).1) ((translation h j).2-(translation h i).2)
    (baseAngle (LocalSlider.optionOther i j k)) (angular h (LocalSlider.optionOther i j k))
    (LocalSlider.cornerSign se) (LocalSlider.cornerSign sf) q hq0 hq
    (angular_bounds h q hq0 hh _) (angular_bounds h q hq0 hh _)
    hdist.1 hdist.2 htr.1 htr.2 (LocalSlider.cornerSign_bounds se) (LocalSlider.cornerSign_bounds sf)
    (by change movingCornerGap a b z h i j k se sf 0 = 0; rw [movingCornerGap_zero,htight])
    (supportGap_corner_nonnegative a b z h i j k se sf hgap)
  change -(100*q^2/2) ≤ deriv (movingCornerGap a b z h i j k se sf) 0 at hb
  rwa [movingCornerGap_derivative] at hb

theorem cornerRow_normal_form (a b z : ℝ) (h : Fin 45 → ℝ)
    (i j : Fin 17) (k : Fin 8) (se sf : Bool) (axis : Fin 6) (γ : ℝ)
    (hn : LocalSlider.optionNormal i j k = axes axis) (harm : cornerArm i j k se sf = γ) :
    cornerRow a b z h i j k se sf = normalTranslation h i j (axes axis)+
      (LocalSlider.tangentialOffset a b z i j axis-γ)*angular h (LocalSlider.optionOwner i j k)+
      γ*angular h (LocalSlider.optionOther i j k) := by
  change normalTranslation h i j (LocalSlider.optionNormal i j k)+
    (tangentProjection (LocalSlider.optionNormal i j k)
      (LocalSlider.centres a b z j-LocalSlider.centres a b z i)-cornerArm i j k se sf)*
      angular h (LocalSlider.optionOwner i j k)+cornerArm i j k se sf*
      angular h (LocalSlider.optionOther i j k) = _
  rw [harm,hn]
  rfl

/-- Either retained owner normal gives both common parallel-face rows. -/
theorem parallelRow_lower {a b z q : ℝ} {h : Fin 45 → ℝ}
    (hbox : LocalSlider.sliderBox a b z) (hq0 : 0 ≤ q) (hq : q ≤ 1/2)
    (hh : ∀ k, |h k| ≤ q) (i j : Fin 17) (k : Fin 8) (axis : Fin 6)
    (sm tm sp tp : Bool)
    (hn : LocalSlider.optionNormal i j k = axes axis)
    (hmarm : cornerArm i j k sm tm = -(1/2))
    (hparm : cornerArm i j k sp tp = 1/2)
    (hmzero : LocalSlider.cornerGap a b z i j k sm tm = 0)
    (hpzero : LocalSlider.cornerGap a b z i j k sp tp = 0)
    (hoff : |LocalSlider.tangentialOffset a b z i j axis| ≤ 1)
    (hgap : supportGap a b z h i j k) :
    -(100*q^2/2) ≤ parallelRow a b z h i j axis true ∧
    -(100*q^2/2) ≤ parallelRow a b z h i j axis false := by
  have hm := cornerRow_lower hbox hq0 hq hh i j k sm tm hmzero hgap
  have hp := cornerRow_lower hbox hq0 hq hh i j k sp tp hpzero hgap
  rw [cornerRow_normal_form a b z h i j k sm tm axis (-(1/2)) hn hmarm] at hm
  rw [cornerRow_normal_form a b z h i j k sp tp axis (1/2) hn hparm] at hp
  have hraw :
      (-(100*q^2/2) ≤ normalTranslation h i j (axes axis)+
        (LocalSlider.tangentialOffset a b z i j axis+1/2)*angular h i-(1/2)*angular h j ∧
       -(100*q^2/2) ≤ normalTranslation h i j (axes axis)+
        (LocalSlider.tangentialOffset a b z i j axis-1/2)*angular h i+(1/2)*angular h j) ∨
      (-(100*q^2/2) ≤ normalTranslation h i j (axes axis)+(1/2)*angular h i+
        (LocalSlider.tangentialOffset a b z i j axis-1/2)*angular h j ∧
       -(100*q^2/2) ≤ normalTranslation h i j (axes axis)-(1/2)*angular h i+
        (LocalSlider.tangentialOffset a b z i j axis+1/2)*angular h j) := by
    by_cases hk : k < 4
    · left
      simp only [LocalSlider.optionOwner,LocalSlider.optionOther,if_pos hk] at hm hp
      constructor <;> linarith
    · right
      simp only [LocalSlider.optionOwner,LocalSlider.optionOther,if_neg hk] at hm hp
      constructor <;> linarith
  have hb := parallel_face_rows (normalTranslation h i j (axes axis))
    (LocalSlider.tangentialOffset a b z i j axis) (angular h i) (angular h j) (100*q^2/2) hoff hraw
  simpa [parallelRow,sub_eq_add_neg] using hb

end
end Sq17.LocalPerturbation
#print axioms Sq17.LocalPerturbation.cornerRow_lower
#print axioms Sq17.LocalPerturbation.parallelRow_lower
