import Sq17Lean.LocalSliderGeometry

namespace Sq17.LocalSlider
open Sq17.EndpointGeometry
noncomputable section

def velocity (k : Fin 3) (i : Fin 17) : ℝ × ℝ :=
  ![if i = 4 then (-1,0) else (0,0),
    if i = 10 then (s,-c) else (0,0),
    if i = 12 then (-s,c) else (0,0)] k

theorem centres_affine (a b z : ℝ) (i : Fin 17) :
    centres a b z i = EndpointGeometry.centres i +
      a • velocity 0 i + b • velocity 1 i + z • velocity 2 i := by
  fin_cases i <;> ext <;> simp [centres,offset,velocity] <;> ring

/-- Eight directed edge normals: first square, then second; each has
its own first/second axis, in positive/negative order. -/
def optionOwner (i j : Fin 17) (k : Fin 8) : Fin 17 := if k < 4 then i else j
def optionOther (i j : Fin 17) (k : Fin 8) : Fin 17 := if k < 4 then j else i

def optionNormal (i j : Fin 17) (k : Fin 8) : ℝ × ℝ :=
  let u := directions (optionOwner i j k)
  ![u,-u,(-u.2,u.1),(u.2,-u.1),u,-u,(-u.2,u.1),(u.2,-u.1)] k

def cornerSign (positive : Bool) : ℝ := if positive then 1/2 else -(1/2)

/-- A particular corner of the other square witnesses failure of this
oriented edge inequality. No support-maximization assumption is needed. -/
def cornerGap (a b z : ℝ) (i j : Fin 17) (k : Fin 8) (se sf : Bool) : ℝ :=
  let n := optionNormal i j k
  let v := directions (optionOther i j k)
  n.1*((centres a b z j).1-(centres a b z i).1-
      (cornerSign se*v.1-cornerSign sf*v.2))+
    n.2*((centres a b z j).2-(centres a b z i).2-
      (cornerSign se*v.2+cornerSign sf*v.1))-1/2

def gapCoefficient (i j : Fin 17) (k : Fin 8) (l : Fin 3) : ℝ :=
  let n := optionNormal i j k
  n.1*((velocity l j).1-(velocity l i).1)+
    n.2*((velocity l j).2-(velocity l i).2)

theorem cornerGap_affine (a b z : ℝ) (i j : Fin 17) (k : Fin 8) (se sf : Bool) :
    cornerGap a b z i j k se sf = cornerGap 0 0 0 i j k se sf+
      a*gapCoefficient i j k 0+b*gapCoefficient i j k 1+z*gapCoefficient i j k 2 := by
  simp only [cornerGap,gapCoefficient,centres_affine,Prod.fst_add,Prod.snd_add,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

def cornerUpper (i j : Fin 17) (k : Fin 8) (se sf : Bool) : ℝ :=
  cornerGap 0 0 0 i j k se sf+
    (1/8)*gapCoefficient i j k 0+(311/7500)*gapCoefficient i j k 1-
    (1/32)*gapCoefficient i j k 2+
    (1/8)*|gapCoefficient i j k 0|+(157/3750)*|gapCoefficient i j k 1|+
    (3/32)*|gapCoefficient i j k 2|

theorem cornerGap_le_upper {a b z : ℝ} (h : sliderBox a b z)
    (i j : Fin 17) (k : Fin 8) (se sf : Bool) :
    cornerGap a b z i j k se sf ≤ cornerUpper i j k se sf := by
  rw [cornerGap_affine]
  exact affine_upper h _ _ _ _

theorem optionNormal_unit (i j : Fin 17) (k : Fin 8) :
    (optionNormal i j k).1^2+(optionNormal i j k).2^2=1 := by
  have h := directions_unit (optionOwner i j k)
  fin_cases k <;> norm_num [optionNormal] at * <;> nlinarith

theorem cornerSign_bounds (b : Bool) : |cornerSign b| ≤ (1:ℝ)/2 := by
  cases b <;> norm_num [cornerSign]

end
end Sq17.LocalSlider
#print axioms Sq17.LocalSlider.cornerGap_le_upper
#print axioms Sq17.LocalSlider.optionNormal_unit
