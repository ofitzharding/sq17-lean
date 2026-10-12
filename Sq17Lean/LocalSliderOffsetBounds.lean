import Sq17Lean.LocalSliderCorner

namespace Sq17.LocalSlider
open Sq17.EndpointGeometry
noncomputable section

def offsetCoefficient (i j : Fin 17) (k : Fin 6) (l : Fin 3) : ℝ :=
  -(axes k).2*((velocity l j).1-(velocity l i).1)+
    (axes k).1*((velocity l j).2-(velocity l i).2)

def offsetMiddle (i j : Fin 17) (k : Fin 6) : ℝ :=
  tangentialOffset 0 0 0 i j k+(1/8)*offsetCoefficient i j k 0+
    (311/7500)*offsetCoefficient i j k 1-(1/32)*offsetCoefficient i j k 2

def offsetRadius (i j : Fin 17) (k : Fin 6) : ℝ :=
  (1/8)*|offsetCoefficient i j k 0|+(157/3750)*|offsetCoefficient i j k 1|+
    (3/32)*|offsetCoefficient i j k 2|

theorem tangentialOffset_affine (a b z : ℝ) (i j : Fin 17) (k : Fin 6) :
    tangentialOffset a b z i j k = tangentialOffset 0 0 0 i j k+
      a*offsetCoefficient i j k 0+b*offsetCoefficient i j k 1+z*offsetCoefficient i j k 2 := by
  simp only [tangentialOffset,offsetCoefficient,centres_affine,Prod.fst_add,Prod.snd_add,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

theorem tangentialOffset_bounds {a b z : ℝ} (h : sliderBox a b z)
    (i j : Fin 17) (k : Fin 6) :
    offsetMiddle i j k-offsetRadius i j k ≤ tangentialOffset a b z i j k ∧
    tangentialOffset a b z i j k ≤ offsetMiddle i j k+offsetRadius i j k := by
  have hu := affine_upper h (tangentialOffset 0 0 0 i j k)
    (offsetCoefficient i j k 0) (offsetCoefficient i j k 1) (offsetCoefficient i j k 2)
  have hl := affine_upper h (-tangentialOffset 0 0 0 i j k)
    (-offsetCoefficient i j k 0) (-offsetCoefficient i j k 1) (-offsetCoefficient i j k 2)
  simp only [abs_neg] at hl
  rw [tangentialOffset_affine]
  unfold offsetMiddle offsetRadius
  constructor <;> linarith

end
end Sq17.LocalSlider
