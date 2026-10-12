import Sq17Lean.LocalPerturbationCoordinates
import Sq17Lean.LocalSliderCorner

/-! Geometric linear forms for the 52 local constraints. These definitions
use square translations, angular velocities, contact normals, and actual
base centres. The numerical matrix is not used in their definition. -/
namespace Sq17.LocalPerturbation
open Sq17.EndpointGeometry
noncomputable section

def normalTranslation (h : Fin 45 → ℝ) (i j : Fin 17) (n : ℝ × ℝ) : ℝ :=
  n.1*((translation h j).1-(translation h i).1)+
  n.2*((translation h j).2-(translation h i).2)

def tangentProjection (n v : ℝ × ℝ) : ℝ := -n.2*v.1+n.1*v.2

def wallRow (h : Fin 45 → ℝ) (i : Fin 17) (wall : Fin 4) (angularWeight : ℝ) : ℝ :=
  ![(translation h i).1,-(translation h i).1,
    (translation h i).2,-(translation h i).2] wall+angularWeight*angular h i

def parallelRow (a b z : ℝ) (h : Fin 45 → ℝ)
    (i j : Fin 17) (axis : Fin 6) (plus : Bool) : ℝ :=
  let n := EndpointGeometry.axes axis
  let τ := LocalSlider.tangentialOffset a b z i j axis
  let arm := (1-|τ|)/2
  let δ := if plus then arm else -arm
  normalTranslation h i j n+(τ/2+δ)*angular h i+(τ/2-δ)*angular h j

def cornerRow (a b z : ℝ) (h : Fin 45 → ℝ)
    (i j : Fin 17) (option : Fin 8) (se sf : Bool) : ℝ :=
  let n := LocalSlider.optionNormal i j option
  let owner := LocalSlider.optionOwner i j option
  let other := LocalSlider.optionOther i j option
  let v := EndpointGeometry.directions other
  let corner := (LocalSlider.cornerSign se*v.1-LocalSlider.cornerSign sf*v.2,
    LocalSlider.cornerSign se*v.2+LocalSlider.cornerSign sf*v.1)
  let τ := tangentProjection n (LocalSlider.centres a b z j-LocalSlider.centres a b z i)
  let hp := tangentProjection n corner
  normalTranslation h i j n+(τ-hp)*angular h owner+hp*angular h other

/-- Order agrees with the source's 25 wall rows followed by 27 pair rows.
The first parallel row uses the positive arm; wall rows use negative then
positive angular half-weight. -/
def geometricRows (a b z : ℝ) (h : Fin 45 → ℝ) : Fin 52 → ℝ := ![
  wallRow h 0 0 (-1/2), wallRow h 0 0 (1/2),
  wallRow h 0 2 (-1/2), wallRow h 0 2 (1/2),
  wallRow h 1 2 (-1/2), wallRow h 1 2 (1/2),
  wallRow h 2 0 (-1/2), wallRow h 2 0 (1/2),
  wallRow h 3 0 (-1/2), wallRow h 3 0 (1/2),
  wallRow h 3 3 (-1/2), wallRow h 3 3 (1/2),
  wallRow h 4 2 (-1/2), wallRow h 4 2 (1/2),
  wallRow h 6 1 (-1/2), wallRow h 6 1 (1/2),
  wallRow h 7 1 (-1/2), wallRow h 7 1 (1/2),
  wallRow h 7 3 (-1/2), wallRow h 7 3 (1/2),
  wallRow h 8 0 (-(c-s)/2),
  wallRow h 14 3 (-1/2), wallRow h 14 3 (1/2),
  wallRow h 16 1 (-1/2), wallRow h 16 1 (1/2),
  parallelRow a b z h 0 1 0 true, parallelRow a b z h 0 1 0 false,
  parallelRow a b z h 0 2 1 true, parallelRow a b z h 0 2 1 false,
  parallelRow a b z h 4 6 1 true, parallelRow a b z h 4 6 1 false,
  cornerRow a b z h 2 8 2 true true,
  parallelRow a b z h 8 9 2 true, parallelRow a b z h 8 9 2 false,
  cornerRow a b z h 3 9 7 true false,
  cornerRow a b z h 2 10 4 true true,
  parallelRow a b z h 10 11 2 true, parallelRow a b z h 10 11 2 false,
  parallelRow a b z h 9 11 3 true, parallelRow a b z h 9 11 3 false,
  cornerRow a b z h 1 12 4 true true,
  parallelRow a b z h 12 13 2 true, parallelRow a b z h 12 13 2 false,
  parallelRow a b z h 11 13 3 true, parallelRow a b z h 11 13 3 false,
  cornerRow a b z h 9 14 0 true true,
  cornerRow a b z h 13 16 0 true true,
  cornerRow a b z h 14 15 4 true false,
  cornerRow a b z h 15 7 2 true true,
  cornerRow a b z h 13 6 3 true false,
  cornerRow a b z h 15 16 0 true false,
  cornerRow a b z h 11 15 0 true true]

end
end Sq17.LocalPerturbation
