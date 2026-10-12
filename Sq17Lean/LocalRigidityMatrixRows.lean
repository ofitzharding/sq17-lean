import Sq17Lean.LocalRigidityResidualCheck
import Sq17Lean.LocalRigidityMatrixData
import Sq17Lean.LocalGeometricRows
import Sq17Lean.LocalSliderOffsets

namespace Sq17.LocalRigidity.MatrixRows
open scoped BigOperators
open Sq17.LocalPerturbation Sq17.EndpointGeometry
open MatrixData
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
noncomputable section

def sparse000 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v1)*h 0 + (MatrixData.v20)*h 2
theorem matrix_sparse000 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 0 j*h j) = sparse000 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse000,MatrixData.v0]
  <;> ring
theorem geometric_sparse000 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse000 a b z h = geometricRows a b z h 0 := by
  change sparse000 a b z h = wallRow h 0 0 (-1/2)
  norm_num [sparse000,MatrixData.v20,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse001 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v1)*h 0 + (MatrixData.v2)*h 2
theorem matrix_sparse001 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 1 j*h j) = sparse001 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse001,MatrixData.v0]
  <;> ring
theorem geometric_sparse001 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse001 a b z h = geometricRows a b z h 1 := by
  change sparse001 a b z h = wallRow h 0 0 (1/2)
  norm_num [sparse001,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse002 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v1)*h 1 + (MatrixData.v20)*h 2
theorem matrix_sparse002 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 2 j*h j) = sparse002 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse002,MatrixData.v0]
  <;> ring
theorem geometric_sparse002 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse002 a b z h = geometricRows a b z h 2 := by
  change sparse002 a b z h = wallRow h 0 2 (-1/2)
  norm_num [sparse002,MatrixData.v20,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse003 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v1)*h 1 + (MatrixData.v2)*h 2
theorem matrix_sparse003 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 3 j*h j) = sparse003 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse003,MatrixData.v0]
  <;> ring
theorem geometric_sparse003 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse003 a b z h = geometricRows a b z h 3 := by
  change sparse003 a b z h = wallRow h 0 2 (1/2)
  norm_num [sparse003,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse004 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v1)*h 4 + (MatrixData.v20)*h 5
theorem matrix_sparse004 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 4 j*h j) = sparse004 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse004,MatrixData.v0]
  <;> ring
theorem geometric_sparse004 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse004 a b z h = geometricRows a b z h 4 := by
  change sparse004 a b z h = wallRow h 1 2 (-1/2)
  norm_num [sparse004,MatrixData.v20,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse005 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v1)*h 4 + (MatrixData.v2)*h 5
theorem matrix_sparse005 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 5 j*h j) = sparse005 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse005,MatrixData.v0]
  <;> ring
theorem geometric_sparse005 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse005 a b z h = geometricRows a b z h 5 := by
  change sparse005 a b z h = wallRow h 1 2 (1/2)
  norm_num [sparse005,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse006 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v1)*h 6 + (MatrixData.v20)*h 8
theorem matrix_sparse006 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 6 j*h j) = sparse006 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse006,MatrixData.v0]
  <;> ring
theorem geometric_sparse006 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse006 a b z h = geometricRows a b z h 6 := by
  change sparse006 a b z h = wallRow h 2 0 (-1/2)
  norm_num [sparse006,MatrixData.v20,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse007 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v1)*h 6 + (MatrixData.v2)*h 8
theorem matrix_sparse007 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 7 j*h j) = sparse007 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse007,MatrixData.v0]
  <;> ring
theorem geometric_sparse007 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse007 a b z h = geometricRows a b z h 7 := by
  change sparse007 a b z h = wallRow h 2 0 (1/2)
  norm_num [sparse007,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse008 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v1)*h 9 + (MatrixData.v20)*h 11
theorem matrix_sparse008 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 8 j*h j) = sparse008 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse008,MatrixData.v0]
  <;> ring
theorem geometric_sparse008 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse008 a b z h = geometricRows a b z h 8 := by
  change sparse008 a b z h = wallRow h 3 0 (-1/2)
  norm_num [sparse008,MatrixData.v20,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse009 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v1)*h 9 + (MatrixData.v2)*h 11
theorem matrix_sparse009 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 9 j*h j) = sparse009 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse009,MatrixData.v0]
  <;> ring
theorem geometric_sparse009 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse009 a b z h = geometricRows a b z h 9 := by
  change sparse009 a b z h = wallRow h 3 0 (1/2)
  norm_num [sparse009,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse010 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v81)*h 10 + (MatrixData.v20)*h 11
theorem matrix_sparse010 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 10 j*h j) = sparse010 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse010,MatrixData.v0]
  <;> ring
theorem geometric_sparse010 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse010 a b z h = geometricRows a b z h 10 := by
  change sparse010 a b z h = wallRow h 3 3 (-1/2)
  norm_num [sparse010,MatrixData.v81,MatrixData.v20,MatrixData.v2,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse011 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v81)*h 10 + (MatrixData.v2)*h 11
theorem matrix_sparse011 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 11 j*h j) = sparse011 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse011,MatrixData.v0]
  <;> ring
theorem geometric_sparse011 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse011 a b z h = geometricRows a b z h 11 := by
  change sparse011 a b z h = wallRow h 3 3 (1/2)
  norm_num [sparse011,MatrixData.v81,MatrixData.v2,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse012 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v1)*h 12 + (MatrixData.v20)*h 13
theorem matrix_sparse012 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 12 j*h j) = sparse012 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse012,MatrixData.v0]
  <;> ring
theorem geometric_sparse012 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse012 a b z h = geometricRows a b z h 12 := by
  change sparse012 a b z h = wallRow h 4 2 (-1/2)
  norm_num [sparse012,MatrixData.v20,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse013 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v1)*h 12 + (MatrixData.v2)*h 13
theorem matrix_sparse013 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 13 j*h j) = sparse013 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse013,MatrixData.v0]
  <;> ring
theorem geometric_sparse013 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse013 a b z h = geometricRows a b z h 13 := by
  change sparse013 a b z h = wallRow h 4 2 (1/2)
  norm_num [sparse013,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse014 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v81)*h 14 + (MatrixData.v20)*h 16
theorem matrix_sparse014 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 14 j*h j) = sparse014 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse014,MatrixData.v0]
  <;> ring
theorem geometric_sparse014 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse014 a b z h = geometricRows a b z h 14 := by
  change sparse014 a b z h = wallRow h 6 1 (-1/2)
  norm_num [sparse014,MatrixData.v81,MatrixData.v20,MatrixData.v2,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse015 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v81)*h 14 + (MatrixData.v2)*h 16
theorem matrix_sparse015 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 15 j*h j) = sparse015 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse015,MatrixData.v0]
  <;> ring
theorem geometric_sparse015 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse015 a b z h = geometricRows a b z h 15 := by
  change sparse015 a b z h = wallRow h 6 1 (1/2)
  norm_num [sparse015,MatrixData.v81,MatrixData.v2,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse016 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v81)*h 17 + (MatrixData.v20)*h 19
theorem matrix_sparse016 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 16 j*h j) = sparse016 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse016,MatrixData.v0]
  <;> ring
theorem geometric_sparse016 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse016 a b z h = geometricRows a b z h 16 := by
  change sparse016 a b z h = wallRow h 7 1 (-1/2)
  norm_num [sparse016,MatrixData.v81,MatrixData.v20,MatrixData.v2,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse017 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v81)*h 17 + (MatrixData.v2)*h 19
theorem matrix_sparse017 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 17 j*h j) = sparse017 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse017,MatrixData.v0]
  <;> ring
theorem geometric_sparse017 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse017 a b z h = geometricRows a b z h 17 := by
  change sparse017 a b z h = wallRow h 7 1 (1/2)
  norm_num [sparse017,MatrixData.v81,MatrixData.v2,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse018 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v81)*h 18 + (MatrixData.v20)*h 19
theorem matrix_sparse018 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 18 j*h j) = sparse018 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse018,MatrixData.v0]
  <;> ring
theorem geometric_sparse018 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse018 a b z h = geometricRows a b z h 18 := by
  change sparse018 a b z h = wallRow h 7 3 (-1/2)
  norm_num [sparse018,MatrixData.v81,MatrixData.v20,MatrixData.v2,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse019 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v81)*h 18 + (MatrixData.v2)*h 19
theorem matrix_sparse019 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 19 j*h j) = sparse019 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse019,MatrixData.v0]
  <;> ring
theorem geometric_sparse019 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse019 a b z h = geometricRows a b z h 19 := by
  change sparse019 a b z h = wallRow h 7 3 (1/2)
  norm_num [sparse019,MatrixData.v81,MatrixData.v2,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse020 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v1)*h 20 + (MatrixData.v84)*h 22
theorem matrix_sparse020 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 20 j*h j) = sparse020 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse020,MatrixData.v0]
  <;> ring
theorem geometric_sparse020 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse020 a b z h = geometricRows a b z h 20 := by
  change sparse020 a b z h = wallRow h 8 0 (-(c-s)/2)
  norm_num [sparse020,MatrixData.v84,MatrixData.v83,MatrixData.v82,MatrixData.v61,MatrixData.v4,MatrixData.v3,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse021 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v81)*h 37 + (MatrixData.v20)*h 38
theorem matrix_sparse021 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 21 j*h j) = sparse021 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse021,MatrixData.v0]
  <;> ring
theorem geometric_sparse021 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse021 a b z h = geometricRows a b z h 21 := by
  change sparse021 a b z h = wallRow h 14 3 (-1/2)
  norm_num [sparse021,MatrixData.v81,MatrixData.v20,MatrixData.v2,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse022 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v81)*h 37 + (MatrixData.v2)*h 38
theorem matrix_sparse022 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 22 j*h j) = sparse022 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse022,MatrixData.v0]
  <;> ring
theorem geometric_sparse022 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse022 a b z h = geometricRows a b z h 22 := by
  change sparse022 a b z h = wallRow h 14 3 (1/2)
  norm_num [sparse022,MatrixData.v81,MatrixData.v2,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse023 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v81)*h 42 + (MatrixData.v20)*h 44
theorem matrix_sparse023 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 23 j*h j) = sparse023 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse023,MatrixData.v0]
  <;> ring
theorem geometric_sparse023 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse023 a b z h = geometricRows a b z h 23 := by
  change sparse023 a b z h = wallRow h 16 1 (-1/2)
  norm_num [sparse023,MatrixData.v81,MatrixData.v20,MatrixData.v2,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse024 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v81)*h 42 + (MatrixData.v2)*h 44
theorem matrix_sparse024 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 24 j*h j) = sparse024 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse024,MatrixData.v0]
  <;> ring
theorem geometric_sparse024 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse024 a b z h = geometricRows a b z h 24 := by
  change sparse024 a b z h = wallRow h 16 1 (1/2)
  norm_num [sparse024,MatrixData.v81,MatrixData.v2,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse025 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v81)*h 0 + (MatrixData.v92)*h 2 + (MatrixData.v1)*h 3 + (MatrixData.v94)*h 5
theorem matrix_sparse025 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 25 j*h j) = sparse025 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse025,MatrixData.v0]
  <;> ring
theorem geometric_sparse025 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse025 a b z h = geometricRows a b z h 25 := by
  change sparse025 a b z h = parallelRow a b z h 0 1 0 true
  dsimp only [parallelRow]
  rw [LocalSlider.offset_1_2,abs_zero]
  norm_num [sparse025,MatrixData.v94,MatrixData.v93,MatrixData.v92,MatrixData.v91,MatrixData.v90,MatrixData.v89,MatrixData.v88,MatrixData.v87,MatrixData.v85,MatrixData.v81,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse026 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v81)*h 0 + (MatrixData.v96)*h 2 + (MatrixData.v1)*h 3 + (MatrixData.v98)*h 5
theorem matrix_sparse026 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 26 j*h j) = sparse026 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse026,MatrixData.v0]
  <;> ring
theorem geometric_sparse026 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse026 a b z h = geometricRows a b z h 26 := by
  change sparse026 a b z h = parallelRow a b z h 0 1 0 false
  dsimp only [parallelRow]
  rw [LocalSlider.offset_1_2,abs_zero]
  norm_num [sparse026,MatrixData.v98,MatrixData.v97,MatrixData.v96,MatrixData.v95,MatrixData.v91,MatrixData.v90,MatrixData.v89,MatrixData.v88,MatrixData.v87,MatrixData.v85,MatrixData.v81,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse027 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v81)*h 1 + (MatrixData.v104)*h 2 + (MatrixData.v1)*h 7 + (MatrixData.v106)*h 8
theorem matrix_sparse027 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 27 j*h j) = sparse027 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse027,MatrixData.v0]
  <;> ring
theorem geometric_sparse027 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse027 a b z h = geometricRows a b z h 27 := by
  change sparse027 a b z h = parallelRow a b z h 0 2 1 true
  dsimp only [parallelRow]
  rw [LocalSlider.offset_1_3,abs_zero]
  norm_num [sparse027,MatrixData.v106,MatrixData.v105,MatrixData.v104,MatrixData.v103,MatrixData.v102,MatrixData.v101,MatrixData.v100,MatrixData.v99,MatrixData.v87,MatrixData.v85,MatrixData.v81,MatrixData.v40,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse028 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v81)*h 1 + (MatrixData.v108)*h 2 + (MatrixData.v1)*h 7 + (MatrixData.v110)*h 8
theorem matrix_sparse028 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 28 j*h j) = sparse028 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse028,MatrixData.v0]
  <;> ring
theorem geometric_sparse028 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse028 a b z h = geometricRows a b z h 28 := by
  change sparse028 a b z h = parallelRow a b z h 0 2 1 false
  dsimp only [parallelRow]
  rw [LocalSlider.offset_1_3,abs_zero]
  norm_num [sparse028,MatrixData.v110,MatrixData.v109,MatrixData.v108,MatrixData.v107,MatrixData.v103,MatrixData.v102,MatrixData.v101,MatrixData.v100,MatrixData.v99,MatrixData.v87,MatrixData.v85,MatrixData.v81,MatrixData.v40,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse029 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v81)*h 12 + (MatrixData.v119+a*MatrixData.v403)*h 13 + (MatrixData.v1)*h 15 + (MatrixData.v121+a*MatrixData.v405)*h 16
theorem matrix_sparse029 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 29 j*h j) = sparse029 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse029,MatrixData.v0]
  <;> ring
theorem geometric_sparse029 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse029 a b z h = geometricRows a b z h 29 := by
  change sparse029 a b z h = parallelRow a b z h 4 6 1 true
  dsimp only [parallelRow]
  rw [LocalSlider.offset_5_7,abs_neg,abs_of_nonneg hb.1]
  norm_num [sparse029,MatrixData.v405,MatrixData.v404,MatrixData.v403,MatrixData.v402,MatrixData.v345,MatrixData.v344,MatrixData.v343,MatrixData.v342,MatrixData.v341,MatrixData.v340,MatrixData.v339,MatrixData.v338,MatrixData.v337,MatrixData.v336,MatrixData.v335,MatrixData.v334,MatrixData.v121,MatrixData.v120,MatrixData.v119,MatrixData.v118,MatrixData.v117,MatrixData.v116,MatrixData.v115,MatrixData.v114,MatrixData.v113,MatrixData.v112,MatrixData.v111,MatrixData.v81,MatrixData.v40,MatrixData.v21,MatrixData.v20,MatrixData.v7,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse030 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v81)*h 12 + (MatrixData.v123+a*MatrixData.v407)*h 13 + (MatrixData.v1)*h 15 + (MatrixData.v125+a*MatrixData.v409)*h 16
theorem matrix_sparse030 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 30 j*h j) = sparse030 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse030,MatrixData.v0]
  <;> ring
theorem geometric_sparse030 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse030 a b z h = geometricRows a b z h 30 := by
  change sparse030 a b z h = parallelRow a b z h 4 6 1 false
  dsimp only [parallelRow]
  rw [LocalSlider.offset_5_7,abs_neg,abs_of_nonneg hb.1]
  norm_num [sparse030,MatrixData.v409,MatrixData.v408,MatrixData.v407,MatrixData.v406,MatrixData.v349,MatrixData.v348,MatrixData.v347,MatrixData.v346,MatrixData.v342,MatrixData.v341,MatrixData.v340,MatrixData.v339,MatrixData.v338,MatrixData.v337,MatrixData.v336,MatrixData.v335,MatrixData.v334,MatrixData.v125,MatrixData.v124,MatrixData.v123,MatrixData.v122,MatrixData.v118,MatrixData.v117,MatrixData.v116,MatrixData.v115,MatrixData.v114,MatrixData.v113,MatrixData.v112,MatrixData.v111,MatrixData.v81,MatrixData.v40,MatrixData.v21,MatrixData.v20,MatrixData.v7,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse031 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v81)*h 7 + (MatrixData.v135)*h 8 + (MatrixData.v1)*h 21 + (MatrixData.v133)*h 22
theorem matrix_sparse031 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 31 j*h j) = sparse031 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse031,MatrixData.v0]
  <;> ring
theorem geometric_sparse031 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse031 a b z h = geometricRows a b z h 31 := by
  change sparse031 a b z h = cornerRow a b z h 2 8 2 true true
  norm_num [sparse031,MatrixData.v135,MatrixData.v134,MatrixData.v133,MatrixData.v131,MatrixData.v129,MatrixData.v127,MatrixData.v85,MatrixData.v82,MatrixData.v81,MatrixData.v61,MatrixData.v40,MatrixData.v8,MatrixData.v4,MatrixData.v3,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse032 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v143)*h 20 + (MatrixData.v144)*h 21 + (MatrixData.v149)*h 22 + (MatrixData.v3)*h 23 + (MatrixData.v4)*h 24 + (MatrixData.v151)*h 25
theorem matrix_sparse032 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 32 j*h j) = sparse032 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse032,MatrixData.v0]
  <;> ring
theorem geometric_sparse032 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse032 a b z h = geometricRows a b z h 32 := by
  change sparse032 a b z h = parallelRow a b z h 8 9 2 true
  dsimp only [parallelRow]
  have ht := (LocalSlider.face_4_bounds hb).1
  rw [abs_of_nonneg (by linarith)]
  norm_num [sparse032,MatrixData.v151,MatrixData.v150,MatrixData.v149,MatrixData.v148,MatrixData.v147,MatrixData.v146,MatrixData.v145,MatrixData.v144,MatrixData.v143,MatrixData.v142,MatrixData.v141,MatrixData.v140,MatrixData.v139,MatrixData.v138,MatrixData.v137,MatrixData.v136,MatrixData.v81,MatrixData.v61,MatrixData.v30,MatrixData.v29,MatrixData.v28,MatrixData.v27,MatrixData.v26,MatrixData.v25,MatrixData.v24,MatrixData.v23,MatrixData.v22,MatrixData.v14,MatrixData.v13,MatrixData.v10,MatrixData.v8,MatrixData.v4,MatrixData.v3,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse033 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v143)*h 20 + (MatrixData.v144)*h 21 + (MatrixData.v153)*h 22 + (MatrixData.v3)*h 23 + (MatrixData.v4)*h 24 + (MatrixData.v155)*h 25
theorem matrix_sparse033 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 33 j*h j) = sparse033 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse033,MatrixData.v0]
  <;> ring
theorem geometric_sparse033 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse033 a b z h = geometricRows a b z h 33 := by
  change sparse033 a b z h = parallelRow a b z h 8 9 2 false
  dsimp only [parallelRow]
  have ht := (LocalSlider.face_4_bounds hb).1
  rw [abs_of_nonneg (by linarith)]
  norm_num [sparse033,MatrixData.v155,MatrixData.v154,MatrixData.v153,MatrixData.v152,MatrixData.v148,MatrixData.v147,MatrixData.v146,MatrixData.v145,MatrixData.v144,MatrixData.v143,MatrixData.v142,MatrixData.v141,MatrixData.v140,MatrixData.v139,MatrixData.v138,MatrixData.v137,MatrixData.v136,MatrixData.v81,MatrixData.v61,MatrixData.v30,MatrixData.v29,MatrixData.v28,MatrixData.v27,MatrixData.v26,MatrixData.v25,MatrixData.v24,MatrixData.v23,MatrixData.v22,MatrixData.v14,MatrixData.v13,MatrixData.v10,MatrixData.v8,MatrixData.v4,MatrixData.v3,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse034 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v144)*h 9 + (MatrixData.v162)*h 10 + (MatrixData.v166)*h 11 + (MatrixData.v4)*h 23 + (MatrixData.v38)*h 24 + (MatrixData.v168)*h 25
theorem matrix_sparse034 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 34 j*h j) = sparse034 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse034,MatrixData.v0]
  <;> ring
theorem geometric_sparse034 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse034 a b z h = geometricRows a b z h 34 := by
  change sparse034 a b z h = cornerRow a b z h 3 9 7 true false
  norm_num [sparse034,MatrixData.v168,MatrixData.v167,MatrixData.v166,MatrixData.v165,MatrixData.v164,MatrixData.v163,MatrixData.v162,MatrixData.v161,MatrixData.v160,MatrixData.v159,MatrixData.v158,MatrixData.v157,MatrixData.v156,MatrixData.v144,MatrixData.v111,MatrixData.v85,MatrixData.v81,MatrixData.v38,MatrixData.v30,MatrixData.v29,MatrixData.v28,MatrixData.v27,MatrixData.v26,MatrixData.v25,MatrixData.v24,MatrixData.v21,MatrixData.v20,MatrixData.v14,MatrixData.v13,MatrixData.v10,MatrixData.v7,MatrixData.v4,MatrixData.v3,MatrixData.v2,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse035 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v143)*h 6 + (MatrixData.v144)*h 7 + (MatrixData.v176)*h 8 + (MatrixData.v181)*h 26 + (MatrixData.v178+b*MatrixData.v411)*h 27
theorem matrix_sparse035 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 35 j*h j) = sparse035 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse035,MatrixData.v0]
  <;> ring
theorem geometric_sparse035 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse035 a b z h = geometricRows a b z h 35 := by
  change sparse035 a b z h = cornerRow a b z h 2 10 4 true true
  norm_num [sparse035,MatrixData.v411,MatrixData.v410,MatrixData.v357,MatrixData.v356,MatrixData.v355,MatrixData.v354,MatrixData.v353,MatrixData.v352,MatrixData.v351,MatrixData.v350,MatrixData.v181,MatrixData.v180,MatrixData.v179,MatrixData.v178,MatrixData.v177,MatrixData.v176,MatrixData.v175,MatrixData.v174,MatrixData.v173,MatrixData.v172,MatrixData.v171,MatrixData.v170,MatrixData.v169,MatrixData.v144,MatrixData.v143,MatrixData.v126,MatrixData.v85,MatrixData.v81,MatrixData.v61,MatrixData.v38,MatrixData.v37,MatrixData.v36,MatrixData.v35,MatrixData.v34,MatrixData.v33,MatrixData.v32,MatrixData.v31,MatrixData.v19,MatrixData.v16,MatrixData.v15,MatrixData.v11,MatrixData.v4,MatrixData.v3,MatrixData.v2,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse036 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v198)*h 26 + (MatrixData.v193+b*MatrixData.v413)*h 27 + (MatrixData.v3)*h 28 + (MatrixData.v4)*h 29 + (MatrixData.v195+b*MatrixData.v415)*h 30
theorem matrix_sparse036 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 36 j*h j) = sparse036 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse036,MatrixData.v0]
  <;> ring
theorem geometric_sparse036 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse036 a b z h = geometricRows a b z h 36 := by
  change sparse036 a b z h = parallelRow a b z h 10 11 2 true
  dsimp only [parallelRow]
  have ht := (LocalSlider.face_7_bounds hb).1
  rw [abs_of_nonneg (by linarith)]
  norm_num [sparse036,MatrixData.v415,MatrixData.v414,MatrixData.v413,MatrixData.v412,MatrixData.v371,MatrixData.v370,MatrixData.v369,MatrixData.v368,MatrixData.v367,MatrixData.v366,MatrixData.v365,MatrixData.v364,MatrixData.v363,MatrixData.v362,MatrixData.v361,MatrixData.v360,MatrixData.v359,MatrixData.v358,MatrixData.v351,MatrixData.v350,MatrixData.v198,MatrixData.v197,MatrixData.v196,MatrixData.v195,MatrixData.v194,MatrixData.v193,MatrixData.v192,MatrixData.v191,MatrixData.v190,MatrixData.v189,MatrixData.v188,MatrixData.v187,MatrixData.v186,MatrixData.v185,MatrixData.v184,MatrixData.v183,MatrixData.v182,MatrixData.v144,MatrixData.v143,MatrixData.v81,MatrixData.v61,MatrixData.v48,MatrixData.v47,MatrixData.v46,MatrixData.v45,MatrixData.v44,MatrixData.v43,MatrixData.v42,MatrixData.v41,MatrixData.v40,MatrixData.v39,MatrixData.v38,MatrixData.v37,MatrixData.v36,MatrixData.v35,MatrixData.v34,MatrixData.v33,MatrixData.v32,MatrixData.v31,MatrixData.v16,MatrixData.v15,MatrixData.v14,MatrixData.v11,MatrixData.v10,MatrixData.v4,MatrixData.v3,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse037 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v198)*h 26 + (MatrixData.v200+b*MatrixData.v417)*h 27 + (MatrixData.v3)*h 28 + (MatrixData.v4)*h 29 + (MatrixData.v202+b*MatrixData.v419)*h 30
theorem matrix_sparse037 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 37 j*h j) = sparse037 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse037,MatrixData.v0]
  <;> ring
theorem geometric_sparse037 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse037 a b z h = geometricRows a b z h 37 := by
  change sparse037 a b z h = parallelRow a b z h 10 11 2 false
  dsimp only [parallelRow]
  have ht := (LocalSlider.face_7_bounds hb).1
  rw [abs_of_nonneg (by linarith)]
  norm_num [sparse037,MatrixData.v419,MatrixData.v418,MatrixData.v417,MatrixData.v416,MatrixData.v375,MatrixData.v374,MatrixData.v373,MatrixData.v372,MatrixData.v368,MatrixData.v367,MatrixData.v366,MatrixData.v365,MatrixData.v364,MatrixData.v363,MatrixData.v362,MatrixData.v361,MatrixData.v360,MatrixData.v359,MatrixData.v358,MatrixData.v351,MatrixData.v350,MatrixData.v202,MatrixData.v201,MatrixData.v200,MatrixData.v199,MatrixData.v198,MatrixData.v197,MatrixData.v196,MatrixData.v192,MatrixData.v191,MatrixData.v190,MatrixData.v189,MatrixData.v188,MatrixData.v187,MatrixData.v186,MatrixData.v185,MatrixData.v184,MatrixData.v183,MatrixData.v182,MatrixData.v144,MatrixData.v143,MatrixData.v81,MatrixData.v61,MatrixData.v48,MatrixData.v47,MatrixData.v46,MatrixData.v45,MatrixData.v44,MatrixData.v43,MatrixData.v42,MatrixData.v41,MatrixData.v40,MatrixData.v39,MatrixData.v38,MatrixData.v37,MatrixData.v36,MatrixData.v35,MatrixData.v34,MatrixData.v33,MatrixData.v32,MatrixData.v31,MatrixData.v16,MatrixData.v15,MatrixData.v14,MatrixData.v11,MatrixData.v10,MatrixData.v4,MatrixData.v3,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse038 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v144)*h 23 + (MatrixData.v162)*h 24 + (MatrixData.v214)*h 25 + (MatrixData.v4)*h 28 + (MatrixData.v38)*h 29 + (MatrixData.v216)*h 30
theorem matrix_sparse038 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 38 j*h j) = sparse038 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse038,MatrixData.v0]
  <;> ring
theorem geometric_sparse038 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse038 a b z h = geometricRows a b z h 38 := by
  change sparse038 a b z h = parallelRow a b z h 9 11 3 true
  dsimp only [parallelRow]
  have ht := (LocalSlider.face_8_bounds hb).1
  rw [abs_of_nonneg (by linarith)]
  norm_num [sparse038,MatrixData.v216,MatrixData.v215,MatrixData.v214,MatrixData.v213,MatrixData.v212,MatrixData.v211,MatrixData.v210,MatrixData.v209,MatrixData.v208,MatrixData.v207,MatrixData.v206,MatrixData.v205,MatrixData.v204,MatrixData.v203,MatrixData.v162,MatrixData.v156,MatrixData.v144,MatrixData.v81,MatrixData.v48,MatrixData.v47,MatrixData.v46,MatrixData.v45,MatrixData.v44,MatrixData.v43,MatrixData.v42,MatrixData.v41,MatrixData.v40,MatrixData.v39,MatrixData.v38,MatrixData.v30,MatrixData.v29,MatrixData.v28,MatrixData.v27,MatrixData.v26,MatrixData.v25,MatrixData.v24,MatrixData.v15,MatrixData.v14,MatrixData.v13,MatrixData.v10,MatrixData.v4,MatrixData.v3,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse039 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v144)*h 23 + (MatrixData.v162)*h 24 + (MatrixData.v218)*h 25 + (MatrixData.v4)*h 28 + (MatrixData.v38)*h 29 + (MatrixData.v220)*h 30
theorem matrix_sparse039 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 39 j*h j) = sparse039 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse039,MatrixData.v0]
  <;> ring
theorem geometric_sparse039 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse039 a b z h = geometricRows a b z h 39 := by
  change sparse039 a b z h = parallelRow a b z h 9 11 3 false
  dsimp only [parallelRow]
  have ht := (LocalSlider.face_8_bounds hb).1
  rw [abs_of_nonneg (by linarith)]
  norm_num [sparse039,MatrixData.v220,MatrixData.v219,MatrixData.v218,MatrixData.v217,MatrixData.v213,MatrixData.v212,MatrixData.v211,MatrixData.v210,MatrixData.v209,MatrixData.v208,MatrixData.v207,MatrixData.v206,MatrixData.v205,MatrixData.v204,MatrixData.v203,MatrixData.v162,MatrixData.v156,MatrixData.v144,MatrixData.v81,MatrixData.v48,MatrixData.v47,MatrixData.v46,MatrixData.v45,MatrixData.v44,MatrixData.v43,MatrixData.v42,MatrixData.v41,MatrixData.v40,MatrixData.v39,MatrixData.v38,MatrixData.v30,MatrixData.v29,MatrixData.v28,MatrixData.v27,MatrixData.v26,MatrixData.v25,MatrixData.v24,MatrixData.v15,MatrixData.v14,MatrixData.v13,MatrixData.v10,MatrixData.v4,MatrixData.v3,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse040 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v143)*h 3 + (MatrixData.v144)*h 4 + (MatrixData.v176)*h 5 + (MatrixData.v181)*h 31 + (MatrixData.v226+z*MatrixData.v421)*h 32
theorem matrix_sparse040 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 40 j*h j) = sparse040 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse040,MatrixData.v0]
  <;> ring
theorem geometric_sparse040 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse040 a b z h = geometricRows a b z h 40 := by
  change sparse040 a b z h = cornerRow a b z h 1 12 4 true true
  norm_num [sparse040,MatrixData.v421,MatrixData.v420,MatrixData.v383,MatrixData.v382,MatrixData.v381,MatrixData.v380,MatrixData.v379,MatrixData.v378,MatrixData.v377,MatrixData.v376,MatrixData.v226,MatrixData.v225,MatrixData.v224,MatrixData.v223,MatrixData.v222,MatrixData.v221,MatrixData.v181,MatrixData.v180,MatrixData.v179,MatrixData.v177,MatrixData.v176,MatrixData.v175,MatrixData.v174,MatrixData.v144,MatrixData.v143,MatrixData.v126,MatrixData.v85,MatrixData.v81,MatrixData.v61,MatrixData.v60,MatrixData.v59,MatrixData.v58,MatrixData.v57,MatrixData.v56,MatrixData.v55,MatrixData.v54,MatrixData.v53,MatrixData.v52,MatrixData.v51,MatrixData.v50,MatrixData.v49,MatrixData.v40,MatrixData.v19,MatrixData.v18,MatrixData.v17,MatrixData.v16,MatrixData.v11,MatrixData.v4,MatrixData.v3,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse041 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v198)*h 31 + (MatrixData.v238+z*MatrixData.v423)*h 32 + (MatrixData.v3)*h 33 + (MatrixData.v4)*h 34 + (MatrixData.v240+z*MatrixData.v425)*h 35
theorem matrix_sparse041 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 41 j*h j) = sparse041 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse041,MatrixData.v0]
  <;> ring
theorem geometric_sparse041 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse041 a b z h = geometricRows a b z h 41 := by
  change sparse041 a b z h = parallelRow a b z h 12 13 2 true
  dsimp only [parallelRow]
  have ht := (LocalSlider.face_10_bounds hb).1
  rw [abs_of_nonneg (by linarith)]
  norm_num [sparse041,MatrixData.v425,MatrixData.v424,MatrixData.v423,MatrixData.v422,MatrixData.v397,MatrixData.v396,MatrixData.v395,MatrixData.v394,MatrixData.v393,MatrixData.v392,MatrixData.v391,MatrixData.v390,MatrixData.v389,MatrixData.v388,MatrixData.v387,MatrixData.v386,MatrixData.v385,MatrixData.v384,MatrixData.v377,MatrixData.v376,MatrixData.v240,MatrixData.v239,MatrixData.v238,MatrixData.v237,MatrixData.v236,MatrixData.v235,MatrixData.v234,MatrixData.v233,MatrixData.v232,MatrixData.v231,MatrixData.v230,MatrixData.v229,MatrixData.v228,MatrixData.v227,MatrixData.v198,MatrixData.v197,MatrixData.v196,MatrixData.v144,MatrixData.v143,MatrixData.v81,MatrixData.v71,MatrixData.v70,MatrixData.v69,MatrixData.v68,MatrixData.v67,MatrixData.v66,MatrixData.v65,MatrixData.v64,MatrixData.v63,MatrixData.v62,MatrixData.v61,MatrixData.v60,MatrixData.v59,MatrixData.v58,MatrixData.v57,MatrixData.v56,MatrixData.v55,MatrixData.v54,MatrixData.v53,MatrixData.v52,MatrixData.v51,MatrixData.v50,MatrixData.v49,MatrixData.v40,MatrixData.v22,MatrixData.v18,MatrixData.v17,MatrixData.v16,MatrixData.v14,MatrixData.v11,MatrixData.v10,MatrixData.v4,MatrixData.v3,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse042 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v198)*h 31 + (MatrixData.v242+z*MatrixData.v427)*h 32 + (MatrixData.v3)*h 33 + (MatrixData.v4)*h 34 + (MatrixData.v244+z*MatrixData.v429)*h 35
theorem matrix_sparse042 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 42 j*h j) = sparse042 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse042,MatrixData.v0]
  <;> ring
theorem geometric_sparse042 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse042 a b z h = geometricRows a b z h 42 := by
  change sparse042 a b z h = parallelRow a b z h 12 13 2 false
  dsimp only [parallelRow]
  have ht := (LocalSlider.face_10_bounds hb).1
  rw [abs_of_nonneg (by linarith)]
  norm_num [sparse042,MatrixData.v429,MatrixData.v428,MatrixData.v427,MatrixData.v426,MatrixData.v401,MatrixData.v400,MatrixData.v399,MatrixData.v398,MatrixData.v394,MatrixData.v393,MatrixData.v392,MatrixData.v391,MatrixData.v390,MatrixData.v389,MatrixData.v388,MatrixData.v387,MatrixData.v386,MatrixData.v385,MatrixData.v384,MatrixData.v377,MatrixData.v376,MatrixData.v244,MatrixData.v243,MatrixData.v242,MatrixData.v241,MatrixData.v237,MatrixData.v236,MatrixData.v235,MatrixData.v234,MatrixData.v233,MatrixData.v232,MatrixData.v231,MatrixData.v230,MatrixData.v229,MatrixData.v228,MatrixData.v227,MatrixData.v198,MatrixData.v197,MatrixData.v196,MatrixData.v144,MatrixData.v143,MatrixData.v81,MatrixData.v71,MatrixData.v70,MatrixData.v69,MatrixData.v68,MatrixData.v67,MatrixData.v66,MatrixData.v65,MatrixData.v64,MatrixData.v63,MatrixData.v62,MatrixData.v61,MatrixData.v60,MatrixData.v59,MatrixData.v58,MatrixData.v57,MatrixData.v56,MatrixData.v55,MatrixData.v54,MatrixData.v53,MatrixData.v52,MatrixData.v51,MatrixData.v50,MatrixData.v49,MatrixData.v40,MatrixData.v22,MatrixData.v18,MatrixData.v17,MatrixData.v16,MatrixData.v14,MatrixData.v11,MatrixData.v10,MatrixData.v4,MatrixData.v3,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse043 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v144)*h 28 + (MatrixData.v162)*h 29 + (MatrixData.v256)*h 30 + (MatrixData.v4)*h 33 + (MatrixData.v38)*h 34 + (MatrixData.v258)*h 35
theorem matrix_sparse043 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 43 j*h j) = sparse043 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse043,MatrixData.v0]
  <;> ring
theorem geometric_sparse043 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse043 a b z h = geometricRows a b z h 43 := by
  change sparse043 a b z h = parallelRow a b z h 11 13 3 true
  dsimp only [parallelRow]
  have ht := (LocalSlider.face_11_bounds hb).1
  rw [abs_of_nonneg (by linarith)]
  norm_num [sparse043,MatrixData.v258,MatrixData.v257,MatrixData.v256,MatrixData.v255,MatrixData.v254,MatrixData.v253,MatrixData.v252,MatrixData.v251,MatrixData.v250,MatrixData.v249,MatrixData.v248,MatrixData.v247,MatrixData.v246,MatrixData.v245,MatrixData.v162,MatrixData.v156,MatrixData.v144,MatrixData.v81,MatrixData.v71,MatrixData.v70,MatrixData.v69,MatrixData.v68,MatrixData.v67,MatrixData.v66,MatrixData.v65,MatrixData.v64,MatrixData.v63,MatrixData.v62,MatrixData.v48,MatrixData.v47,MatrixData.v46,MatrixData.v45,MatrixData.v44,MatrixData.v43,MatrixData.v42,MatrixData.v41,MatrixData.v40,MatrixData.v39,MatrixData.v38,MatrixData.v22,MatrixData.v17,MatrixData.v15,MatrixData.v14,MatrixData.v10,MatrixData.v4,MatrixData.v3,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse044 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v144)*h 28 + (MatrixData.v162)*h 29 + (MatrixData.v260)*h 30 + (MatrixData.v4)*h 33 + (MatrixData.v38)*h 34 + (MatrixData.v262)*h 35
theorem matrix_sparse044 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 44 j*h j) = sparse044 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse044,MatrixData.v0]
  <;> ring
theorem geometric_sparse044 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse044 a b z h = geometricRows a b z h 44 := by
  change sparse044 a b z h = parallelRow a b z h 11 13 3 false
  dsimp only [parallelRow]
  have ht := (LocalSlider.face_11_bounds hb).1
  rw [abs_of_nonneg (by linarith)]
  norm_num [sparse044,MatrixData.v262,MatrixData.v261,MatrixData.v260,MatrixData.v259,MatrixData.v255,MatrixData.v254,MatrixData.v253,MatrixData.v252,MatrixData.v251,MatrixData.v250,MatrixData.v249,MatrixData.v248,MatrixData.v247,MatrixData.v246,MatrixData.v245,MatrixData.v162,MatrixData.v156,MatrixData.v144,MatrixData.v81,MatrixData.v71,MatrixData.v70,MatrixData.v69,MatrixData.v68,MatrixData.v67,MatrixData.v66,MatrixData.v65,MatrixData.v64,MatrixData.v63,MatrixData.v62,MatrixData.v48,MatrixData.v47,MatrixData.v46,MatrixData.v45,MatrixData.v44,MatrixData.v43,MatrixData.v42,MatrixData.v41,MatrixData.v40,MatrixData.v39,MatrixData.v38,MatrixData.v22,MatrixData.v17,MatrixData.v15,MatrixData.v14,MatrixData.v10,MatrixData.v4,MatrixData.v3,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse045 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v143)*h 23 + (MatrixData.v144)*h 24 + (MatrixData.v268)*h 25 + (MatrixData.v3)*h 36 + (MatrixData.v4)*h 37 + (MatrixData.v176)*h 38
theorem matrix_sparse045 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 45 j*h j) = sparse045 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse045,MatrixData.v0]
  <;> ring
theorem geometric_sparse045 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse045 a b z h = geometricRows a b z h 45 := by
  change sparse045 a b z h = cornerRow a b z h 9 14 0 true true
  norm_num [sparse045,MatrixData.v268,MatrixData.v267,MatrixData.v266,MatrixData.v265,MatrixData.v264,MatrixData.v263,MatrixData.v204,MatrixData.v203,MatrixData.v177,MatrixData.v176,MatrixData.v175,MatrixData.v174,MatrixData.v144,MatrixData.v143,MatrixData.v81,MatrixData.v61,MatrixData.v30,MatrixData.v29,MatrixData.v28,MatrixData.v27,MatrixData.v26,MatrixData.v25,MatrixData.v24,MatrixData.v21,MatrixData.v20,MatrixData.v14,MatrixData.v13,MatrixData.v10,MatrixData.v9,MatrixData.v7,MatrixData.v4,MatrixData.v3,MatrixData.v2,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse046 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v143)*h 33 + (MatrixData.v144)*h 34 + (MatrixData.v276)*h 35 + (MatrixData.v3)*h 42 + (MatrixData.v4)*h 43 + (MatrixData.v176)*h 44
theorem matrix_sparse046 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 46 j*h j) = sparse046 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse046,MatrixData.v0]
  <;> ring
theorem geometric_sparse046 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse046 a b z h = geometricRows a b z h 46 := by
  change sparse046 a b z h = cornerRow a b z h 13 16 0 true true
  norm_num [sparse046,MatrixData.v276,MatrixData.v275,MatrixData.v274,MatrixData.v273,MatrixData.v272,MatrixData.v271,MatrixData.v270,MatrixData.v269,MatrixData.v177,MatrixData.v176,MatrixData.v175,MatrixData.v174,MatrixData.v144,MatrixData.v143,MatrixData.v81,MatrixData.v71,MatrixData.v70,MatrixData.v69,MatrixData.v68,MatrixData.v67,MatrixData.v66,MatrixData.v65,MatrixData.v64,MatrixData.v63,MatrixData.v62,MatrixData.v61,MatrixData.v22,MatrixData.v21,MatrixData.v20,MatrixData.v17,MatrixData.v14,MatrixData.v10,MatrixData.v7,MatrixData.v4,MatrixData.v3,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse047 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v283)*h 36 + (MatrixData.v284)*h 37 + (MatrixData.v287)*h 38 + (MatrixData.v5)*h 39 + (MatrixData.v79)*h 40 + (MatrixData.v289)*h 41
theorem matrix_sparse047 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 47 j*h j) = sparse047 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse047,MatrixData.v0]
  <;> ring
theorem geometric_sparse047 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse047 a b z h = geometricRows a b z h 47 := by
  change sparse047 a b z h = cornerRow a b z h 14 15 4 true false
  norm_num [sparse047,MatrixData.v289,MatrixData.v288,MatrixData.v287,MatrixData.v286,MatrixData.v285,MatrixData.v284,MatrixData.v283,MatrixData.v282,MatrixData.v281,MatrixData.v280,MatrixData.v279,MatrixData.v278,MatrixData.v277,MatrixData.v163,MatrixData.v111,MatrixData.v81,MatrixData.v80,MatrixData.v79,MatrixData.v78,MatrixData.v77,MatrixData.v76,MatrixData.v75,MatrixData.v74,MatrixData.v73,MatrixData.v72,MatrixData.v21,MatrixData.v20,MatrixData.v12,MatrixData.v11,MatrixData.v9,MatrixData.v7,MatrixData.v6,MatrixData.v5,MatrixData.v2,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse048 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v6)*h 17 + (MatrixData.v5)*h 18 + (MatrixData.v301)*h 19 + (MatrixData.v298)*h 39 + (MatrixData.v283)*h 40 + (MatrixData.v303)*h 41
theorem matrix_sparse048 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 48 j*h j) = sparse048 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse048,MatrixData.v0]
  <;> ring
theorem geometric_sparse048 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse048 a b z h = geometricRows a b z h 48 := by
  change sparse048 a b z h = cornerRow a b z h 15 7 2 true true
  norm_num [sparse048,MatrixData.v303,MatrixData.v302,MatrixData.v301,MatrixData.v300,MatrixData.v299,MatrixData.v298,MatrixData.v297,MatrixData.v296,MatrixData.v295,MatrixData.v294,MatrixData.v293,MatrixData.v292,MatrixData.v291,MatrixData.v290,MatrixData.v283,MatrixData.v81,MatrixData.v78,MatrixData.v77,MatrixData.v76,MatrixData.v75,MatrixData.v74,MatrixData.v73,MatrixData.v72,MatrixData.v21,MatrixData.v20,MatrixData.v12,MatrixData.v11,MatrixData.v7,MatrixData.v6,MatrixData.v5,MatrixData.v2,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse049 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v4)*h 14 + (MatrixData.v38)*h 15 + (MatrixData.v166)*h 16 + (MatrixData.v144)*h 33 + (MatrixData.v162)*h 34 + (MatrixData.v308)*h 35
theorem matrix_sparse049 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 49 j*h j) = sparse049 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse049,MatrixData.v0]
  <;> ring
theorem geometric_sparse049 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse049 a b z h = geometricRows a b z h 49 := by
  change sparse049 a b z h = cornerRow a b z h 13 6 3 true false
  norm_num [sparse049,MatrixData.v308,MatrixData.v307,MatrixData.v306,MatrixData.v305,MatrixData.v304,MatrixData.v271,MatrixData.v270,MatrixData.v269,MatrixData.v167,MatrixData.v166,MatrixData.v165,MatrixData.v164,MatrixData.v163,MatrixData.v162,MatrixData.v156,MatrixData.v144,MatrixData.v81,MatrixData.v71,MatrixData.v70,MatrixData.v69,MatrixData.v68,MatrixData.v67,MatrixData.v66,MatrixData.v65,MatrixData.v64,MatrixData.v63,MatrixData.v62,MatrixData.v38,MatrixData.v22,MatrixData.v21,MatrixData.v20,MatrixData.v19,MatrixData.v17,MatrixData.v14,MatrixData.v10,MatrixData.v7,MatrixData.v4,MatrixData.v3,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse050 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v283)*h 39 + (MatrixData.v284)*h 40 + (MatrixData.v313)*h 41 + (MatrixData.v5)*h 42 + (MatrixData.v79)*h 43 + (MatrixData.v287)*h 44
theorem matrix_sparse050 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 50 j*h j) = sparse050 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse050,MatrixData.v0]
  <;> ring
theorem geometric_sparse050 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse050 a b z h = geometricRows a b z h 50 := by
  change sparse050 a b z h = cornerRow a b z h 15 16 0 true false
  norm_num [sparse050,MatrixData.v313,MatrixData.v312,MatrixData.v311,MatrixData.v310,MatrixData.v309,MatrixData.v293,MatrixData.v292,MatrixData.v291,MatrixData.v288,MatrixData.v287,MatrixData.v286,MatrixData.v285,MatrixData.v284,MatrixData.v283,MatrixData.v163,MatrixData.v81,MatrixData.v80,MatrixData.v79,MatrixData.v78,MatrixData.v77,MatrixData.v76,MatrixData.v75,MatrixData.v74,MatrixData.v73,MatrixData.v72,MatrixData.v21,MatrixData.v20,MatrixData.v12,MatrixData.v11,MatrixData.v10,MatrixData.v7,MatrixData.v6,MatrixData.v5,MatrixData.v2,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

def sparse051 (a b z : ℝ) (h : Fin 45 → ℝ) : ℝ := (MatrixData.v143)*h 28 + (MatrixData.v144)*h 29 + (MatrixData.v333)*h 30 + (MatrixData.v3)*h 39 + (MatrixData.v4)*h 40 + (MatrixData.v331)*h 41
theorem matrix_sparse051 (a b z : ℝ) (h : Fin 45 → ℝ) :
    (∑ j, matrixFamily coefficient ![a,b,z] 51 j*h j) = sparse051 a b z h := by
  norm_num [matrixFamily,Fin.sum_univ_succ,coefficient,codes,values,sparse051,MatrixData.v0]
  <;> ring
theorem geometric_sparse051 {a b z : ℝ} (hb : LocalSlider.sliderBox a b z) (h : Fin 45 → ℝ) :
    sparse051 a b z h = geometricRows a b z h 51 := by
  change sparse051 a b z h = cornerRow a b z h 11 15 0 true true
  norm_num [sparse051,MatrixData.v333,MatrixData.v332,MatrixData.v331,MatrixData.v330,MatrixData.v329,MatrixData.v328,MatrixData.v327,MatrixData.v326,MatrixData.v325,MatrixData.v318,MatrixData.v317,MatrixData.v316,MatrixData.v315,MatrixData.v314,MatrixData.v246,MatrixData.v245,MatrixData.v144,MatrixData.v143,MatrixData.v81,MatrixData.v80,MatrixData.v79,MatrixData.v78,MatrixData.v77,MatrixData.v76,MatrixData.v75,MatrixData.v74,MatrixData.v73,MatrixData.v72,MatrixData.v61,MatrixData.v48,MatrixData.v47,MatrixData.v46,MatrixData.v45,MatrixData.v44,MatrixData.v43,MatrixData.v42,MatrixData.v41,MatrixData.v40,MatrixData.v39,MatrixData.v15,MatrixData.v14,MatrixData.v12,MatrixData.v11,MatrixData.v10,MatrixData.v6,MatrixData.v5,MatrixData.v4,MatrixData.v3,MatrixData.v2,MatrixData.v1,MatrixData.v0,wallRow,cornerRow,normalTranslation,tangentProjection,translation,angular,LocalSlider.tangentialOffset,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,LocalSlider.centres,LocalSlider.offset,LocalSlider.velocity,EndpointGeometry.centres,EndpointGeometry.directions,EndpointGeometry.axes,directionKind,rotate]
  <;> ring

theorem matrix_geometric {a b z : ℝ} (hb : LocalSlider.sliderBox a b z)
    (h : Fin 45 → ℝ) (r : Fin 52) :
    (∑ j, matrixFamily coefficient ![a,b,z] r j*h j) = geometricRows a b z h r := by
  fin_cases r
  · exact (matrix_sparse000 a b z h).trans (geometric_sparse000 hb h)
  · exact (matrix_sparse001 a b z h).trans (geometric_sparse001 hb h)
  · exact (matrix_sparse002 a b z h).trans (geometric_sparse002 hb h)
  · exact (matrix_sparse003 a b z h).trans (geometric_sparse003 hb h)
  · exact (matrix_sparse004 a b z h).trans (geometric_sparse004 hb h)
  · exact (matrix_sparse005 a b z h).trans (geometric_sparse005 hb h)
  · exact (matrix_sparse006 a b z h).trans (geometric_sparse006 hb h)
  · exact (matrix_sparse007 a b z h).trans (geometric_sparse007 hb h)
  · exact (matrix_sparse008 a b z h).trans (geometric_sparse008 hb h)
  · exact (matrix_sparse009 a b z h).trans (geometric_sparse009 hb h)
  · exact (matrix_sparse010 a b z h).trans (geometric_sparse010 hb h)
  · exact (matrix_sparse011 a b z h).trans (geometric_sparse011 hb h)
  · exact (matrix_sparse012 a b z h).trans (geometric_sparse012 hb h)
  · exact (matrix_sparse013 a b z h).trans (geometric_sparse013 hb h)
  · exact (matrix_sparse014 a b z h).trans (geometric_sparse014 hb h)
  · exact (matrix_sparse015 a b z h).trans (geometric_sparse015 hb h)
  · exact (matrix_sparse016 a b z h).trans (geometric_sparse016 hb h)
  · exact (matrix_sparse017 a b z h).trans (geometric_sparse017 hb h)
  · exact (matrix_sparse018 a b z h).trans (geometric_sparse018 hb h)
  · exact (matrix_sparse019 a b z h).trans (geometric_sparse019 hb h)
  · exact (matrix_sparse020 a b z h).trans (geometric_sparse020 hb h)
  · exact (matrix_sparse021 a b z h).trans (geometric_sparse021 hb h)
  · exact (matrix_sparse022 a b z h).trans (geometric_sparse022 hb h)
  · exact (matrix_sparse023 a b z h).trans (geometric_sparse023 hb h)
  · exact (matrix_sparse024 a b z h).trans (geometric_sparse024 hb h)
  · exact (matrix_sparse025 a b z h).trans (geometric_sparse025 hb h)
  · exact (matrix_sparse026 a b z h).trans (geometric_sparse026 hb h)
  · exact (matrix_sparse027 a b z h).trans (geometric_sparse027 hb h)
  · exact (matrix_sparse028 a b z h).trans (geometric_sparse028 hb h)
  · exact (matrix_sparse029 a b z h).trans (geometric_sparse029 hb h)
  · exact (matrix_sparse030 a b z h).trans (geometric_sparse030 hb h)
  · exact (matrix_sparse031 a b z h).trans (geometric_sparse031 hb h)
  · exact (matrix_sparse032 a b z h).trans (geometric_sparse032 hb h)
  · exact (matrix_sparse033 a b z h).trans (geometric_sparse033 hb h)
  · exact (matrix_sparse034 a b z h).trans (geometric_sparse034 hb h)
  · exact (matrix_sparse035 a b z h).trans (geometric_sparse035 hb h)
  · exact (matrix_sparse036 a b z h).trans (geometric_sparse036 hb h)
  · exact (matrix_sparse037 a b z h).trans (geometric_sparse037 hb h)
  · exact (matrix_sparse038 a b z h).trans (geometric_sparse038 hb h)
  · exact (matrix_sparse039 a b z h).trans (geometric_sparse039 hb h)
  · exact (matrix_sparse040 a b z h).trans (geometric_sparse040 hb h)
  · exact (matrix_sparse041 a b z h).trans (geometric_sparse041 hb h)
  · exact (matrix_sparse042 a b z h).trans (geometric_sparse042 hb h)
  · exact (matrix_sparse043 a b z h).trans (geometric_sparse043 hb h)
  · exact (matrix_sparse044 a b z h).trans (geometric_sparse044 hb h)
  · exact (matrix_sparse045 a b z h).trans (geometric_sparse045 hb h)
  · exact (matrix_sparse046 a b z h).trans (geometric_sparse046 hb h)
  · exact (matrix_sparse047 a b z h).trans (geometric_sparse047 hb h)
  · exact (matrix_sparse048 a b z h).trans (geometric_sparse048 hb h)
  · exact (matrix_sparse049 a b z h).trans (geometric_sparse049 hb h)
  · exact (matrix_sparse050 a b z h).trans (geometric_sparse050 hb h)
  · exact (matrix_sparse051 a b z h).trans (geometric_sparse051 hb h)
end
end Sq17.LocalRigidity.MatrixRows
#print axioms Sq17.LocalRigidity.MatrixRows.matrix_geometric
