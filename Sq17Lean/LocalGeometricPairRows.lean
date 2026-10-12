import Sq17Lean.LocalGeometricPairFeasibility

namespace Sq17.LocalPerturbation
open Sq17.EndpointGeometry
set_option maxHeartbeats 3000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def parallelCorners : Fin 16 → Fin 19 × Fin 8 × Bool × Bool × Bool × Bool := ![(0,0,true,false,true,true),(0,4,true,false,true,true),(1,2,true,true,false,true),(1,6,true,true,false,true),(2,2,true,true,false,true),(2,6,true,true,false,true),(4,0,true,false,true,true),(4,4,true,false,true,true),(7,0,true,false,true,true),(7,4,true,false,true,true),(8,3,false,false,true,false),(8,7,false,false,true,false),(10,0,true,false,true,true),(10,4,true,false,true,true),(11,3,false,false,true,false),(11,7,false,false,true,false)]
theorem parallel_minus_arm (r : Fin 16) :
    cornerArm (LocalSlider.contactPairs (parallelCorners r).1).1
      (LocalSlider.contactPairs (parallelCorners r).1).2.1 (parallelCorners r).2.1
      (parallelCorners r).2.2.1 (parallelCorners r).2.2.2.1 = -(1/2) := by
  fin_cases r <;> norm_num [parallelCorners,LocalSlider.contactPairs,cornerArm,
    tangentProjection,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,
    LocalSlider.cornerSign,EndpointGeometry.directions] <;> nlinarith [cs_unit]
theorem parallel_minus_tight (a b z : ℝ) (r : Fin 16) :
    LocalSlider.cornerGap a b z (LocalSlider.contactPairs (parallelCorners r).1).1
      (LocalSlider.contactPairs (parallelCorners r).1).2.1 (parallelCorners r).2.1
      (parallelCorners r).2.2.1 (parallelCorners r).2.2.2.1 = 0 := by
  fin_cases r
  · change LocalSlider.cornerGap a b z 0 1 0 true false = 0
    have he : LocalSlider.cornerGap a b z 0 1 0 true false = LocalSlider.pairGap a b z 0 1 0 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_1_2]
  · change LocalSlider.cornerGap a b z 0 1 4 true false = 0
    have he : LocalSlider.cornerGap a b z 0 1 4 true false = LocalSlider.pairGap a b z 0 1 0 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_1_2]
  · change LocalSlider.cornerGap a b z 0 2 2 true true = 0
    have he : LocalSlider.cornerGap a b z 0 2 2 true true = LocalSlider.pairGap a b z 0 2 1 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_1_3]
  · change LocalSlider.cornerGap a b z 0 2 6 true true = 0
    have he : LocalSlider.cornerGap a b z 0 2 6 true true = LocalSlider.pairGap a b z 0 2 1 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_1_3]
  · change LocalSlider.cornerGap a b z 4 6 2 true true = 0
    have he : LocalSlider.cornerGap a b z 4 6 2 true true = LocalSlider.pairGap a b z 4 6 1 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_5_7]
  · change LocalSlider.cornerGap a b z 4 6 6 true true = 0
    have he : LocalSlider.cornerGap a b z 4 6 6 true true = LocalSlider.pairGap a b z 4 6 1 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_5_7]
  · change LocalSlider.cornerGap a b z 8 9 0 true false = 0
    have he : LocalSlider.cornerGap a b z 8 9 0 true false = LocalSlider.pairGap a b z 8 9 2 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_9_10]
  · change LocalSlider.cornerGap a b z 8 9 4 true false = 0
    have he : LocalSlider.cornerGap a b z 8 9 4 true false = LocalSlider.pairGap a b z 8 9 2 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_9_10]
  · change LocalSlider.cornerGap a b z 10 11 0 true false = 0
    have he : LocalSlider.cornerGap a b z 10 11 0 true false = LocalSlider.pairGap a b z 10 11 2 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_11_12]
  · change LocalSlider.cornerGap a b z 10 11 4 true false = 0
    have he : LocalSlider.cornerGap a b z 10 11 4 true false = LocalSlider.pairGap a b z 10 11 2 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_11_12]
  · change LocalSlider.cornerGap a b z 9 11 3 false false = 0
    have he : LocalSlider.cornerGap a b z 9 11 3 false false = LocalSlider.pairGap a b z 9 11 3 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_10_12]
  · change LocalSlider.cornerGap a b z 9 11 7 false false = 0
    have he : LocalSlider.cornerGap a b z 9 11 7 false false = LocalSlider.pairGap a b z 9 11 3 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_10_12]
  · change LocalSlider.cornerGap a b z 12 13 0 true false = 0
    have he : LocalSlider.cornerGap a b z 12 13 0 true false = LocalSlider.pairGap a b z 12 13 2 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_13_14]
  · change LocalSlider.cornerGap a b z 12 13 4 true false = 0
    have he : LocalSlider.cornerGap a b z 12 13 4 true false = LocalSlider.pairGap a b z 12 13 2 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_13_14]
  · change LocalSlider.cornerGap a b z 11 13 3 false false = 0
    have he : LocalSlider.cornerGap a b z 11 13 3 false false = LocalSlider.pairGap a b z 11 13 3 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_12_14]
  · change LocalSlider.cornerGap a b z 11 13 7 false false = 0
    have he : LocalSlider.cornerGap a b z 11 13 7 false false = LocalSlider.pairGap a b z 11 13 3 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_12_14]
theorem parallel_plus_arm (r : Fin 16) :
    cornerArm (LocalSlider.contactPairs (parallelCorners r).1).1
      (LocalSlider.contactPairs (parallelCorners r).1).2.1 (parallelCorners r).2.1
      (parallelCorners r).2.2.2.2.1 (parallelCorners r).2.2.2.2.2 = 1/2 := by
  fin_cases r <;> norm_num [parallelCorners,LocalSlider.contactPairs,cornerArm,
    tangentProjection,LocalSlider.optionNormal,LocalSlider.optionOwner,LocalSlider.optionOther,
    LocalSlider.cornerSign,EndpointGeometry.directions] <;> nlinarith [cs_unit]
theorem parallel_plus_tight (a b z : ℝ) (r : Fin 16) :
    LocalSlider.cornerGap a b z (LocalSlider.contactPairs (parallelCorners r).1).1
      (LocalSlider.contactPairs (parallelCorners r).1).2.1 (parallelCorners r).2.1
      (parallelCorners r).2.2.2.2.1 (parallelCorners r).2.2.2.2.2 = 0 := by
  fin_cases r
  · change LocalSlider.cornerGap a b z 0 1 0 true true = 0
    have he : LocalSlider.cornerGap a b z 0 1 0 true true = LocalSlider.pairGap a b z 0 1 0 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_1_2]
  · change LocalSlider.cornerGap a b z 0 1 4 true true = 0
    have he : LocalSlider.cornerGap a b z 0 1 4 true true = LocalSlider.pairGap a b z 0 1 0 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_1_2]
  · change LocalSlider.cornerGap a b z 0 2 2 false true = 0
    have he : LocalSlider.cornerGap a b z 0 2 2 false true = LocalSlider.pairGap a b z 0 2 1 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_1_3]
  · change LocalSlider.cornerGap a b z 0 2 6 false true = 0
    have he : LocalSlider.cornerGap a b z 0 2 6 false true = LocalSlider.pairGap a b z 0 2 1 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_1_3]
  · change LocalSlider.cornerGap a b z 4 6 2 false true = 0
    have he : LocalSlider.cornerGap a b z 4 6 2 false true = LocalSlider.pairGap a b z 4 6 1 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_5_7]
  · change LocalSlider.cornerGap a b z 4 6 6 false true = 0
    have he : LocalSlider.cornerGap a b z 4 6 6 false true = LocalSlider.pairGap a b z 4 6 1 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_5_7]
  · change LocalSlider.cornerGap a b z 8 9 0 true true = 0
    have he : LocalSlider.cornerGap a b z 8 9 0 true true = LocalSlider.pairGap a b z 8 9 2 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_9_10]
  · change LocalSlider.cornerGap a b z 8 9 4 true true = 0
    have he : LocalSlider.cornerGap a b z 8 9 4 true true = LocalSlider.pairGap a b z 8 9 2 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_9_10]
  · change LocalSlider.cornerGap a b z 10 11 0 true true = 0
    have he : LocalSlider.cornerGap a b z 10 11 0 true true = LocalSlider.pairGap a b z 10 11 2 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_11_12]
  · change LocalSlider.cornerGap a b z 10 11 4 true true = 0
    have he : LocalSlider.cornerGap a b z 10 11 4 true true = LocalSlider.pairGap a b z 10 11 2 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_11_12]
  · change LocalSlider.cornerGap a b z 9 11 3 true false = 0
    have he : LocalSlider.cornerGap a b z 9 11 3 true false = LocalSlider.pairGap a b z 9 11 3 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_10_12]
  · change LocalSlider.cornerGap a b z 9 11 7 true false = 0
    have he : LocalSlider.cornerGap a b z 9 11 7 true false = LocalSlider.pairGap a b z 9 11 3 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_10_12]
  · change LocalSlider.cornerGap a b z 12 13 0 true true = 0
    have he : LocalSlider.cornerGap a b z 12 13 0 true true = LocalSlider.pairGap a b z 12 13 2 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_13_14]
  · change LocalSlider.cornerGap a b z 12 13 4 true true = 0
    have he : LocalSlider.cornerGap a b z 12 13 4 true true = LocalSlider.pairGap a b z 12 13 2 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_13_14]
  · change LocalSlider.cornerGap a b z 11 13 3 true false = 0
    have he : LocalSlider.cornerGap a b z 11 13 3 true false = LocalSlider.pairGap a b z 11 13 3 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_12_14]
  · change LocalSlider.cornerGap a b z 11 13 7 true false = 0
    have he : LocalSlider.cornerGap a b z 11 13 7 true false = LocalSlider.pairGap a b z 11 13 3 := by
      norm_num [LocalSlider.cornerGap,LocalSlider.pairGap,LocalSlider.optionNormal,
        LocalSlider.optionOwner,LocalSlider.optionOther,LocalSlider.cornerSign,
        axes,EndpointGeometry.directions,directionKind,axisKind,supportTable]
      <;> nlinarith [cs_unit]
    rw [he,LocalSlider.pair_contact_12_14]
theorem parallelCorners_designated (r : Fin 16) :
    ((parallelCorners r).1,(parallelCorners r).2.1) ∈ LocalSlider.designatedOptions := by
  fin_cases r <;> decide +kernel

theorem parallelCorners_cover : ∀ r : Fin 19, ∀ k : Fin 8,
    r ∈ ([0,1,2,4,7,8,10,11] : List (Fin 19)) → (r,k) ∈ LocalSlider.designatedOptions →
    ∃ w : Fin 16, (parallelCorners w).1=r ∧ (parallelCorners w).2.1=k := by decide +kernel

theorem parallelCorners_offset {a b z : ℝ} (hbox : LocalSlider.sliderBox a b z) (r : Fin 16) :
    |LocalSlider.tangentialOffset a b z (LocalSlider.contactPairs (parallelCorners r).1).1
      (LocalSlider.contactPairs (parallelCorners r).1).2.1
      (LocalSlider.contactPairs (parallelCorners r).1).2.2| ≤ 1 := by
  fin_cases r
  · have hh := LocalSlider.face_offsets_bounded hbox 0
    exact hh.trans (by norm_num)
  · have hh := LocalSlider.face_offsets_bounded hbox 0
    exact hh.trans (by norm_num)
  · have hh := LocalSlider.face_offsets_bounded hbox 1
    exact hh.trans (by norm_num)
  · have hh := LocalSlider.face_offsets_bounded hbox 1
    exact hh.trans (by norm_num)
  · have hh := LocalSlider.face_offsets_bounded hbox 2
    exact hh.trans (by norm_num)
  · have hh := LocalSlider.face_offsets_bounded hbox 2
    exact hh.trans (by norm_num)
  · have hh := LocalSlider.face_offsets_bounded hbox 3
    exact hh.trans (by norm_num)
  · have hh := LocalSlider.face_offsets_bounded hbox 3
    exact hh.trans (by norm_num)
  · have hh := LocalSlider.face_offsets_bounded hbox 4
    exact hh.trans (by norm_num)
  · have hh := LocalSlider.face_offsets_bounded hbox 4
    exact hh.trans (by norm_num)
  · have hh := LocalSlider.face_offsets_bounded hbox 5
    exact hh.trans (by norm_num)
  · have hh := LocalSlider.face_offsets_bounded hbox 5
    exact hh.trans (by norm_num)
  · have hh := LocalSlider.face_offsets_bounded hbox 6
    exact hh.trans (by norm_num)
  · have hh := LocalSlider.face_offsets_bounded hbox 6
    exact hh.trans (by norm_num)
  · have hh := LocalSlider.face_offsets_bounded hbox 7
    exact hh.trans (by norm_num)
  · have hh := LocalSlider.face_offsets_bounded hbox 7
    exact hh.trans (by norm_num)
theorem parallel_contact_lower {a b z q : ℝ} {h : Fin 45 → ℝ}
    (hbox : LocalSlider.sliderBox a b z) (hq0 : 0 ≤ q) (hq : q ≤ 1/2)
    (hh : ∀ k, |h k| ≤ q) (r : Fin 19) (k : Fin 8)
    (hr : r ∈ ([0,1,2,4,7,8,10,11] : List (Fin 19)))
    (hk : (r,k) ∈ LocalSlider.designatedOptions)
    (hgap : supportGap a b z h (LocalSlider.contactPairs r).1 (LocalSlider.contactPairs r).2.1 k) :
    -(100*q^2/2) ≤ parallelRow a b z h (LocalSlider.contactPairs r).1
      (LocalSlider.contactPairs r).2.1 (LocalSlider.contactPairs r).2.2 true ∧
    -(100*q^2/2) ≤ parallelRow a b z h (LocalSlider.contactPairs r).1
      (LocalSlider.contactPairs r).2.1 (LocalSlider.contactPairs r).2.2 false := by
  obtain ⟨w,hrw,hkw⟩ := parallelCorners_cover r k hr hk
  subst r; subst k
  exact parallelRow_lower hbox hq0 hq hh _ _ _ _ _ _ _ _
    (LocalSlider.designatedOptions_normal _ (parallelCorners_designated w))
    (parallel_minus_arm w) (parallel_plus_arm w)
    (parallel_minus_tight a b z w) (parallel_plus_tight a b z w)
    (parallelCorners_offset hbox w) hgap

def pairRowIndex (r : Fin 27) : Fin 52 := ⟨25+r.val,by omega⟩

theorem last27_rows_lower {a b z q : ℝ} {h : Fin 45 → ℝ}
    (hbox : LocalSlider.sliderBox a b z) (hq0 : 0 ≤ q) (hq : q ≤ 1/2)
    (hh : ∀ k, |h k| ≤ q)
    (hselected : ∀ r : Fin 19, ∃ k : Fin 8, (r,k) ∈ LocalSlider.designatedOptions ∧
      supportGap a b z h (LocalSlider.contactPairs r).1 (LocalSlider.contactPairs r).2.1 k)
    (l : Fin 27) : -(100*q^2/2) ≤ geometricRows a b z h (pairRowIndex l) := by
  fin_cases l
  · change -(100*q^2/2) ≤ parallelRow a b z h 0 1 0 true
    obtain ⟨k,hk,hgap⟩ := hselected 0
    exact (parallel_contact_lower hbox hq0 hq hh 0 k (by decide +kernel) hk hgap).1
  · change -(100*q^2/2) ≤ parallelRow a b z h 0 1 0 false
    obtain ⟨k,hk,hgap⟩ := hselected 0
    exact (parallel_contact_lower hbox hq0 hq hh 0 k (by decide +kernel) hk hgap).2
  · change -(100*q^2/2) ≤ parallelRow a b z h 0 2 1 true
    obtain ⟨k,hk,hgap⟩ := hselected 1
    exact (parallel_contact_lower hbox hq0 hq hh 1 k (by decide +kernel) hk hgap).1
  · change -(100*q^2/2) ≤ parallelRow a b z h 0 2 1 false
    obtain ⟨k,hk,hgap⟩ := hselected 1
    exact (parallel_contact_lower hbox hq0 hq hh 1 k (by decide +kernel) hk hgap).2
  · change -(100*q^2/2) ≤ parallelRow a b z h 4 6 1 true
    obtain ⟨k,hk,hgap⟩ := hselected 2
    exact (parallel_contact_lower hbox hq0 hq hh 2 k (by decide +kernel) hk hgap).1
  · change -(100*q^2/2) ≤ parallelRow a b z h 4 6 1 false
    obtain ⟨k,hk,hgap⟩ := hselected 2
    exact (parallel_contact_lower hbox hq0 hq hh 2 k (by decide +kernel) hk hgap).2
  · change -(100*q^2/2) ≤ cornerRow a b z h 2 8 2 true true
    obtain ⟨k,hk,hgap⟩ := hselected 3
    have he : k = 2 := by simpa [LocalSlider.designatedOptions] using hk
    subst k
    exact cornerRow_lower hbox hq0 hq hh 2 8 2 true true
      (LocalSlider.designated_corner_3 a b z) hgap
  · change -(100*q^2/2) ≤ parallelRow a b z h 8 9 2 true
    obtain ⟨k,hk,hgap⟩ := hselected 4
    exact (parallel_contact_lower hbox hq0 hq hh 4 k (by decide +kernel) hk hgap).1
  · change -(100*q^2/2) ≤ parallelRow a b z h 8 9 2 false
    obtain ⟨k,hk,hgap⟩ := hselected 4
    exact (parallel_contact_lower hbox hq0 hq hh 4 k (by decide +kernel) hk hgap).2
  · change -(100*q^2/2) ≤ cornerRow a b z h 3 9 7 true false
    obtain ⟨k,hk,hgap⟩ := hselected 5
    have he : k = 7 := by simpa [LocalSlider.designatedOptions] using hk
    subst k
    exact cornerRow_lower hbox hq0 hq hh 3 9 7 true false
      (LocalSlider.designated_corner_5 a b z) hgap
  · change -(100*q^2/2) ≤ cornerRow a b z h 2 10 4 true true
    obtain ⟨k,hk,hgap⟩ := hselected 6
    have he : k = 4 := by simpa [LocalSlider.designatedOptions] using hk
    subst k
    exact cornerRow_lower hbox hq0 hq hh 2 10 4 true true
      (LocalSlider.designated_corner_6 a b z) hgap
  · change -(100*q^2/2) ≤ parallelRow a b z h 10 11 2 true
    obtain ⟨k,hk,hgap⟩ := hselected 7
    exact (parallel_contact_lower hbox hq0 hq hh 7 k (by decide +kernel) hk hgap).1
  · change -(100*q^2/2) ≤ parallelRow a b z h 10 11 2 false
    obtain ⟨k,hk,hgap⟩ := hselected 7
    exact (parallel_contact_lower hbox hq0 hq hh 7 k (by decide +kernel) hk hgap).2
  · change -(100*q^2/2) ≤ parallelRow a b z h 9 11 3 true
    obtain ⟨k,hk,hgap⟩ := hselected 8
    exact (parallel_contact_lower hbox hq0 hq hh 8 k (by decide +kernel) hk hgap).1
  · change -(100*q^2/2) ≤ parallelRow a b z h 9 11 3 false
    obtain ⟨k,hk,hgap⟩ := hselected 8
    exact (parallel_contact_lower hbox hq0 hq hh 8 k (by decide +kernel) hk hgap).2
  · change -(100*q^2/2) ≤ cornerRow a b z h 1 12 4 true true
    obtain ⟨k,hk,hgap⟩ := hselected 9
    have he : k = 4 := by simpa [LocalSlider.designatedOptions] using hk
    subst k
    exact cornerRow_lower hbox hq0 hq hh 1 12 4 true true
      (LocalSlider.designated_corner_9 a b z) hgap
  · change -(100*q^2/2) ≤ parallelRow a b z h 12 13 2 true
    obtain ⟨k,hk,hgap⟩ := hselected 10
    exact (parallel_contact_lower hbox hq0 hq hh 10 k (by decide +kernel) hk hgap).1
  · change -(100*q^2/2) ≤ parallelRow a b z h 12 13 2 false
    obtain ⟨k,hk,hgap⟩ := hselected 10
    exact (parallel_contact_lower hbox hq0 hq hh 10 k (by decide +kernel) hk hgap).2
  · change -(100*q^2/2) ≤ parallelRow a b z h 11 13 3 true
    obtain ⟨k,hk,hgap⟩ := hselected 11
    exact (parallel_contact_lower hbox hq0 hq hh 11 k (by decide +kernel) hk hgap).1
  · change -(100*q^2/2) ≤ parallelRow a b z h 11 13 3 false
    obtain ⟨k,hk,hgap⟩ := hselected 11
    exact (parallel_contact_lower hbox hq0 hq hh 11 k (by decide +kernel) hk hgap).2
  · change -(100*q^2/2) ≤ cornerRow a b z h 9 14 0 true true
    obtain ⟨k,hk,hgap⟩ := hselected 12
    have he : k = 0 := by simpa [LocalSlider.designatedOptions] using hk
    subst k
    exact cornerRow_lower hbox hq0 hq hh 9 14 0 true true
      (LocalSlider.designated_corner_12 a b z) hgap
  · change -(100*q^2/2) ≤ cornerRow a b z h 13 16 0 true true
    obtain ⟨k,hk,hgap⟩ := hselected 13
    have he : k = 0 := by simpa [LocalSlider.designatedOptions] using hk
    subst k
    exact cornerRow_lower hbox hq0 hq hh 13 16 0 true true
      (LocalSlider.designated_corner_13 a b z) hgap
  · change -(100*q^2/2) ≤ cornerRow a b z h 14 15 4 true false
    obtain ⟨k,hk,hgap⟩ := hselected 14
    have he : k = 4 := by simpa [LocalSlider.designatedOptions] using hk
    subst k
    exact cornerRow_lower hbox hq0 hq hh 14 15 4 true false
      (LocalSlider.designated_corner_14 a b z) hgap
  · change -(100*q^2/2) ≤ cornerRow a b z h 15 7 2 true true
    obtain ⟨k,hk,hgap⟩ := hselected 15
    have he : k = 2 := by simpa [LocalSlider.designatedOptions] using hk
    subst k
    exact cornerRow_lower hbox hq0 hq hh 15 7 2 true true
      (LocalSlider.designated_corner_15 a b z) hgap
  · change -(100*q^2/2) ≤ cornerRow a b z h 13 6 3 true false
    obtain ⟨k,hk,hgap⟩ := hselected 16
    have he : k = 3 := by simpa [LocalSlider.designatedOptions] using hk
    subst k
    exact cornerRow_lower hbox hq0 hq hh 13 6 3 true false
      (LocalSlider.designated_corner_16 a b z) hgap
  · change -(100*q^2/2) ≤ cornerRow a b z h 15 16 0 true false
    obtain ⟨k,hk,hgap⟩ := hselected 17
    have he : k = 0 := by simpa [LocalSlider.designatedOptions] using hk
    subst k
    exact cornerRow_lower hbox hq0 hq hh 15 16 0 true false
      (LocalSlider.designated_corner_17 a b z) hgap
  · change -(100*q^2/2) ≤ cornerRow a b z h 11 15 0 true true
    obtain ⟨k,hk,hgap⟩ := hselected 18
    have he : k = 0 := by simpa [LocalSlider.designatedOptions] using hk
    subst k
    exact cornerRow_lower hbox hq0 hq hh 11 15 0 true true
      (LocalSlider.designated_corner_18 a b z) hgap
end Sq17.LocalPerturbation
#print axioms Sq17.LocalPerturbation.last27_rows_lower
