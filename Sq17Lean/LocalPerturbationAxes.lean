import Sq17Lean.LocalPerturbationCoordinates
import Sq17Lean.LocalSliderDistances
import Sq17Lean.LocalSliderUnwanted
import Sq17Lean.SquareSeparationFinite
import Sq17Lean.LocalRigidityCornerFeasibility
import Sq17Lean.LocalRigidityGapStability

/-! Actual moving square axes and rejection of the 125 unwanted options. -/
namespace Sq17.LocalPerturbation
open Sq17.EndpointGeometry Sq17.WallCapacity Sq17.LocalRigidity
noncomputable section

def optionPhase : Fin 8 → ℝ := ![0,Real.pi,Real.pi/2,-Real.pi/2,
  0,Real.pi,Real.pi/2,-Real.pi/2]

def vectorNormal (v : Fin 17 → ℝ × ℝ) (i j : Fin 17) (k : Fin 8) : ℝ × ℝ :=
  let u := v (LocalSlider.optionOwner i j k)
  ![u,-u,(-u.2,u.1),(u.2,-u.1),u,-u,(-u.2,u.1),(u.2,-u.1)] k

theorem angle_vectorNormal (θ : Fin 17 → ℝ) (i j : Fin 17) (k : Fin 8) :
    (Real.cos (θ (LocalSlider.optionOwner i j k)+optionPhase k),
      Real.sin (θ (LocalSlider.optionOwner i j k)+optionPhase k)) =
    vectorNormal (fun l => (Real.cos (θ l),Real.sin (θ l))) i j k := by
  fin_cases k <;> ext <;>
    simp [vectorNormal,optionPhase,LocalSlider.optionOwner,Real.cos_add,Real.sin_add,neg_div]

def optionAngle (i j : Fin 17) (k : Fin 8) : ℝ :=
  baseAngle (LocalSlider.optionOwner i j k)+optionPhase k

def optionNormal (h : Fin 45 → ℝ) (i j : Fin 17) (k : Fin 8) : ℝ × ℝ :=
  vectorNormal (directions h) i j k

theorem optionAngle_base (i j : Fin 17) (k : Fin 8) :
    (Real.cos (optionAngle i j k),Real.sin (optionAngle i j k)) =
      LocalSlider.optionNormal i j k := by
  unfold optionAngle
  rw [angle_vectorNormal]
  simp only [baseAngle_direction]
  rfl

theorem optionAngle_moved (h : Fin 45 → ℝ) (i j : Fin 17) (k : Fin 8) :
    (Real.cos (optionAngle i j k+angular h (LocalSlider.optionOwner i j k)),
      Real.sin (optionAngle i j k+angular h (LocalSlider.optionOwner i j k))) =
      optionNormal h i j k := by
  have he : optionAngle i j k+angular h (LocalSlider.optionOwner i j k) =
      (baseAngle (LocalSlider.optionOwner i j k)+angular h (LocalSlider.optionOwner i j k))+
        optionPhase k := by unfold optionAngle; ring
  rw [he]
  exact angle_vectorNormal (fun l => baseAngle l+angular h l) i j k

def supportGap (a b z : ℝ) (h : Fin 45 → ℝ) (i j : Fin 17) (k : Fin 8) : Prop :=
  let n := optionNormal h i j k
  squareSupport (directions h i).1 (directions h i).2 n.1 n.2+
    squareSupport (directions h j).1 (directions h j).2 n.1 n.2 ≤
    n.1*((centres a b z h j).1-(centres a b z h i).1)+
    n.2*((centres a b z h j).2-(centres a b z h i).2)

theorem disjoint_has_option (a b z : ℝ) (h : Fin 45 → ℝ) (i j : Fin 17)
    (hd : Disjoint
      (interior (Sq17.sq (centres a b z h i).1 (centres a b z h i).2
        (directions h i).1 (directions h i).2))
      (interior (Sq17.sq (centres a b z h j).1 (centres a b z h j).2
        (directions h j).1 (directions h j).2))) :
    ∃ k : Fin 8, supportGap a b z h i j k := by
  obtain ⟨k,σ,hσ,hg⟩ := square_disjoint_finite_axis (centres a b z h i)
    (centres a b z h j) (directions h i).1 (directions h i).2
    (directions h j).1 (directions h j).2 (directions_unit h i) (directions_unit h j) hd
  rcases hσ with rfl|rfl
  · fin_cases k
    · exact ⟨0,by simpa [supportGap,optionNormal,vectorNormal,LocalSlider.optionOwner,edgeNormal] using hg⟩
    · exact ⟨2,by simpa [supportGap,optionNormal,vectorNormal,LocalSlider.optionOwner,edgeNormal] using hg⟩
    · exact ⟨4,by simpa [supportGap,optionNormal,vectorNormal,LocalSlider.optionOwner,edgeNormal] using hg⟩
    · exact ⟨6,by simpa [supportGap,optionNormal,vectorNormal,LocalSlider.optionOwner,edgeNormal] using hg⟩
  · fin_cases k
    · exact ⟨1,by simpa [supportGap,optionNormal,vectorNormal,LocalSlider.optionOwner,edgeNormal] using hg⟩
    · exact ⟨3,by simpa [supportGap,optionNormal,vectorNormal,LocalSlider.optionOwner,edgeNormal] using hg⟩
    · exact ⟨5,by simpa [supportGap,optionNormal,vectorNormal,LocalSlider.optionOwner,edgeNormal] using hg⟩
    · exact ⟨7,by simpa [supportGap,optionNormal,vectorNormal,LocalSlider.optionOwner,edgeNormal] using hg⟩

def movingCornerGap (a b z : ℝ) (h : Fin 45 → ℝ)
    (i j : Fin 17) (k : Fin 8) (se sf : Bool) : ℝ → ℝ :=
  rotatingCornerGap (optionAngle i j k) (angular h (LocalSlider.optionOwner i j k))
    ((LocalSlider.centres a b z j).1-(LocalSlider.centres a b z i).1)
    ((LocalSlider.centres a b z j).2-(LocalSlider.centres a b z i).2)
    ((translation h j).1-(translation h i).1) ((translation h j).2-(translation h i).2)
    (baseAngle (LocalSlider.optionOther i j k)) (angular h (LocalSlider.optionOther i j k))
    (LocalSlider.cornerSign se) (LocalSlider.cornerSign sf)

theorem movingCornerGap_zero (a b z : ℝ) (h : Fin 45 → ℝ)
    (i j : Fin 17) (k : Fin 8) (se sf : Bool) :
    movingCornerGap a b z h i j k se sf 0 = LocalSlider.cornerGap a b z i j k se sf := by
  have hn := optionAngle_base i j k
  have hv := baseAngle_direction (LocalSlider.optionOther i j k)
  have hn1 := congrArg Prod.fst hn
  have hn2 := congrArg Prod.snd hn
  have hv1 := congrArg Prod.fst hv
  have hv2 := congrArg Prod.snd hv
  simp only [Prod.fst,Prod.snd] at hn1 hn2 hv1 hv2
  simp only [movingCornerGap,rotatingCornerGap,zero_mul,add_zero,hn1,hn2,hv1,hv2,
    LocalSlider.cornerGap]

theorem movingCornerGap_one (a b z : ℝ) (h : Fin 45 → ℝ)
    (i j : Fin 17) (k : Fin 8) (se sf : Bool) :
    movingCornerGap a b z h i j k se sf 1 =
      let n := optionNormal h i j k
      let v := directions h (LocalSlider.optionOther i j k)
      n.1*((centres a b z h j).1-(centres a b z h i).1-
          (LocalSlider.cornerSign se*v.1-LocalSlider.cornerSign sf*v.2))+
        n.2*((centres a b z h j).2-(centres a b z h i).2-
          (LocalSlider.cornerSign se*v.2+LocalSlider.cornerSign sf*v.1))-1/2 := by
  have hn := optionAngle_moved h i j k
  have hn1 := congrArg Prod.fst hn
  have hn2 := congrArg Prod.snd hn
  simp only [Prod.fst,Prod.snd] at hn1 hn2
  simp only [movingCornerGap,rotatingCornerGap,one_mul,hn1,hn2,directions,
    centres,Prod.fst_add,Prod.snd_add]
  ring

theorem supportGap_corner_nonnegative (a b z : ℝ) (h : Fin 45 → ℝ)
    (i j : Fin 17) (k : Fin 8) (se sf : Bool) (hg : supportGap a b z h i j k) :
    0 ≤ movingCornerGap a b z h i j k se sf 1 := by
  let owner := LocalSlider.optionOwner i j k
  let other := LocalSlider.optionOther i j k
  let n := optionNormal h i j k
  have hn : n.1^2+n.2^2=1 := by
    dsimp only [n]
    rw [← optionAngle_moved h i j k]
    exact Real.cos_sq_add_sin_sq _
  have hswap : squareSupport (directions h owner).1 (directions h owner).2 n.1 n.2+
      squareSupport (directions h other).1 (directions h other).2 n.1 n.2 ≤
      n.1*((centres a b z h j).1-(centres a b z h i).1)+
      n.2*((centres a b z h j).2-(centres a b z h i).2) := by
    dsimp [owner,other,LocalSlider.optionOwner,LocalSlider.optionOther]
    split_ifs <;> simpa only [supportGap,add_comm] using hg
  rw [movingCornerGap_one]
  exact support_gap_corner_feasible _ _ _ _ _ _ _ _ _ _ (directions_unit h owner) hn
    (LocalSlider.cornerSign_bounds se) (LocalSlider.cornerSign_bounds sf) hswap

theorem unwanted_stays_negative {a b z : ℝ} (hb : LocalSlider.sliderBox a b z)
    (h : Fin 45 → ℝ) (hh : ∀ j, |h j| ≤ (1:ℝ)/10000000)
    (w : Fin 19 × Fin 8 × Bool × Bool) (hw : w ∈ LocalSlider.unwantedOptions) :
    movingCornerGap a b z h (LocalSlider.contactPairs w.1).1
      (LocalSlider.contactPairs w.1).2.1 w.2.1 w.2.2.1 w.2.2.2 1 < 0 := by
  let i := (LocalSlider.contactPairs w.1).1
  let j := (LocalSlider.contactPairs w.1).2.1
  have hdist := LocalSlider.pair_distances_le_ten hb i j
  have htrans := translation_difference_bounds h (1/10000000) (by norm_num) hh i j
  apply rotatingCornerGap_stays_negative _ _ _ _ _ _ _ _ _ _ (1/10000000) (1/100)
      (by norm_num) (by norm_num)
      (angular_bounds h _ (by norm_num) hh _) (angular_bounds h _ (by norm_num) hh _)
      hdist.1 hdist.2 htrans.1 htrans.2
      (LocalSlider.cornerSign_bounds _) (LocalSlider.cornerSign_bounds _)
  · change movingCornerGap a b z h i j w.2.1 w.2.2.1 w.2.2.2 0 ≤ _
    rw [movingCornerGap_zero]
    exact LocalSlider.unwantedOptions_negative hb w hw
  · norm_num

/-- Every actually feasible directed separator belongs to the finite
retained list, derived from the checked margins and actual square motions. -/
theorem supportGap_designated {a b z : ℝ} (hb : LocalSlider.sliderBox a b z)
    (h : Fin 45 → ℝ) (hh : ∀ j, |h j| ≤ (1:ℝ)/10000000)
    (r : Fin 19) (k : Fin 8)
    (hg : supportGap a b z h (LocalSlider.contactPairs r).1
      (LocalSlider.contactPairs r).2.1 k) : (r,k) ∈ LocalSlider.designatedOptions := by
  rcases LocalSlider.options_exhaustive r k with good|⟨w,hw,hr,hk⟩
  · exact good
  · have hneg := unwanted_stays_negative hb h hh w hw
    rw [hr,hk] at hneg
    have hpos := supportGap_corner_nonnegative a b z h _ _ k w.2.2.1 w.2.2.2 hg
    exact False.elim (not_lt_of_ge hpos hneg)

#print axioms disjoint_has_option
#print axioms supportGap_designated

theorem disjoint_has_designated {a b z : ℝ} (hb : LocalSlider.sliderBox a b z)
    (h : Fin 45 → ℝ) (hh : ∀ j, |h j| ≤ (1:ℝ)/10000000) (r : Fin 19)
    (hd : Disjoint
      (interior (Sq17.sq (centres a b z h (LocalSlider.contactPairs r).1).1
        (centres a b z h (LocalSlider.contactPairs r).1).2
        (directions h (LocalSlider.contactPairs r).1).1
        (directions h (LocalSlider.contactPairs r).1).2))
      (interior (Sq17.sq (centres a b z h (LocalSlider.contactPairs r).2.1).1
        (centres a b z h (LocalSlider.contactPairs r).2.1).2
        (directions h (LocalSlider.contactPairs r).2.1).1
        (directions h (LocalSlider.contactPairs r).2.1).2))) :
    ∃ k : Fin 8, (r,k) ∈ LocalSlider.designatedOptions ∧
      supportGap a b z h (LocalSlider.contactPairs r).1 (LocalSlider.contactPairs r).2.1 k := by
  obtain ⟨k,hk⟩ := disjoint_has_option a b z h _ _ hd
  exact ⟨k,supportGap_designated hb h hh r k hk,hk⟩

#print axioms disjoint_has_designated
end
end Sq17.LocalPerturbation
