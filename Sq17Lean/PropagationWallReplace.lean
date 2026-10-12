import Sq17Lean.PropagationWallBaseline
import Sq17Lean.PropagationStateTrace

/-! Checked wall cuts in the actual translated trace frame. All removed-side
bounds are strict; closed clipping covers boundary contact on the retained side. -/
namespace Sq17.Propagation

def traceContainer (S d : ℝ) : Set (ℝ × ℝ) :=
  {p | -d ≤ p.1 ∧ p.1 ≤ S+d ∧ -d ≤ p.2 ∧ p.2 ≤ S+d}

def rationalFrameWallCheck (V : List (ℚ × ℚ)) (r : WallRowCertificate)
    (S d : ℚ) (n : ℕ) : Bool :=
  r.check n && (rationalHalfPlane V (-1) 0 (-(max 1 r.span/2-d)) ||
    rationalHalfPlane V 1 0 (S+d-max 1 r.span/2) ||
    rationalHalfPlane V 0 (-1) (-(max 1 r.span/2-d)) ||
    rationalHalfPlane V 0 1 (S+d-max 1 r.span/2))

theorem rationalFrameWallCheck_sound (V : List (ℚ × ℚ)) (r : WallRowCertificate)
    (S d : ℚ) (n : ℕ) (hc : rationalFrameWallCheck V r S d n = true)
    (x : ℝ × ℝ) (hx : x ∈ convexHull ℝ (realPoint '' {p | p ∈ V}))
    (θ : ℝ) (hθ : θ ∈ Set.Icc (r.lo : ℝ) (r.hi : ℝ)) :
    ¬ Sq17.sq x.1 x.2 (Real.cos θ) (Real.sin θ) ⊆ traceContainer S d := by
  intro hfit
  have hb := Bool.and_eq_true_iff.mp hc
  have bounds := r.center_bounds_max_translated n hb.1 x.1 x.2 θ S d hθ hfit
  have hw : rationalHalfPlane V (-1) 0 (-(max 1 r.span/2-d)) = true ∨
      rationalHalfPlane V 1 0 (S+d-max 1 r.span/2) = true ∨
      rationalHalfPlane V 0 (-1) (-(max 1 r.span/2-d)) = true ∨
      rationalHalfPlane V 0 1 (S+d-max 1 r.span/2) = true := by
    simpa only [Bool.or_eq_true, or_assoc] using hb.2
  rcases hw with hw | hw | hw | hw
  all_goals
    have hv := rationalHalfPlane_sound _ _ _ _ hw x hx
    push_cast at hv
    norm_num at hv
    linarith

def WallRowCertificate.polygonRow (r : WallRowCertificate)
    (V : List (ℚ × ℚ)) : PolygonRow := ⟨V,r.lo,r.hi⟩

def wallReplaceCheck (before after removed kept : List (ℚ × ℚ))
    (r : WallRowCertificate) (S d : ℚ) (n : ℕ) (a b q : ℚ)
    (keepWitness : (ℚ × ℚ) → HullTriangleWitness) : Bool :=
  rationalClipCheck before removed a b q &&
  rationalClipCheck before kept (-a) (-b) (-q) &&
  kept.all (fun p => triangleHullCheck after p (keepWitness p)) &&
  rationalFrameWallCheck removed r S d n

theorem wallReplace_preserves (before after removed kept : List (ℚ × ℚ))
    (r : WallRowCertificate) (S d : ℚ) (n : ℕ) (a b q : ℚ)
    (keepWitness : (ℚ × ℚ) → HullTriangleWitness)
    (hc : wallReplaceCheck before after removed kept r S d n a b q keepWitness = true)
    (p : AnglePose) (hp : p ∈ (r.polygonRow before).region)
    (hfit : p.square ⊆ traceContainer S d) : p ∈ (r.polygonRow after).region := by
  simp only [wallReplaceCheck, Bool.and_eq_true] at hc
  rcases hc with ⟨⟨⟨hremove,hkeep⟩,htriangle⟩,hwall⟩
  by_cases hcut : (a : ℝ)*p.center.1+(b : ℝ)*p.center.2 < (q : ℝ)
  · have hm := rationalClipCheck_sound before removed a b q hremove p.center hp.1 hcut
    exact False.elim (rationalFrameWallCheck_sound removed r S d n hwall
      p.center hm p.angle hp.2 hfit)
  · have hclosed : ((-a : ℚ) : ℝ)*p.center.1+((-b : ℚ) : ℝ)*p.center.2 ≤
        ((-q : ℚ) : ℝ) := by push_cast; linarith
    have hk := rationalClipCheck_sound_closed before kept (-a) (-b) (-q)
      hkeep p.center hp.1 hclosed
    exact ⟨triangleHullCheck_list_sound kept after keepWitness htriangle hk,hp.2⟩

structure WallStep (Owner : Type*) where
  owner : Owner
  preRows : List PolygonRow
  suffix : List PolygonRow
  before : List (ℚ × ℚ)
  after : List (ℚ × ℚ)
  removed : List (ℚ × ℚ)
  kept : List (ℚ × ℚ)
  row : WallRowCertificate
  degree : ℕ
  a : ℚ
  b : ℚ
  q : ℚ
  keepWitness : (ℚ × ℚ) → HullTriangleWitness

def WallStep.check {Owner : Type*} (step : WallStep Owner)
    (state : Owner → List PolygonRow) (S d : ℚ) : Bool :=
  decide (state step.owner =
    step.preRows ++ step.row.polygonRow step.before :: step.suffix) &&
  wallReplaceCheck step.before step.after step.removed step.kept step.row S d
    step.degree step.a step.b step.q step.keepWitness

def WallStep.apply {Owner : Type*} [DecidableEq Owner]
    (step : WallStep Owner) (state : Owner → List PolygonRow) : Owner → List PolygonRow :=
  Function.update state step.owner (if step.after = [] then step.preRows ++ step.suffix
    else step.preRows ++ step.row.polygonRow step.after :: step.suffix)

theorem WallStep.check_sound {Owner : Type*} [DecidableEq Owner]
    (step : WallStep Owner) (state : Owner → List PolygonRow) (S d : ℚ)
    (p : Owner → AnglePose) (hc : step.check state S d = true)
    (hrep : Represents (stateDomains state) p)
    (hfit : (p step.owner).square ⊆ traceContainer S d) :
    Represents (stateDomains (step.apply state)) p := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hsource := of_decide_eq_true hh.1
  intro i
  by_cases hi : i = step.owner
  · subst i
    have hp := hrep step.owner
    change p step.owner ∈ rowsRegion (state step.owner) at hp
    rw [hsource,rowsRegion_replace] at hp
    change p step.owner ∈ rowsRegion ((step.apply state) step.owner)
    simp only [WallStep.apply,Function.update_self]
    rcases hp with hp | hp
    · split
      · exact hp
      · rw [rowsRegion_replace]; exact Or.inl hp
    · have ha := wallReplace_preserves step.before step.after step.removed step.kept
        step.row S d step.degree step.a step.b step.q step.keepWitness hh.2 _ hp hfit
      split
      · rename_i he
        have hempty : (step.row.polygonRow step.after).region = ∅ := by
          simp [WallRowCertificate.polygonRow,PolygonRow.region,he]
        rw [hempty] at ha
        exact False.elim ha
      · rw [rowsRegion_replace]; exact Or.inr ha
  · simpa only [stateDomains,WallStep.apply,Function.update_of_ne hi] using hrep i

end Sq17.Propagation
#print axioms Sq17.Propagation.rationalFrameWallCheck_sound
#print axioms Sq17.Propagation.wallReplace_preserves
#print axioms Sq17.Propagation.WallStep.check_sound
