import Sq17Lean.PropagationState

/-! A finite executable checker for sequences of certified pair cuts.
Initialization, wall steps and splitting require their own checked rules. -/
namespace Sq17.Propagation

theorem polygonRow_empty (r : CoreRowCertificate) :
    (PolygonRow.ofCertificate [] r).region = ∅ := by
  ext p
  simp [PolygonRow.region, PolygonRow.ofCertificate]

theorem stateDomains_erase_empty {Owner : Type*} [DecidableEq Owner]
    (S : Owner → List PolygonRow) (i : Owner) (preRows suffix : List PolygonRow)
    (r : CoreRowCertificate) :
    stateDomains (Function.update S i
      (preRows ++ PolygonRow.ofCertificate [] r :: suffix)) =
    stateDomains (Function.update S i (preRows ++ suffix)) := by
  funext k
  by_cases hk : k = i
  · subst k
    simp only [stateDomains, Function.update_self, rowsRegion_replace,
      polygonRow_empty, Set.union_empty]
  · simp only [stateDomains, Function.update_of_ne hk]

structure PolygonStep (Owner : Type*) where
  owner : Owner
  partner : Owner
  preRows : List PolygonRow
  suffix : List PolygonRow
  before : List (ℚ × ℚ)
  after : List (ℚ × ℚ)
  removed : List (ℚ × ℚ)
  kept : List (ℚ × ℚ)
  row : CoreRowCertificate
  partners : List PolygonPartnerCertificate
  degree : ℕ
  a : ℚ
  b : ℚ
  q : ℚ
  keepWitness : (ℚ × ℚ) → HullTriangleWitness

def PolygonStep.check {Owner : Type*} [DecidableEq Owner]
    (step : PolygonStep Owner) (S : Owner → List PolygonRow) : Bool :=
  decide (step.owner ≠ step.partner ∧ S step.owner =
    step.preRows ++ PolygonRow.ofCertificate step.before step.row :: step.suffix) &&
  livePartnerCheck (S step.partner) step.partners &&
  polygonReplaceCheck step.before step.after step.removed step.kept step.row
    step.partners step.degree step.a step.b step.q step.keepWitness

def PolygonStep.apply {Owner : Type*} [DecidableEq Owner]
    (step : PolygonStep Owner) (S : Owner → List PolygonRow) : Owner → List PolygonRow :=
  if step.after = [] then Function.update S step.owner (step.preRows ++ step.suffix)
  else Function.update S step.owner
    (step.preRows ++ PolygonRow.ofCertificate step.after step.row :: step.suffix)

def DisjointPacking {Owner : Type*} (p : Owner → AnglePose) : Prop :=
  ∀ i j, i ≠ j → Disjoint (interior (p i).square) (interior (p j).square)

theorem PolygonStep.check_sound {Owner : Type*} [DecidableEq Owner]
    (step : PolygonStep Owner) (S : Owner → List PolygonRow) (p : Owner → AnglePose)
    (hc : step.check S = true) (hrep : Represents (stateDomains S) p)
    (hpacking : DisjointPacking p) :
    Represents (stateDomains (step.apply S)) p := by
  simp only [PolygonStep.check, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨⟨hne,hsource⟩,hpartners⟩,hreplace⟩
  have h := polygonStateReplace_prune S p step.owner step.partner step.preRows step.suffix
    step.before step.after step.removed step.kept step.row step.partners step.degree
    step.a step.b step.q step.keepWitness hreplace hsource hpartners hrep
    (hpacking step.owner step.partner hne)
  by_cases he : step.after = []
  · simpa only [PolygonStep.apply, he, ite_true, stateDomains_erase_empty] using h
  · simpa only [PolygonStep.apply, ite_eq_right he] using h

def polygonTraceCheck {Owner : Type*} [DecidableEq Owner]
    (S : Owner → List PolygonRow) : List (PolygonStep Owner) → Bool
  | [] => true
  | step :: steps => step.check S && polygonTraceCheck (step.apply S) steps

def polygonTraceRun {Owner : Type*} [DecidableEq Owner]
    (S : Owner → List PolygonRow) : List (PolygonStep Owner) → Owner → List PolygonRow
  | [] => S
  | step :: steps => polygonTraceRun (step.apply S) steps

theorem polygonTraceCheck_sound {Owner : Type*} [DecidableEq Owner]
    (steps : List (PolygonStep Owner)) (S : Owner → List PolygonRow) (p : Owner → AnglePose)
    (hc : polygonTraceCheck S steps = true) (hrep : Represents (stateDomains S) p)
    (hpacking : DisjointPacking p) :
    Represents (stateDomains (polygonTraceRun S steps)) p := by
  induction steps generalizing S with
  | nil => exact hrep
  | cons step steps ih =>
    have hh := Bool.and_eq_true_iff.mp hc
    exact ih (step.apply S) hh.2 (step.check_sound S p hh.1 hrep hpacking)

/-- An accepted sequence ending with an empty owner excludes every represented
packing. This is conditional on the explicitly supplied initial state. -/
theorem polygonTraceCheck_excludes {Owner : Type*} [DecidableEq Owner]
    (steps : List (PolygonStep Owner)) (S : Owner → List PolygonRow)
    (hc : polygonTraceCheck S steps = true) (i : Owner)
    (hempty : polygonTraceRun S steps i = []) :
    ¬ ∃ p, Represents (stateDomains S) p ∧ DisjointPacking p := by
  rintro ⟨p,hrep,hpacking⟩
  have hfinal := polygonTraceCheck_sound steps S p hc hrep hpacking i
  rcases hfinal with ⟨r,hr,_⟩
  simpa [hempty] using hr

end Sq17.Propagation

#print axioms Sq17.Propagation.PolygonStep.check_sound
#print axioms Sq17.Propagation.polygonTraceCheck_sound
#print axioms Sq17.Propagation.polygonTraceCheck_excludes
