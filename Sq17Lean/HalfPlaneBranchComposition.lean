import Sq17Lean.HalfPlaneStateSound

/-! Composition only: no concrete branch ledger is certified here. Children may
use different angle tables. A checkpoint is bound by semantic containment,
including its angle intervals and cached boxes, rather than by file identity. -/
namespace Sq17.Propagation.HalfPlaneState.BranchComposition

def Excluded (T : Array Entry) (S : HState) (side padding : ℚ) : Prop :=
  ∀ p, Rep T S p → Packing S.length p → Fits S.length side padding p → False

theorem excluded_of_check (T : Array Entry) (S : HState) (side padding : ℚ)
    (steps : List Step) (hT : TableValid T 44)
    (hcheck : excludes T side padding S.length S steps = true) :
    Excluded T S side padding := by
  intro p hr hp hf
  exact excludes_sound T hT side padding S.length S steps le_rfl hcheck ⟨p, hr, hp, hf⟩

theorem excluded_of_run (T : Array Entry) (S E : HState) (side padding : ℚ)
    (steps : List Step) (hT : TableValid T 44)
    (hrun : runAll T side padding S steps = some E)
    (hend : Excluded T E side padding) : Excluded T S side padding := by
  intro p hr hp hf
  obtain ⟨he, hlen⟩ := runAll_sound T hT side padding steps S E p hrun hr hp hf
  exact hend p he (by simpa only [hlen] using hp) (by simpa only [hlen] using hf)

/-- For the selected owner, include its restricted parent domain in the child.
For every other owner, include the entire parent domain. A child can enlarge
domains and change row order, row count, table indices, or core approximations. -/
def CheckpointCover (T U : Array Entry) (parent child : HState)
    (owner : ℕ) (guard : AnglePose → Prop) : Prop :=
  ∀ i, i < parent.length → ∀ q,
    q ∈ rowsRegion T (rowsOf parent i) → (i = owner → guard q) →
      q ∈ rowsRegion U (rowsOf child i)

theorem checkpoint_rep (T U : Array Entry) (parent child : HState)
    (owner : ℕ) (guard : AnglePose → Prop)
    (hlen : child.length = parent.length)
    (hcover : CheckpointCover T U parent child owner guard)
    (p : ℕ → AnglePose) (hrep : Rep T parent p) (hg : guard (p owner)) :
    Rep U child p := by
  intro i hi
  have hip : i < parent.length := by simpa only [hlen] using hi
  apply hcover i hip (p i) (hrep i hip)
  intro heq
  simpa only [heq] using hg

/-- The same theorem handles x, y and angle splits by taking `coordinate` to be
`fun p => p.center.1`, `fun p => p.center.2`, or `AnglePose.angle`.
Both children include the splitting boundary. No gap tolerance is permitted. -/
theorem excluded_of_split (T Tl Tr : Array Entry) (parent left right : HState)
    (side padding : ℚ) (owner : ℕ) (coordinate : AnglePose → ℝ) (mid : ℝ)
    (hlength : left.length = parent.length)
    (hrlength : right.length = parent.length)
    (hleft : CheckpointCover T Tl parent left owner (fun q => coordinate q ≤ mid))
    (hright : CheckpointCover T Tr parent right owner (fun q => mid ≤ coordinate q))
    (el : Excluded Tl left side padding) (er : Excluded Tr right side padding) :
    Excluded T parent side padding := by
  intro p hr hp hf
  rcases le_total (coordinate (p owner)) mid with hl | hh
  · exact el p (checkpoint_rep T Tl parent left owner _ hlength hleft p hr hl)
      (by simpa only [hlength] using hp) (by simpa only [hlength] using hf)
  · exact er p (checkpoint_rep T Tr parent right owner _ hrlength hright p hr hh)
      (by simpa only [hrlength] using hp) (by simpa only [hrlength] using hf)

end Sq17.Propagation.HalfPlaneState.BranchComposition

#print axioms Sq17.Propagation.HalfPlaneState.BranchComposition.excluded_of_check
#print axioms Sq17.Propagation.HalfPlaneState.BranchComposition.excluded_of_run
#print axioms Sq17.Propagation.HalfPlaneState.BranchComposition.excluded_of_split
