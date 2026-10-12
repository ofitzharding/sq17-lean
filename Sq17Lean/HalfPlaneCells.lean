import Sq17Lean.HalfPlaneSeed
import Sq17Lean.CenteredOrbitFrame

/-! Binding the per-case statement to the named cells of the exact cover.

The seed is checked against the exact rational vertices of the named cells,
translated by `-sigma`. The conclusion is then stated for centres in the
translated cells themselves, for a roster `ρ : Fin n → Fin 24`. -/
namespace Sq17.Propagation.HalfPlaneState
open Sq17.Propagation.HalfPlaneInt

def shiftedCell (sigma : ℚ) (k : Fin 24) : List (ℚ × ℚ) :=
  (ExactCells.vertices k).map fun v => (v.1-sigma, v.2-sigma)

def rosterCells (sigma : ℚ) (ρ : List (Fin 24)) : List (List (ℚ × ℚ)) :=
  ρ.map (shiftedCell sigma)

theorem shift_cell_subset (sigma : ℚ) (k : Fin 24) :
    CenteredOrbitFrame.shift (-(sigma:ℝ)) '' ExactCells.cell k ⊆
      convexHull ℝ (realPoint '' {v | v ∈ shiftedCell sigma k}) := by
  rintro _ ⟨p, hp, rfl⟩
  have hp' : p ∈ convexHull ℝ (realPoint '' {v | v ∈ ExactCells.vertices k}) := hp
  have hconv : Convex ℝ {q : ℝ × ℝ | CenteredOrbitFrame.shift (-(sigma:ℝ)) q ∈
      convexHull ℝ (realPoint '' {v | v ∈ shiftedCell sigma k})} := by
    intro x hx y hy a b ha hb hab
    have e : CenteredOrbitFrame.shift (-(sigma:ℝ)) (a • x + b • y) =
        a • CenteredOrbitFrame.shift (-(sigma:ℝ)) x +
          b • CenteredOrbitFrame.shift (-(sigma:ℝ)) y := by
      ext <;>
        simp only [CenteredOrbitFrame.shift, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul] <;>
        linear_combination (sigma:ℝ) * hab
    show CenteredOrbitFrame.shift (-(sigma:ℝ)) (a • x + b • y) ∈
      convexHull ℝ (realPoint '' {v | v ∈ shiftedCell sigma k})
    rw [e]
    exact (convex_convexHull ℝ _) hx hy ha hb hab
  have hsub : convexHull ℝ (realPoint '' {v | v ∈ ExactCells.vertices k}) ⊆
      {q : ℝ × ℝ | CenteredOrbitFrame.shift (-(sigma:ℝ)) q ∈
        convexHull ℝ (realPoint '' {v | v ∈ shiftedCell sigma k})} := by
    apply convexHull_min _ hconv
    rintro _ ⟨v, hv, rfl⟩
    apply subset_convexHull
    refine ⟨(v.1-sigma, v.2-sigma), List.mem_map.mpr ⟨v, hv, rfl⟩, ?_⟩
    ext <;> simp [realPoint, CenteredOrbitFrame.shift] <;> ring
  exact hsub hp'

/-- No `n` unit squares with centres in the translated named cells of the roster,
pairwise disjoint interiors, inside the translated container. -/
theorem roster_excluded (T : Array Entry) (B : Array (TrigBounds × TrigBounds))
    (side shift sigma : ℚ) (n : ℕ) (ρ : Fin n → Fin 24) (S : HState) (steps : List Step)
    (htable : tableOK 44 T B = true)
    (hseed : stateSeedOK T (-initialAngleRadius) initialAngleRadius
      (rosterCells sigma (List.ofFn ρ)) S = true)
    (hlen : S.length = n)
    (hex : excludes T side shift n S steps = true)
    (c u : Fin n → ℝ × ℝ)
    (hunit : ∀ i, (u i).1^2+(u i).2^2 = 1)
    (hcenter : ∀ i, c i ∈ CenteredOrbitFrame.shift (-(sigma:ℝ)) '' ExactCells.cell (ρ i))
    (hd : ∀ i j, i ≠ j → Disjoint
      (interior (Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2))
      (interior (Sq17.sq (c j).1 (c j).2 (u j).1 (u j).2)))
    (hfit : ∀ i, Sq17.sq (c i).1 (c i).2 (u i).1 (u i).2 ⊆ traceContainer side shift) :
    False := by
  obtain ⟨c', hc'⟩ : ∃ c' : ℕ → ℝ × ℝ, ∀ k (h : k < n), c' k = c ⟨k, h⟩ :=
    ⟨fun k => if h : k < n then c ⟨k, h⟩ else (0, 0), fun k h => by simp [h]⟩
  obtain ⟨u', hu'⟩ : ∃ u' : ℕ → ℝ × ℝ, ∀ k (h : k < n), u' k = u ⟨k, h⟩ :=
    ⟨fun k => if h : k < n then u ⟨k, h⟩ else (1, 0), fun k h => by simp [h]⟩
  apply case_excluded T B side shift n (rosterCells sigma (List.ofFn ρ)) S steps htable
    hseed hlen hex c' u'
  · intro i hi
    rw [hu' i hi]
    exact hunit _
  · intro i hi
    rw [hc' i hi]
    have hcell : (rosterCells sigma (List.ofFn ρ)).getD i [] = shiftedCell sigma (ρ ⟨i, hi⟩) := by
      simp [rosterCells, List.getD_eq_getElem?_getD, hi]
    rw [hcell]
    exact shift_cell_subset sigma _ (hcenter _)
  · intro i j hi hj hij
    rw [hc' i hi, hc' j hj, hu' i hi, hu' j hj]
    exact hd _ _ (fun h => hij (by simpa using congrArg Fin.val h))
  · intro i hi
    rw [hc' i hi, hu' i hi]
    exact hfit _

end Sq17.Propagation.HalfPlaneState

#print axioms Sq17.Propagation.HalfPlaneState.roster_excluded
