import Sq17Lean.EndpointStrictGaps
import Sq17Lean.SquareSupportSeparation

/-! The exact algebraic endpoint is attained by seventeen actual unit squares.
Touching contacts are handled by interior disjointness, not strict gaps. -/
namespace Sq17.EndpointGeometry
open Sq17.WallCapacity

theorem squares_contained (i : Fin 17) :
    squares i ⊆ {z | 0 ≤ z.1 ∧ z.1 ≤ side ∧ 0 ≤ z.2 ∧ z.2 ≤ side} := by
  apply support_walls_contained (centres i) (directions i).1 (directions i).2 side (directions_unit i)
  · have h := all_wall_gaps i 0
    have hs := square_support_table i 0
    change squareSupport (directions i).1 (directions i).2 1 0 = supportTable (directionKind i) 0 at hs
    rw [hs]
    change 0 ≤ (centres i).1-supportTable (directionKind i) 0 at h
    linarith
  · have h := all_wall_gaps i 1
    have hs := square_support_table i 0
    change squareSupport (directions i).1 (directions i).2 1 0 = supportTable (directionKind i) 0 at hs
    rw [hs]
    change 0 ≤ side-(centres i).1-supportTable (directionKind i) 0 at h
    linarith
  · have h := all_wall_gaps i 2
    have hs := square_support_table i 1
    change squareSupport (directions i).1 (directions i).2 0 1 = supportTable (directionKind i) 0 at hs
    rw [hs]
    change 0 ≤ (centres i).2-supportTable (directionKind i) 0 at h
    linarith
  · have h := all_wall_gaps i 3
    have hs := square_support_table i 1
    change squareSupport (directions i).1 (directions i).2 0 1 = supportTable (directionKind i) 0 at hs
    rw [hs]
    change 0 ≤ side-(centres i).2-supportTable (directionKind i) 0 at h
    linarith

theorem pairGap_disjoint (i j : Fin 17) (k : Fin 6) (hg : 0 ≤ pairGap i j k) :
    Disjoint (interior (squares i)) (interior (squares j)) := by
  apply support_gap_disjoint (centres i) (centres j)
    (directions i).1 (directions i).2 (directions j).1 (directions j).2
    (axes k).1 (axes k).2 (directions_unit i) (directions_unit j) (axes_unit k)
  rw [square_support_table,square_support_table]
  unfold pairGap at hg
  linarith

theorem squares_disjoint (i j : Fin 17) (hij : i ≠ j) :
    Disjoint (interior (squares i)) (interior (squares j)) := by
  have hordered (i j : Fin 17) (hlt : i < j) :
      Disjoint (interior (squares i)) (interior (squares j)) := by
    obtain ⟨z,hz,hmatch⟩ := pairRoster_covers i j hlt
    have hd := pairGap_disjoint z.1 z.2.1 z.2.2 (pairRoster_sound z hz)
    rcases hmatch with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simpa only [ha,hb] using hd
    · simpa only [ha,hb] using hd.symm
  rcases lt_or_gt_of_ne hij with h | h
  · exact hordered i j h
  · exact (hordered j i h).symm

/-- Exact endpoint upper packing, with no numerical or geometric assumptions. -/
theorem endpoint_packing : ∃ S : Fin 17 → Set (ℝ × ℝ),
    (∀ i, Sq17.IsUnitSquare (S i)) ∧
    (∀ i, ∀ z ∈ S i, 0 ≤ z.1 ∧ z.1 ≤ side ∧ 0 ≤ z.2 ∧ z.2 ≤ side) ∧
    (∀ i j, i ≠ j → Disjoint (interior (S i)) (interior (S j))) :=
  ⟨squares,squares_unit,squares_contained,squares_disjoint⟩

end Sq17.EndpointGeometry
#print axioms Sq17.EndpointGeometry.endpoint_packing
