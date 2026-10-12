import Sq17Lean.WallSquareSymmetry

/-! Exact frames used by the connected trace root. The target side remains L:
first translate [0,L]² to its centered location inside the 1169/250 cover frame,
apply D4 there, and then subtract the trace header's sigma. -/
namespace Sq17.CenteredOrbitFrame
open Sq17.Propagation

def shift (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1+t,p.2+t)

noncomputable def delta (L : ℝ) : ℝ := (1169/250-L)/2

def centeredBox (L : ℝ) : Set (ℝ × ℝ) :=
  {p | delta L ≤ p.1 ∧ p.1 ≤ delta L+L ∧ delta L ≤ p.2 ∧ p.2 ≤ delta L+L}

def traceBox (L sigma : ℝ) : Set (ℝ × ℝ) :=
  {p | delta L-sigma ≤ p.1 ∧ p.1 ≤ delta L-sigma+L ∧
    delta L-sigma ≤ p.2 ∧ p.2 ≤ delta L-sigma+L}

noncomputable def shiftHomeomorph (t : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun := shift t
  invFun := shift (-t)
  left_inv p := by ext <;> simp [shift]
  right_inv p := by ext <;> simp [shift]
  continuous_toFun := by unfold shift; fun_prop
  continuous_invFun := by unfold shift; fun_prop

theorem shift_mem_square (t : ℝ) (p u z : ℝ × ℝ) :
    shift t z ∈ Sq17.sq (shift t p).1 (shift t p).2 u.1 u.2 ↔
      z ∈ Sq17.sq p.1 p.2 u.1 u.2 := by
  simp [shift,Sq17.sq]

theorem shift_square_image (t : ℝ) (p u : ℝ × ℝ) :
    shift t '' Sq17.sq p.1 p.2 u.1 u.2 =
      Sq17.sq (shift t p).1 (shift t p).2 u.1 u.2 := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (shift_mem_square t p u x).2 hx
  · intro hz
    obtain ⟨x,rfl⟩ := (shiftHomeomorph t).surjective z
    exact ⟨x,(shift_mem_square t p u x).1 hz,rfl⟩

theorem shift_square_disjoint (t : ℝ) (p q u v : ℝ × ℝ)
    (hd : Disjoint (interior (Sq17.sq p.1 p.2 u.1 u.2))
      (interior (Sq17.sq q.1 q.2 v.1 v.2))) :
    Disjoint (interior (Sq17.sq (shift t p).1 (shift t p).2 u.1 u.2))
      (interior (Sq17.sq (shift t q).1 (shift t q).2 v.1 v.2)) := by
  rw [← shift_square_image,← shift_square_image]
  change Disjoint (interior ((shiftHomeomorph t) '' _))
    (interior ((shiftHomeomorph t) '' _))
  rw [← (shiftHomeomorph t).image_interior,← (shiftHomeomorph t).image_interior]
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
  have hxy : y = x := (shiftHomeomorph t).injective he
  exact Set.disjoint_left.mp hd hx (hxy ▸ hy)

theorem shift_mem_centered (L : ℝ) (z : ℝ × ℝ) :
    shift (delta L) z ∈ centeredBox L ↔ z ∈ containerBox L := by
  simp only [shift,centeredBox,containerBox,Set.mem_ofPred_eq]
  constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;>
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem square_fit_centered (L : ℝ) (p u : ℝ × ℝ)
    (hf : Sq17.sq p.1 p.2 u.1 u.2 ⊆ containerBox L) :
    Sq17.sq (shift (delta L) p).1 (shift (delta L) p).2 u.1 u.2 ⊆ centeredBox L := by
  rw [← shift_square_image]
  rintro _ ⟨z,hz,rfl⟩
  exact (shift_mem_centered L z).2 (hf hz)

theorem centered_subset_cover (L : ℝ) (hL : L ≤ 1169/250) :
    centeredBox L ⊆ containerBox (1169/250) := by
  intro z hz
  rcases hz with ⟨h1,h2,h3,h4⟩
  change 0 ≤ z.1 ∧ z.1 ≤ 1169/250 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1169/250
  dsimp [delta] at h1 h2 h3 h4
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

/-- Every actual D4 symmetry preserves the centered target box of side L,
not merely the larger rational cover box. -/
theorem action_mem_centered (g : Fin 8) (L : ℝ) (z : ℝ × ℝ)
    (hz : z ∈ centeredBox L) : CellSymmetry.action g z ∈ centeredBox L := by
  fin_cases g <;> simp only [CellSymmetry.action,centeredBox,delta,Set.mem_ofPred_eq] at * <;>
    rcases hz with ⟨h1,h2,h3,h4⟩ <;>
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem action_square_fit_centered (g : Fin 8) (L : ℝ) (p u : ℝ × ℝ)
    (hf : Sq17.sq p.1 p.2 u.1 u.2 ⊆ centeredBox L) :
    Sq17.sq (CellSymmetry.action g p).1 (CellSymmetry.action g p).2
      (CellSymmetry.direction g u).1 (CellSymmetry.direction g u).2 ⊆ centeredBox L := by
  rw [← CellSymmetry.action_square_image]
  rintro _ ⟨z,hz,rfl⟩
  exact action_mem_centered g L z (hf hz)

theorem shift_mem_trace (L sigma : ℝ) (z : ℝ × ℝ) :
    shift (-sigma) z ∈ traceBox L sigma ↔ z ∈ centeredBox L := by
  simp only [shift,traceBox,centeredBox,Set.mem_ofPred_eq]
  constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;>
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem square_fit_trace (L sigma : ℝ) (p u : ℝ × ℝ)
    (hf : Sq17.sq p.1 p.2 u.1 u.2 ⊆ centeredBox L) :
    Sq17.sq (shift (-sigma) p).1 (shift (-sigma) p).2 u.1 u.2 ⊆ traceBox L sigma := by
  rw [← shift_square_image]
  rintro _ ⟨z,hz,rfl⟩
  exact (shift_mem_trace L sigma z).2 (hf hz)

/-- These are exactly the two target-containment comparisons of FULL2 roots.
The checker additionally asks d≥0 and 0<L≤1169/250 for its other obligations. -/
theorem trace_subset_header (L sigma Sx d : ℝ)
    (hlo : -d ≤ delta L-sigma) (hhi : delta L-sigma+L ≤ Sx+d) :
    traceBox L sigma ⊆ {z | -d ≤ z.1 ∧ z.1 ≤ Sx+d ∧ -d ≤ z.2 ∧ z.2 ≤ Sx+d} := by
  rintro z ⟨h1,h2,h3,h4⟩
  exact ⟨hlo.trans h1,h2.trans hhi,hlo.trans h3,h4.trans hhi⟩

theorem shift_mem_trace_cell (sigma : ℝ) (i : Fin 24) (p : ℝ × ℝ)
    (hp : p ∈ ExactCells.cell i) :
    shift (-sigma) p ∈ shift (-sigma) '' ExactCells.cell i := ⟨p,hp,rfl⟩

end Sq17.CenteredOrbitFrame

#print axioms Sq17.CenteredOrbitFrame.shift_square_disjoint
#print axioms Sq17.CenteredOrbitFrame.square_fit_centered
#print axioms Sq17.CenteredOrbitFrame.action_square_fit_centered
#print axioms Sq17.CenteredOrbitFrame.square_fit_trace
#print axioms Sq17.CenteredOrbitFrame.trace_subset_header
