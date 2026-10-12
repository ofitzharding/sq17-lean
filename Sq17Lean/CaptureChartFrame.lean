import Sq17Lean.CenteredOrbitFrame
import Sq17Lean.EndpointGeometry

/-! Exact inverse quarter turn from the capture trace frame to the local
endpoint chart. A quarter turn preserves the represented square orientation
modulo its own quarter-turn symmetry, so no angle-lift assumption is needed. -/
namespace Sq17.CaptureChart
open Sq17.EndpointGeometry
noncomputable section

def chartShift (sigma : ℝ) : ℝ := CenteredOrbitFrame.delta side-sigma
def turn (sigma : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.2-chartShift sigma,side-p.1+chartShift sigma)

def turnHomeomorph (sigma : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun := turn sigma
  invFun p := (side-p.2+chartShift sigma,p.1+chartShift sigma)
  left_inv p := by ext <;> simp [turn] <;> ring
  right_inv p := by ext <;> simp [turn] <;> ring
  continuous_toFun := by unfold turn; fun_prop
  continuous_invFun := by fun_prop

theorem turn_mem_square (sigma : ℝ) (P u p : ℝ × ℝ) :
    turn sigma p ∈ Sq17.sq (turn sigma P).1 (turn sigma P).2 u.1 u.2 ↔
      p ∈ Sq17.sq P.1 P.2 u.1 u.2 := by
  have hx : ((turn sigma p).1-(turn sigma P).1)*u.1+
      ((turn sigma p).2-(turn sigma P).2)*u.2 =
      (p.2-P.2)*u.1-(p.1-P.1)*u.2 := by dsimp [turn]; ring
  have hy : ((turn sigma p).2-(turn sigma P).2)*u.1-
      ((turn sigma p).1-(turn sigma P).1)*u.2 =
      -((p.1-P.1)*u.1+(p.2-P.2)*u.2) := by dsimp [turn]; ring
  simp only [Sq17.sq,Set.mem_setOf_eq,hx,hy,abs_neg,and_comm]

theorem turn_square_image (sigma : ℝ) (P u : ℝ × ℝ) :
    turn sigma '' Sq17.sq P.1 P.2 u.1 u.2 =
      Sq17.sq (turn sigma P).1 (turn sigma P).2 u.1 u.2 := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact (turn_mem_square sigma P u q).2 hq
  · intro hp
    obtain ⟨q,rfl⟩ := (turnHomeomorph sigma).surjective p
    exact ⟨q,(turn_mem_square sigma P u q).1 hp,rfl⟩

theorem turn_square_disjoint (sigma : ℝ) (P Q u v : ℝ × ℝ)
    (hd : Disjoint (interior (Sq17.sq P.1 P.2 u.1 u.2))
      (interior (Sq17.sq Q.1 Q.2 v.1 v.2))) :
    Disjoint (interior (Sq17.sq (turn sigma P).1 (turn sigma P).2 u.1 u.2))
      (interior (Sq17.sq (turn sigma Q).1 (turn sigma Q).2 v.1 v.2)) := by
  rw [← turn_square_image,← turn_square_image]
  change Disjoint (interior ((turnHomeomorph sigma) '' _))
    (interior ((turnHomeomorph sigma) '' _))
  rw [← (turnHomeomorph sigma).image_interior,← (turnHomeomorph sigma).image_interior]
  apply Set.disjoint_left.mpr
  rintro p ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
  have hxy : y = x := (turnHomeomorph sigma).injective he
  exact Set.disjoint_left.mp hd hx (hxy ▸ hy)

def chartBox (L : ℝ) : Set (ℝ × ℝ) :=
  {p | (side-L)/2 ≤ p.1 ∧ p.1 ≤ (side+L)/2 ∧
    (side-L)/2 ≤ p.2 ∧ p.2 ≤ (side+L)/2}

theorem turn_mem_chartBox (L sigma : ℝ) (p : ℝ × ℝ) :
    turn sigma p ∈ chartBox L ↔ p ∈ CenteredOrbitFrame.traceBox L sigma := by
  dsimp [turn,chartBox,CenteredOrbitFrame.traceBox,chartShift,CenteredOrbitFrame.delta]
  constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;>
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem chartBox_subset_endpoint {L : ℝ} (hL : L ≤ side) :
    chartBox L ⊆ {p | 0 ≤ p.1 ∧ p.1 ≤ side ∧ 0 ≤ p.2 ∧ p.2 ≤ side} := by
  rintro p ⟨h1,h2,h3,h4⟩
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem turn_square_fit (L sigma : ℝ) (P u : ℝ × ℝ)
    (hf : Sq17.sq P.1 P.2 u.1 u.2 ⊆ CenteredOrbitFrame.traceBox L sigma) :
    Sq17.sq (turn sigma P).1 (turn sigma P).2 u.1 u.2 ⊆ chartBox L := by
  rw [← turn_square_image]
  rintro _ ⟨p,hp,rfl⟩
  exact (turn_mem_chartBox L sigma p).2 (hf hp)

#print axioms turn_square_disjoint
#print axioms turn_square_fit
end
end Sq17.CaptureChart
