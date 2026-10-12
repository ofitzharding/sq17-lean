import Sq17Lean.CellSymmetry

namespace Sq17.CellSymmetry
open Sq17.Propagation

def direction (g : Fin 8) (u : ℝ × ℝ) : ℝ × ℝ :=
  match g.val with
  | 0 => u
  | 1 => (-u.1,u.2)
  | 2 => (u.1,-u.2)
  | 3 => (-u.1,-u.2)
  | 4 => (u.2,u.1)
  | 5 => (-u.2,u.1)
  | 6 => (u.2,-u.1)
  | _ => (-u.2,-u.1)

noncomputable def homeomorph (g : Fin 8) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun := action g
  invFun := action (inv g)
  left_inv := action_inverse g
  right_inv p := by simpa only [inverse_inverse] using action_inverse (inv g) p
  continuous_toFun := by
    change Continuous (fun p => action g p)
    fin_cases g <;> simp only [action] <;> fun_prop
  continuous_invFun := by
    change Continuous (fun p => action (inv g) p)
    fin_cases g <;> simp [inv,action] <;> constructor <;> fun_prop

theorem direction_unit (g : Fin 8) (u : ℝ × ℝ) (hu : u.1^2+u.2^2=1) :
    (direction g u).1^2+(direction g u).2^2=1 := by
  fin_cases g <;> simp [direction] <;> nlinarith only [hu]

theorem action_mem_square (g : Fin 8) (p u z : ℝ × ℝ) :
    action g z ∈ Sq17.sq (action g p).1 (action g p).2
      (direction g u).1 (direction g u).2 ↔ z ∈ Sq17.sq p.1 p.2 u.1 u.2 := by
  fin_cases g <;> simp only [action,direction,Sq17.sq,Set.mem_ofPred_eq,abs_le] <;>
    constructor <;> intro h <;> rcases h with ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩ <;>
    constructor <;> constructor <;> nlinarith only [h1,h2,h3,h4]

theorem action_square_image (g : Fin 8) (p u : ℝ × ℝ) :
    action g '' Sq17.sq p.1 p.2 u.1 u.2 =
      Sq17.sq (action g p).1 (action g p).2 (direction g u).1 (direction g u).2 := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (action_mem_square g p u x).2 hx
  · intro hz
    obtain ⟨x,rfl⟩ := (homeomorph g).surjective z
    exact ⟨x,(action_mem_square g p u x).1 hz,rfl⟩

theorem action_square_disjoint (g : Fin 8) (p q u v : ℝ × ℝ)
    (hd : Disjoint (interior (Sq17.sq p.1 p.2 u.1 u.2))
      (interior (Sq17.sq q.1 q.2 v.1 v.2))) :
    Disjoint (interior (Sq17.sq (action g p).1 (action g p).2
      (direction g u).1 (direction g u).2))
      (interior (Sq17.sq (action g q).1 (action g q).2
      (direction g v).1 (direction g v).2)) := by
  rw [← action_square_image,← action_square_image]
  change Disjoint (interior ((homeomorph g) '' _)) (interior ((homeomorph g) '' _))
  rw [← (homeomorph g).image_interior,← (homeomorph g).image_interior]
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
  have hxy : y = x := (homeomorph g).injective he
  exact Set.disjoint_left.mp hd hx (hxy ▸ hy)

theorem action_mem_container (g : Fin 8) (z : ℝ × ℝ)
    (hz : z ∈ containerBox (1169/250)) : action g z ∈ containerBox (1169/250) := by
  fin_cases g <;> simp only [action,containerBox,Set.mem_ofPred_eq] at * <;>
    rcases hz with ⟨h1,h2,h3,h4⟩ <;> exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem action_square_fit (g : Fin 8) (p u : ℝ × ℝ)
    (hfit : Sq17.sq p.1 p.2 u.1 u.2 ⊆ containerBox (1169/250)) :
    Sq17.sq (action g p).1 (action g p).2 (direction g u).1 (direction g u).2 ⊆
      containerBox (1169/250) := by
  rw [← action_square_image]
  rintro _ ⟨z,hz,rfl⟩
  exact action_mem_container g z (hfit hz)

end Sq17.CellSymmetry
#print axioms Sq17.CellSymmetry.action_square_disjoint
#print axioms Sq17.CellSymmetry.action_square_fit
