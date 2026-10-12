import Sq17Lean.SquareSeparationAxes

/-! Actual disjoint unit squares satisfy one of the four unoriented
edge-normal separation inequalities. Boundary contact is permitted. -/
namespace Sq17.WallCapacity

private theorem frame_dot (ux uy a b vx vy : ℝ) :
    (ux*vx+uy*vy)*(a*ux+b*uy)+(ux*vy-uy*vx)*(b*ux-a*uy) =
      (ux^2+uy^2)*(a*vx+b*vy) := by ring

private theorem frame_cross (ux uy a b vx vy : ℝ) :
    (ux*vx+uy*vy)*(b*ux-a*uy)-(ux*vy-uy*vx)*(a*ux+b*uy) =
      (ux^2+uy^2)*(b*vx-a*vy) := by ring

/-- The complete finite-axis necessity theorem, for the same real square
sets as the packing problem. No axis-selection premise is assumed. -/
theorem square_disjoint_axis (p q : ℝ × ℝ) (ux uy vx vy : ℝ)
    (hu : ux^2+uy^2=1) (hv : vx^2+vy^2=1)
    (hdis : Disjoint (interior (Sq17.sq p.1 p.2 ux uy))
      (interior (Sq17.sq q.1 q.2 vx vy))) :
    let H := (1+|ux*vx+uy*vy|+|ux*vy-uy*vx|)/2
    H ≤ |ux*(q.1-p.1)+uy*(q.2-p.2)| ∨
    H ≤ |ux*(q.2-p.2)-uy*(q.1-p.1)| ∨
    H ≤ |vx*(q.1-p.1)+vy*(q.2-p.2)| ∨
    H ≤ |vx*(q.2-p.2)-vy*(q.1-p.1)| := by
  obtain ⟨a,b,hab,hgap⟩ := square_disjoint_unit_separator p q ux uy vx vy hu hv hdis
  let c := ux*vx+uy*vy
  let s := ux*vy-uy*vx
  let x := a*ux+b*uy
  let y := b*ux-a*uy
  let dx := ux*(q.1-p.1)+uy*(q.2-p.2)
  let dy := ux*(q.2-p.2)-uy*(q.1-p.1)
  have hcs : c^2+s^2=1 := by
    calc
      _ = (ux^2+uy^2)*(vx^2+vy^2) := by dsimp [c,s]; ring
      _ = 1 := by rw [hu,hv]; norm_num
  have hxy : x^2+y^2=1 := by
    calc
      _ = (ux^2+uy^2)*(a^2+b^2) := by dsimp [x,y]; ring
      _ = 1 := by rw [hu,hab]; norm_num
  have hxypos : 0 < |x|+|y| := by
    by_contra hn
    have hx0 : x=0 := abs_eq_zero.mp (by linarith [abs_nonneg x,abs_nonneg y])
    have hy0 : y=0 := abs_eq_zero.mp (by linarith [abs_nonneg x,abs_nonneg y])
    simp [hx0,hy0] at hxy
  have hp1 : c*x+s*y = a*vx+b*vy := by
    dsimp [c,s,x,y]
    rw [frame_dot,hu,one_mul]
  have hp2 : c*y-s*x = b*vx-a*vy := by
    dsimp [c,s,x,y]
    rw [frame_cross,hu,one_mul]
  have hd : x*dx+y*dy = a*(q.1-p.1)+b*(q.2-p.2) := by
    calc
      _ = (ux^2+uy^2)*(a*(q.1-p.1)+b*(q.2-p.2)) := by dsimp [x,y,dx,dy]; ring
      _ = _ := by rw [hu,one_mul]
  have hgap' : (|x|+|y|)/2+squareSupport c s x y ≤ x*dx+y*dy := by
    rw [hd]
    have he : squareSupport c s x y = squareSupport vx vy a b := by
      dsimp [squareSupport]
      rw [mul_comm x c,mul_comm y s,mul_comm y c,mul_comm x s,hp1,hp2]
    rw [he]
    exact hgap
  have ha := support_implies_axis c s x y dx dy hcs hxypos hgap'
  have hd1 : c*dx+s*dy = vx*(q.1-p.1)+vy*(q.2-p.2) := by
    calc
      _ = (ux^2+uy^2)*(vx*(q.1-p.1)+vy*(q.2-p.2)) := by dsimp [c,s,dx,dy]; ring
      _ = _ := by rw [hu,one_mul]
  have hd2 : c*dy-s*dx = vx*(q.2-p.2)-vy*(q.1-p.1) := by
    calc
      _ = (ux^2+uy^2)*(vx*(q.2-p.2)-vy*(q.1-p.1)) := by dsimp [c,s,dx,dy]; ring
      _ = _ := by rw [hu,one_mul]
  dsimp [AxisSeparated] at ha
  rw [hd1,hd2] at ha
  exact ha

#print axioms square_disjoint_axis
end Sq17.WallCapacity
