import Sq17Lean.PropagationGeometry
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Exact support and ordinary convex separation for the actual unit-square
sets. The separation conclusion permits legal boundary contact. -/
namespace Sq17.WallCapacity

noncomputable def squareSupport (ux uy a b : ℝ) : ℝ :=
  (|a*ux+b*uy|+|b*ux-a*uy|)/2

theorem square_convex (cx cy ux uy : ℝ) : Convex ℝ (Sq17.sq cx cy ux uy) := by
  intro x hx y hy a b ha hb hab
  have combine (X Y : ℝ) (hX : |X| ≤ 1/2) (hY : |Y| ≤ 1/2) :
      |a*X+b*Y| ≤ 1/2 := by
    have h := add_le_add (mul_le_mul_of_nonneg_left hX ha)
      (mul_le_mul_of_nonneg_left hY hb)
    have ht := abs_add_le (a*X) (b*Y)
    rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] at ht
    nlinarith
  change |((a • x+b • y).1-cx)*ux+((a • x+b • y).2-cy)*uy| ≤ 1/2 ∧
    |((a • x+b • y).2-cy)*ux-((a • x+b • y).1-cx)*uy| ≤ 1/2
  have he₁ : ((a • x+b • y).1-cx)*ux+((a • x+b • y).2-cy)*uy =
      a*((x.1-cx)*ux+(x.2-cy)*uy)+b*((y.1-cx)*ux+(y.2-cy)*uy) := by
    have hc : b = 1-a := by linarith
    subst b; simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  have he₂ : ((a • x+b • y).2-cy)*ux-((a • x+b • y).1-cx)*uy =
      a*((x.2-cy)*ux-(x.1-cx)*uy)+b*((y.2-cy)*ux-(y.1-cx)*uy) := by
    have hc : b = 1-a := by linarith
    subst b; simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  rw [he₁, he₂]
  exact ⟨combine _ _ hx.1 hy.1, combine _ _ hx.2 hy.2⟩

theorem square_closed (cx cy ux uy : ℝ) : IsClosed (Sq17.sq cx cy ux uy) := by
  change IsClosed ({p : ℝ × ℝ | |(p.1-cx)*ux+(p.2-cy)*uy| ≤ 1/2} ∩
    {p : ℝ × ℝ | |(p.2-cy)*ux-(p.1-cx)*uy| ≤ 1/2})
  exact (isClosed_le (by fun_prop) (by fun_prop)).inter
    (isClosed_le (by fun_prop) (by fun_prop))

theorem square_center_mem_interior (cx cy ux uy : ℝ) :
    (cx,cy) ∈ interior (Sq17.sq cx cy ux uy) := by
  let O : Set (ℝ × ℝ) := {p | |(p.1-cx)*ux+(p.2-cy)*uy| < 1/2 ∧
    |(p.2-cy)*ux-(p.1-cx)*uy| < 1/2}
  have ho : IsOpen O := by
    change IsOpen ({p : ℝ × ℝ | |(p.1-cx)*ux+(p.2-cy)*uy| < 1/2} ∩
      {p : ℝ × ℝ | |(p.2-cy)*ux-(p.1-cx)*uy| < 1/2})
    exact (isOpen_lt (by fun_prop) (by fun_prop)).inter
      (isOpen_lt (by fun_prop) (by fun_prop))
  have hsub : O ⊆ Sq17.sq cx cy ux uy := fun _ h => ⟨h.1.le,h.2.le⟩
  apply ho.subset_interior_iff.mpr hsub
  norm_num [O]

theorem square_closure_interior (cx cy ux uy : ℝ) :
    closure (interior (Sq17.sq cx cy ux uy)) = Sq17.sq cx cy ux uy := by
  rw [(square_convex cx cy ux uy).closure_interior_eq_closure_of_nonempty_interior
    ⟨(cx,cy), square_center_mem_interior cx cy ux uy⟩,
    (square_closed cx cy ux uy).closure_eq]

private theorem sign_mul (x : ℝ) : (if 0 ≤ x then 1 else -1)*x = |x| := by
  split <;> rename_i h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

theorem squareSupport_attained (cx cy ux uy a b : ℝ) (hu : ux^2+uy^2=1) :
    ∃ p ∈ Sq17.sq cx cy ux uy, a*p.1+b*p.2 = a*cx+b*cy+squareSupport ux uy a b := by
  let D := a*ux+b*uy
  let E := b*ux-a*uy
  let A : ℝ := if 0 ≤ D then 1 else -1
  let B : ℝ := if 0 ≤ E then 1 else -1
  have hA : |A| ≤ 1 := by dsimp [A]; split <;> norm_num
  have hB : |B| ≤ 1 := by dsimp [B]; split <;> norm_num
  have hsupport : 1*(|ux*ux+uy*uy|+|ux*uy-uy*ux|) ≤ 1 := by
    have he : ux*ux+uy*uy = 1 := by nlinarith [hu]
    rw [he, mul_comm uy ux, sub_self]; norm_num
  refine ⟨Sq17.Propagation.corePoint cx cy ux uy 1 A B,
    Sq17.Propagation.corePoint_mem_sq cx cy ux uy 1 A B ux uy
      (by norm_num) hA hB hsupport, ?_⟩
  have hAD : A*D = |D| := sign_mul D
  have hBE : B*E = |E| := sign_mul E
  change a*(cx+1/2*(A*ux-B*uy))+b*(cy+1/2*(A*uy+B*ux)) = _
  change A*(a*ux+b*uy) = |a*ux+b*uy| at hAD
  change B*(b*ux-a*uy) = |b*ux-a*uy| at hBE
  dsimp [squareSupport]
  nlinarith only [hAD,hBE]

theorem squareSupport_neg (ux uy a b : ℝ) :
    squareSupport ux uy (-a) (-b) = squareSupport ux uy a b := by
  unfold squareSupport
  have he₁ : (-a)*ux+(-b)*uy = -(a*ux+b*uy) := by ring
  have he₂ : (-b)*ux-(-a)*uy = -(b*ux-a*uy) := by ring
  rw [he₁, he₂, abs_neg, abs_neg]

theorem squareSupport_upper (cx cy ux uy a b : ℝ) (hu : ux^2+uy^2=1)
    (z : ℝ × ℝ) (hz : z ∈ Sq17.sq cx cy ux uy) :
    a*z.1+b*z.2 ≤ a*cx+b*cy+squareSupport ux uy a b := by
  have bound (d x : ℝ) (hx : |x| ≤ 1/2) : d*x ≤ |d|/2 := by
    have h := mul_le_mul_of_nonneg_left hx (abs_nonneg d)
    have hd := le_abs_self (d*x)
    rw [abs_mul] at hd
    linarith
  have h₁ := bound (a*ux+b*uy) ((z.1-cx)*ux+(z.2-cy)*uy) hz.1
  have h₂ := bound (b*ux-a*uy) ((z.2-cy)*ux-(z.1-cx)*uy) hz.2
  have he : a*(z.1-cx)+b*(z.2-cy) =
      (a*ux+b*uy)*((z.1-cx)*ux+(z.2-cy)*uy)+
      (b*ux-a*uy)*((z.2-cy)*ux-(z.1-cx)*uy) := by
    calc
      _ = (a*(z.1-cx)+b*(z.2-cy))*(ux^2+uy^2) := by rw [hu]; ring
      _ = _ := by ring
  dsimp [squareSupport]
  linarith only [h₁,h₂,he]

theorem squareSupport_ge_half (ux uy a b : ℝ)
    (hu : ux^2+uy^2=1) (hm : a^2+b^2=1) : 1/2 ≤ squareSupport ux uy a b := by
  have he : (a*ux+b*uy)^2+(b*ux-a*uy)^2 = 1 := by
    calc
      _ = (a^2+b^2)*(ux^2+uy^2) := by ring
      _ = 1 := by rw [hu,hm]; norm_num
  have ha := abs_nonneg (a*ux+b*uy)
  have hb := abs_nonneg (b*ux-a*uy)
  have hp := mul_nonneg ha hb
  have ha2 := sq_abs (a*ux+b*uy)
  have hb2 := sq_abs (b*ux-a*uy)
  dsimp [squareSupport]
  nlinarith

theorem squareSupport_wall_bound (cx cy ux uy : ℝ) (hu : ux^2+uy^2=1)
    (hfit : Sq17.sq cx cy ux uy ⊆ {p | 0 ≤ p.2}) :
    squareSupport ux uy 0 1 ≤ cy := by
  obtain ⟨z,hz,he⟩ := squareSupport_attained cx cy ux uy 0 (-1) hu
  have hs : squareSupport ux uy 0 (-1) = squareSupport ux uy 0 1 := by
    simpa using squareSupport_neg ux uy 0 1
  rw [hs] at he
  have hz0 := hfit hz
  change 0 ≤ z.2 at hz0
  norm_num at he
  linarith

theorem squareSupport_div (ux uy a b r : ℝ) (hr : 0 < r) :
    squareSupport ux uy (a/r) (b/r) = squareSupport ux uy a b / r := by
  unfold squareSupport
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ←add_div,
    div_mul_eq_mul_div, div_mul_eq_mul_div, ←sub_div,
    abs_div, abs_div, abs_of_pos hr]
  ring

private theorem functional_coords (f : (ℝ × ℝ) →L[ℝ] ℝ) (p : ℝ × ℝ) :
    f p = p.1*f (1,0)+p.2*f (0,1) := by
  have he : p = p.1 • (1,0)+p.2 • (0,1) := by ext <;> simp
  conv_lhs => rw [he, map_add, map_smul, map_smul]
  rfl

/-- Weak separation of closed unit squares follows from disjoint interiors,
so touching configurations remain covered. The normal has Euclidean length one. -/
theorem square_disjoint_unit_separator (p q : ℝ × ℝ) (ux uy vx vy : ℝ)
    (hu : ux^2+uy^2=1) (hv : vx^2+vy^2=1)
    (hdis : Disjoint (interior (Sq17.sq p.1 p.2 ux uy))
      (interior (Sq17.sq q.1 q.2 vx vy))) :
    ∃ a b : ℝ, a^2+b^2=1 ∧
      squareSupport ux uy a b+squareSupport vx vy a b ≤ a*(q.1-p.1)+b*(q.2-p.2) := by
  have hd : Disjoint (interior (Sq17.sq p.1 p.2 ux uy)) (Sq17.sq q.1 q.2 vx vy) := by
    simpa only [square_closure_interior] using hdis.closure_right isOpen_interior
  obtain ⟨f, t, hf, hleft, hright⟩ := geometric_hahn_banach_of_nonempty_interior
    (square_convex p.1 p.2 ux uy) (square_convex q.1 q.2 vx vy) hd
    ⟨p, square_center_mem_interior p.1 p.2 ux uy⟩
    ⟨q, interior_subset (square_center_mem_interior q.1 q.2 vx vy)⟩
  let a := f (1,0)
  let b := f (0,1)
  have hn : 0 < a^2+b^2 := by
    by_contra h
    have ha : a = 0 := by nlinarith [sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a]
    apply hf
    apply ContinuousLinearMap.ext
    intro z
    rw [functional_coords]
    change z.1*a+z.2*b = 0
    rw [ha,hb]; ring
  obtain ⟨x,hx,heqx⟩ := squareSupport_attained p.1 p.2 ux uy a b hu
  obtain ⟨y,hy,heqy⟩ := squareSupport_attained q.1 q.2 vx vy (-a) (-b) hv
  rw [squareSupport_neg] at heqy
  have hx' := hleft x hx
  have hy' := hright y hy
  rw [functional_coords] at hx' hy'
  change x.1*a+x.2*b ≤ t at hx'
  change t ≤ y.1*a+y.2*b at hy'
  have hsep : squareSupport ux uy a b+squareSupport vx vy a b ≤
      a*(q.1-p.1)+b*(q.2-p.2) := by nlinarith only [heqx,heqy,hx',hy']
  let r := Real.sqrt (a^2+b^2)
  have hr : 0 < r := Real.sqrt_pos.2 hn
  have hr2 : r^2 = a^2+b^2 := Real.sq_sqrt hn.le
  refine ⟨a/r,b/r,?_,?_⟩
  · field_simp [ne_of_gt hr]
    nlinarith only [hr2]
  · rw [squareSupport_div _ _ _ _ _ hr, squareSupport_div _ _ _ _ _ hr]
    have h := div_le_div_of_nonneg_right hsep hr.le
    convert h using 1 <;> ring

end Sq17.WallCapacity

#print axioms Sq17.WallCapacity.squareSupport_attained
#print axioms Sq17.WallCapacity.squareSupport_upper
#print axioms Sq17.WallCapacity.squareSupport_ge_half
#print axioms Sq17.WallCapacity.squareSupport_wall_bound
#print axioms Sq17.WallCapacity.square_disjoint_unit_separator
