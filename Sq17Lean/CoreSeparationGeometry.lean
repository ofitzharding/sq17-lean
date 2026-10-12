import Sq17Lean.CoreSeparationAxes

/-! Convex separation for the exact non-normalized, unequal square cores used
by propagation. Coordinates are divided by the first core's squared direction
norm, which is positive; no irrational normalization enters certificates. -/
namespace Sq17.CoreSAT
open Sq17.Propagation Sq17.WallCapacity

def scaledSquare (p : ℝ × ℝ) (c s h : ℝ) : Set (ℝ × ℝ) :=
  Sq17.sq p.1 p.2 (c/(h*(c^2+s^2))) (s/(h*(c^2+s^2)))

theorem scaledSquare_mem (p z : ℝ × ℝ) (c s h : ℝ)
    (hh : 0 < h) (hn : 0 < c^2+s^2) :
    z ∈ scaledSquare p c s h ↔
      |(z.1-p.1)*c+(z.2-p.2)*s| ≤ h*(c^2+s^2)/2 ∧
      |(z.2-p.2)*c-(z.1-p.1)*s| ≤ h*(c^2+s^2)/2 := by
  have hd := mul_pos hh hn
  have h1 : (z.1-p.1)*(c/(h*(c^2+s^2)))+(z.2-p.2)*(s/(h*(c^2+s^2))) =
      ((z.1-p.1)*c+(z.2-p.2)*s)/(h*(c^2+s^2)) := by ring
  have h2 : (z.2-p.2)*(c/(h*(c^2+s^2)))-(z.1-p.1)*(s/(h*(c^2+s^2))) =
      ((z.2-p.2)*c-(z.1-p.1)*s)/(h*(c^2+s^2)) := by ring
  simp only [scaledSquare,Sq17.sq,Set.mem_ofPred_eq,h1,h2,abs_div,abs_of_pos hd,
    div_le_iff₀ hd]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

theorem scaledSquare_subset_core (p : ℝ × ℝ) (c s h : ℝ)
    (hh : 0 < h) (hn : 0 < c^2+s^2) :
    scaledSquare p c s h ⊆ core p.1 p.2 c s h := by
  intro z hz
  obtain ⟨hp,hq⟩ := (scaledSquare_mem p z c s h hh hn).mp hz
  have hd := mul_pos hh hn
  refine ⟨2*((z.1-p.1)*c+(z.2-p.2)*s)/(h*(c^2+s^2)),
    2*((z.2-p.2)*c-(z.1-p.1)*s)/(h*(c^2+s^2)),?_,?_,?_⟩
  · rw [abs_div,abs_mul,abs_of_pos hd]
    norm_num
    apply (div_le_iff₀ hd).mpr
    linarith
  · rw [abs_div,abs_mul,abs_of_pos hd]
    norm_num
    apply (div_le_iff₀ hd).mpr
    linarith
  · apply Prod.ext <;> dsimp [corePoint]
    all_goals field_simp [ne_of_gt hh,ne_of_gt hn]
    all_goals ring

private theorem sign_mul (x : ℝ) : (if 0 ≤ x then 1 else -1)*x = |x| := by
  split <;> rename_i h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

theorem scaledSquare_support_attained (p : ℝ × ℝ) (c s h a b : ℝ)
    (hh : 0 < h) (hn : 0 < c^2+s^2) :
    ∃ z ∈ scaledSquare p c s h,
      a*z.1+b*z.2 = a*p.1+b*p.2+h*squareSupport c s a b := by
  let D := a*c+b*s
  let E := b*c-a*s
  let A : ℝ := if 0 ≤ D then 1 else -1
  let B : ℝ := if 0 ≤ E then 1 else -1
  have hA : |A| ≤ 1 := by dsimp [A];split <;> norm_num
  have hB : |B| ≤ 1 := by dsimp [B];split <;> norm_num
  have hAD : A*D = |D| := sign_mul D
  have hBE : B*E = |E| := sign_mul E
  have hhalf : 0 < h*(c^2+s^2)/2 := by positivity
  have hbnd (t : ℝ) (ht : |t| ≤ 1) : |h*(c^2+s^2)/2*t| ≤ h*(c^2+s^2)/2 := by
    rw [abs_mul,abs_of_pos hhalf]
    nlinarith
  refine ⟨corePoint p.1 p.2 c s h A B,?_,?_⟩
  · apply (scaledSquare_mem _ _ _ _ _ hh hn).mpr
    constructor
    · convert hbnd A hA using 1 <;> dsimp [corePoint] <;> congr 1 <;> ring
    · convert hbnd B hB using 1 <;> dsimp [corePoint] <;> congr 1 <;> ring
  · calc
      _ = a*p.1+b*p.2+h/2*(A*D+B*E) := by dsimp [corePoint,D,E];ring
      _ = _ := by rw [hAD,hBE];dsimp [squareSupport,D,E];ring

private theorem functional_coords (f : (ℝ × ℝ) →L[ℝ] ℝ) (p : ℝ × ℝ) :
    f p = p.1*f (1,0)+p.2*f (0,1) := by
  have he : p = p.1 • (1,0)+p.2 • (0,1) := by ext <;> simp
  conv_lhs => rw [he,map_add,map_smul,map_smul]
  rfl

/-- Disjoint core interiors admit a genuine nonzero support separator. Legal
boundary contact yields weak inequalities and is never declared a collision. -/
theorem core_disjoint_separator (p q : ℝ × ℝ) (c s h e f k : ℝ)
    (hh : 0 < h) (hn : 0 < c^2+s^2) (hk : 0 < k) (hm : 0 < e^2+f^2)
    (hdis : Disjoint (interior (core p.1 p.2 c s h))
      (interior (core q.1 q.2 e f k))) :
    ∃ a b : ℝ, 0 < a^2+b^2 ∧
      h*squareSupport c s a b+k*squareSupport e f a b ≤ a*(q.1-p.1)+b*(q.2-p.2) := by
  have hd := hdis.mono
    (interior_mono (scaledSquare_subset_core p c s h hh hn))
    (interior_mono (scaledSquare_subset_core q e f k hk hm))
  have hd' : Disjoint (interior (scaledSquare p c s h)) (scaledSquare q e f k) := by
    simpa only [scaledSquare,square_closure_interior] using hd.closure_right isOpen_interior
  obtain ⟨F,t,hF,hleft,hright⟩ := geometric_hahn_banach_of_nonempty_interior
    (square_convex p.1 p.2 (c/(h*(c^2+s^2))) (s/(h*(c^2+s^2))))
    (square_convex q.1 q.2 (e/(k*(e^2+f^2))) (f/(k*(e^2+f^2)))) hd'
    ⟨p,square_center_mem_interior _ _ _ _⟩
    ⟨q,interior_subset (square_center_mem_interior _ _ _ _)⟩
  let a := F (1,0)
  let b := F (0,1)
  have hab : 0 < a^2+b^2 := by
    by_contra hzero
    have ha : a=0 := by nlinarith [sq_nonneg b]
    have hb : b=0 := by nlinarith [sq_nonneg a]
    apply hF
    apply ContinuousLinearMap.ext
    intro z
    rw [functional_coords]
    change z.1*a+z.2*b=0
    rw [ha,hb];ring
  obtain ⟨x,hx,hex⟩ := scaledSquare_support_attained p c s h a b hh hn
  obtain ⟨y,hy,hey⟩ := scaledSquare_support_attained q e f k (-a) (-b) hk hm
  rw [squareSupport_neg] at hey
  have hx' := hleft x hx
  have hy' := hright y hy
  rw [functional_coords] at hx' hy'
  change x.1*a+x.2*b ≤ t at hx'
  change t ≤ y.1*a+y.2*b at hy'
  exact ⟨a,b,hab,by nlinarith only [hex,hey,hx',hy']⟩

noncomputable def frameC (c s e f : ℝ) : ℝ := (c*e+s*f)/(c^2+s^2)
noncomputable def frameS (c s e f : ℝ) : ℝ := (c*f-s*e)/(c^2+s^2)
noncomputable def framePoint (c s : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  ((c*z.1+s*z.2)/(c^2+s^2),(c*z.2-s*z.1)/(c^2+s^2))

/-- The exact unequal-core finite-axis theorem in the first core's rational
frame. All denominator positivity is explicit. -/
theorem core_disjoint_frame_axis (p q : ℝ × ℝ) (c s h e f k : ℝ)
    (hh : 0 < h) (hn : 0 < c^2+s^2) (hk : 0 < k) (hm : 0 < e^2+f^2)
    (hdis : Disjoint (interior (core p.1 p.2 c s h))
      (interior (core q.1 q.2 e f k))) :
    AxisSeparated h k (frameC c s e f) (frameS c s e f)
      ((framePoint c s q).1-(framePoint c s p).1)
      ((framePoint c s q).2-(framePoint c s p).2) := by
  obtain ⟨a,b,hab,hgap⟩ := core_disjoint_separator p q c s h e f k hh hn hk hm hdis
  let C := frameC c s e f
  let S := frameS c s e f
  let x := a*c+b*s
  let y := b*c-a*s
  let dx := (framePoint c s q).1-(framePoint c s p).1
  let dy := (framePoint c s q).2-(framePoint c s p).2
  have hne := ne_of_gt hn
  have hnorm : C^2+S^2=(e^2+f^2)/(c^2+s^2) := by
    dsimp [C,S,frameC,frameS]
    field_simp
    ring
  have hcs : 0 < C^2+S^2 := by rw [hnorm];exact div_pos hm hn
  have hxy2 : x^2+y^2=(c^2+s^2)*(a^2+b^2) := by dsimp [x,y];ring
  have hxypos : 0 < |x|+|y| := by
    by_contra hz
    have hx0 : x=0 := abs_eq_zero.mp (by linarith [abs_nonneg x,abs_nonneg y])
    have hy0 : y=0 := abs_eq_zero.mp (by linarith [abs_nonneg x,abs_nonneg y])
    have hp := mul_pos hn hab
    rw [hx0,hy0] at hxy2
    nlinarith only [hxy2,hp]
  have hp1 : C*x+S*y=a*e+b*f := by
    dsimp [C,S,frameC,frameS,x,y]
    field_simp
    ring
  have hp2 : C*y-S*x=b*e-a*f := by
    dsimp [C,S,frameC,frameS,x,y]
    field_simp
    ring
  have hd : x*dx+y*dy=a*(q.1-p.1)+b*(q.2-p.2) := by
    dsimp [x,y,dx,dy,framePoint]
    field_simp
    ring
  apply support_implies_axis h k C S x y dx dy hcs hxypos
  rw [hd]
  have he : squareSupport C S x y=squareSupport e f a b := by
    dsimp [squareSupport]
    rw [mul_comm x C,mul_comm y S,mul_comm y C,mul_comm x S,hp1,hp2]
  rw [he]
  convert hgap using 1 <;> dsimp [x,y,squareSupport] <;> ring

/-- Four original-coordinate support axes. This form avoids rational division
in the finite certificate checker. -/
def RawAxisSeparated (c s h e f k dx dy : ℝ) : Prop :=
  (h*(c^2+s^2)+k*(|c*e+s*f|+|c*f-s*e|))/2 ≤ |c*dx+s*dy| ∨
  (h*(c^2+s^2)+k*(|c*e+s*f|+|c*f-s*e|))/2 ≤ |c*dy-s*dx| ∨
  (h*(|c*e+s*f|+|c*f-s*e|)+k*(e^2+f^2))/2 ≤ |e*dx+f*dy| ∨
  (h*(|c*e+s*f|+|c*f-s*e|)+k*(e^2+f^2))/2 ≤ |e*dy-f*dx|

theorem core_disjoint_axis (p q : ℝ × ℝ) (c s h e f k : ℝ)
    (hh : 0 < h) (hn : 0 < c^2+s^2) (hk : 0 < k) (hm : 0 < e^2+f^2)
    (hdis : Disjoint (interior (core p.1 p.2 c s h))
      (interior (core q.1 q.2 e f k))) :
    RawAxisSeparated c s h e f k (q.1-p.1) (q.2-p.2) := by
  have hs := core_disjoint_frame_axis p q c s h e f k hh hn hk hm hdis
  let C := frameC c s e f
  let S := frameS c s e f
  let dx := (framePoint c s q).1-(framePoint c s p).1
  let dy := (framePoint c s q).2-(framePoint c s p).2
  have habs : |C|+|S|=(|c*e+s*f|+|c*f-s*e|)/(c^2+s^2) := by
    dsimp [C,S,frameC,frameS]
    rw [abs_div,abs_div,abs_of_pos hn]
    ring
  have hnorm : C^2+S^2=(e^2+f^2)/(c^2+s^2) := by
    dsimp [C,S,frameC,frameS]
    field_simp [ne_of_gt hn]
    ring
  have hA : (h+k*(|C|+|S|))/2 =
      ((h*(c^2+s^2)+k*(|c*e+s*f|+|c*f-s*e|))/2)/(c^2+s^2) := by
    rw [habs];field_simp [ne_of_gt hn] <;> ring
  have hB : (h*(|C|+|S|)+k*(C^2+S^2))/2 =
      ((h*(|c*e+s*f|+|c*f-s*e|)+k*(e^2+f^2))/2)/(c^2+s^2) := by
    rw [habs,hnorm];ring
  have he0 : dx=(c*(q.1-p.1)+s*(q.2-p.2))/(c^2+s^2) := by dsimp [dx,framePoint];ring
  have he1 : dy=(c*(q.2-p.2)-s*(q.1-p.1))/(c^2+s^2) := by dsimp [dy,framePoint];ring
  have he2 : C*dx+S*dy=(e*(q.1-p.1)+f*(q.2-p.2))/(c^2+s^2) := by
    dsimp [C,S,dx,dy,frameC,frameS,framePoint]
    field_simp [ne_of_gt hn]
    ring
  have he3 : C*dy-S*dx=(e*(q.2-p.2)-f*(q.1-p.1))/(c^2+s^2) := by
    dsimp [C,S,dx,dy,frameC,frameS,framePoint]
    field_simp [ne_of_gt hn]
    ring
  change AxisSeparated h k C S dx dy at hs
  rw [AxisSeparated,hA,hB,he2,he3,he0,he1] at hs
  simpa only [RawAxisSeparated,abs_div,abs_of_pos hn,div_le_div_iff_of_pos_right hn] using hs

end Sq17.CoreSAT
#print axioms Sq17.CoreSAT.core_disjoint_separator
#print axioms Sq17.CoreSAT.core_disjoint_frame_axis

#print axioms Sq17.CoreSAT.core_disjoint_axis
