import Sq17Lean.SquareSeparationGeometry

/-! Explicit finite axis witnesses for use by checked local feature tables. -/
namespace Sq17.WallCapacity

noncomputable def edgeNormal (ux uy vx vy : ℝ) : Fin 4 → ℝ × ℝ :=
  ![(ux,uy),(-uy,ux),(vx,vy),(-vy,vx)]

theorem support_self (ux uy : ℝ) (hu : ux^2+uy^2=1) :
    squareSupport ux uy ux uy = 1/2 := by
  have h1 : ux*ux+uy*uy=1 := by nlinarith
  have h2 : uy*ux-ux*uy=0 := by ring
  simp [squareSupport,h1,h2]

theorem support_swap (ux uy vx vy : ℝ) :
    squareSupport ux uy vx vy = squareSupport vx vy ux uy := by
  have h1 : vx*ux+vy*uy=ux*vx+uy*vy := by ring
  have h2 : vy*ux-vx*uy= -(uy*vx-ux*vy) := by ring
  simp only [squareSupport,h1,h2,abs_neg]

theorem support_perp (ux uy a b : ℝ) :
    squareSupport ux uy (-b) a = squareSupport ux uy a b := by
  have h1 : (-b)*ux+a*uy= -(b*ux-a*uy) := by ring
  have h2 : a*ux-(-b)*uy=a*ux+b*uy := by ring
  simp only [squareSupport,h1,h2,abs_neg,add_comm]

theorem edgeNormal_unit (ux uy vx vy : ℝ)
    (hu : ux^2+uy^2=1) (hv : vx^2+vy^2=1) (i : Fin 4) :
    (edgeNormal ux uy vx vy i).1^2+(edgeNormal ux uy vx vy i).2^2=1 := by
  fin_cases i <;> simp [edgeNormal] <;> nlinarith

theorem edgeNormal_support (ux uy vx vy : ℝ)
    (hu : ux^2+uy^2=1) (hv : vx^2+vy^2=1) (i : Fin 4) :
    squareSupport ux uy (edgeNormal ux uy vx vy i).1 (edgeNormal ux uy vx vy i).2+
    squareSupport vx vy (edgeNormal ux uy vx vy i).1 (edgeNormal ux uy vx vy i).2 =
      (1+|ux*vx+uy*vy|+|ux*vy-uy*vx|)/2 := by
  have hbase : squareSupport vx vy ux uy = (|ux*vx+uy*vy|+|ux*vy-uy*vx|)/2 := by
    dsimp [squareSupport]
    rw [show uy*vx-ux*vy= -(ux*vy-uy*vx) by ring,abs_neg]
  have hfirst : squareSupport ux uy ux uy+squareSupport vx vy ux uy =
      (1+|ux*vx+uy*vy|+|ux*vy-uy*vx|)/2 := by rw [support_self ux uy hu,hbase];ring
  have hsecond : squareSupport ux uy vx vy+squareSupport vx vy vx vy =
      (1+|ux*vx+uy*vy|+|ux*vy-uy*vx|)/2 := by
    rw [support_swap ux uy vx vy,support_self vx vy hv,hbase];ring
  fin_cases i
  · exact hfirst
  · simpa [edgeNormal,support_perp] using hfirst
  · exact hsecond
  · simpa [edgeNormal,support_perp] using hsecond

/-- A disjoint pair has one of eight directed edge-normal witnesses. -/
theorem square_disjoint_finite_axis (p q : ℝ × ℝ) (ux uy vx vy : ℝ)
    (hu : ux^2+uy^2=1) (hv : vx^2+vy^2=1)
    (hdis : Disjoint (interior (Sq17.sq p.1 p.2 ux uy))
      (interior (Sq17.sq q.1 q.2 vx vy))) :
    ∃ i : Fin 4, ∃ σ : ℝ, (σ=1 ∨ σ= -1) ∧
      squareSupport ux uy (σ*(edgeNormal ux uy vx vy i).1) (σ*(edgeNormal ux uy vx vy i).2)+
      squareSupport vx vy (σ*(edgeNormal ux uy vx vy i).1) (σ*(edgeNormal ux uy vx vy i).2) ≤
      (σ*(edgeNormal ux uy vx vy i).1)*(q.1-p.1)+
      (σ*(edgeNormal ux uy vx vy i).2)*(q.2-p.2) := by
  let H := (1+|ux*vx+uy*vy|+|ux*vy-uy*vx|)/2
  have he : ∃ i : Fin 4, H ≤ |(edgeNormal ux uy vx vy i).1*(q.1-p.1)+
      (edgeNormal ux uy vx vy i).2*(q.2-p.2)| := by
    rcases square_disjoint_axis p q ux uy vx vy hu hv hdis with h|h|h|h
    · exact ⟨0,h⟩
    · refine ⟨1,?_⟩
      convert h using 1 <;> simp only [edgeNormal,Matrix.cons_val_one,Matrix.cons_val_zero,Prod.fst,Prod.snd] <;> congr 1 <;> ring
    · exact ⟨2,h⟩
    · refine ⟨3,?_⟩
      convert h using 1 <;> simp [edgeNormal] <;> congr 1 <;> ring
  obtain ⟨i,hi⟩ := he
  let a := (edgeNormal ux uy vx vy i).1
  let b := (edgeNormal ux uy vx vy i).2
  have hs : squareSupport ux uy a b+squareSupport vx vy a b=H :=
    edgeNormal_support ux uy vx vy hu hv i
  by_cases hp : 0 ≤ a*(q.1-p.1)+b*(q.2-p.2)
  · refine ⟨i,1,Or.inl rfl,?_⟩
    simp only [one_mul]
    rw [hs]
    exact (abs_of_nonneg hp) ▸ hi
  · refine ⟨i,-1,Or.inr rfl,?_⟩
    simp only [neg_one_mul,squareSupport_neg]
    change squareSupport ux uy a b+squareSupport vx vy a b ≤ -a*(q.1-p.1)+ -b*(q.2-p.2)
    rw [hs]
    have hn : a*(q.1-p.1)+b*(q.2-p.2) ≤ 0 := le_of_not_ge hp
    rw [abs_of_nonpos hn] at hi
    linarith

#print axioms square_disjoint_finite_axis
end Sq17.WallCapacity
