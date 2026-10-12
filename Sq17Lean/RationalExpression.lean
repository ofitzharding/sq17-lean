import Sq17Lean.PropagationEndpoint

/-! Rational expression enclosure certificates. Every intermediate interval
is explicit, so producers can round outward without adding rounding to trust. -/
namespace Sq17.RationalExpression

structure Interval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

def Interval.Holds (i : Interval) (x : ℝ) : Prop := (i.lo:ℝ) ≤ x ∧ x ≤ i.hi

def Interval.subsetCheck (i j : Interval) : Bool := decide (j.lo ≤ i.lo ∧ i.hi ≤ j.hi)

theorem Interval.weaken (i j : Interval) (x : ℝ)
    (hc : i.subsetCheck j = true) (hx : i.Holds x) : j.Holds x := by
  have hq : j.lo ≤ i.lo ∧ i.hi ≤ j.hi := of_decide_eq_true hc
  have hr : (j.lo:ℝ) ≤ i.lo ∧ (i.hi:ℝ) ≤ j.hi := by exact_mod_cast hq
  exact ⟨hr.1.trans hx.1,hx.2.trans hr.2⟩

def Interval.add (i j : Interval) : Interval := ⟨i.lo+j.lo,i.hi+j.hi⟩
def Interval.neg (i : Interval) : Interval := ⟨-i.hi,-i.lo⟩
def Interval.mul (i j : Interval) : Interval :=
  ⟨min (min (i.lo*j.lo) (i.lo*j.hi)) (min (i.hi*j.lo) (i.hi*j.hi)),
   max (max (i.lo*j.lo) (i.lo*j.hi)) (max (i.hi*j.lo) (i.hi*j.hi))⟩
def Interval.inv (i : Interval) : Interval := ⟨i.hi⁻¹,i.lo⁻¹⟩
def Interval.abs (i : Interval) : Interval :=
  ⟨if 0 ≤ i.lo then i.lo else if i.hi ≤ 0 then -i.hi else 0,max |i.lo| |i.hi|⟩

theorem Interval.add_sound (i j : Interval) (x y : ℝ) (hx : i.Holds x) (hy : j.Holds y) :
    (i.add j).Holds (x+y) := by
  dsimp [Holds,add]; push_cast; exact ⟨add_le_add hx.1 hy.1,add_le_add hx.2 hy.2⟩
theorem Interval.neg_sound (i : Interval) (x : ℝ) (hx : i.Holds x) :
    i.neg.Holds (-x) := by
  dsimp [Holds,neg]; push_cast; exact ⟨neg_le_neg hx.2,neg_le_neg hx.1⟩

theorem Interval.mul_sound (i j : Interval) (x y : ℝ) (hx : i.Holds x) (hy : j.Holds y) :
    (i.mul j).Holds (x*y) := by
  have hi := Sq17.Propagation.mul_interval y i.lo i.hi x hx
  have hj0 := Sq17.Propagation.mul_interval i.lo j.lo j.hi y hy
  have hj1 := Sq17.Propagation.mul_interval i.hi j.lo j.hi y hy
  dsimp [Holds,mul]; push_cast
  constructor
  · have h0 := min_le_left (min ((i.lo:ℝ)*j.lo) ((i.lo:ℝ)*j.hi)) (min ((i.hi:ℝ)*j.lo) ((i.hi:ℝ)*j.hi))
    have h1 := min_le_right (min ((i.lo:ℝ)*j.lo) ((i.lo:ℝ)*j.hi)) (min ((i.hi:ℝ)*j.lo) ((i.hi:ℝ)*j.hi))
    have h := le_min (h0.trans hj0.1) (h1.trans hj1.1)
    simp only [mul_comm y] at hi
    exact h.trans hi.1
  · have h0 := le_max_left (max ((i.lo:ℝ)*j.lo) ((i.lo:ℝ)*j.hi)) (max ((i.hi:ℝ)*j.lo) ((i.hi:ℝ)*j.hi))
    have h1 := le_max_right (max ((i.lo:ℝ)*j.lo) ((i.lo:ℝ)*j.hi)) (max ((i.hi:ℝ)*j.lo) ((i.hi:ℝ)*j.hi))
    have h := max_le (hj0.2.trans h0) (hj1.2.trans h1)
    simp only [mul_comm y] at hi
    exact hi.2.trans h

theorem Interval.inv_sound (i : Interval) (x : ℝ)
    (hn : 0 < i.lo ∨ i.hi < 0) (hx : i.Holds x) : i.inv.Holds x⁻¹ := by
  dsimp [Holds,inv]; push_cast
  rcases hn with hn | hn
  · have hpos : (0:ℝ) < i.lo := by exact_mod_cast hn
    have hxpos := hpos.trans_le hx.1
    exact ⟨(inv_le_inv₀ (hxpos.trans_le hx.2) hxpos).2 hx.2,
      (inv_le_inv₀ hxpos hpos).2 hx.1⟩
  · have hneg : (i.hi:ℝ) < 0 := by exact_mod_cast hn
    have hxneg := hx.2.trans_lt hneg
    exact ⟨(inv_le_inv_of_neg hneg hxneg).2 hx.2,
      (inv_le_inv_of_neg hxneg (hx.1.trans_lt hxneg)).2 hx.1⟩

theorem Interval.abs_sound (i : Interval) (x : ℝ) (hx : i.Holds x) : i.abs.Holds |x| := by
  constructor
  · dsimp [abs]
    split_ifs with hlo hhi
    · have hr : (0:ℝ) ≤ i.lo := by exact_mod_cast hlo
      simpa only [abs_of_nonneg (hr.trans hx.1)] using hx.1
    · have hr : (i.hi:ℝ) ≤ 0 := by exact_mod_cast hhi
      push_cast
      simpa only [abs_of_nonpos (hx.2.trans hr)] using neg_le_neg hx.2
    · exact_mod_cast abs_nonneg x
  · change |x| ≤ ((max |i.lo| |i.hi| : ℚ):ℝ)
    push_cast
    apply abs_le.mpr
    exact ⟨(abs_le.mp (le_max_left |(i.lo:ℝ)| |(i.hi:ℝ)|)).1.trans hx.1,
      hx.2.trans (abs_le.mp (le_max_right |(i.lo:ℝ)| |(i.hi:ℝ)|)).2⟩

inductive Cert where
  | constant (q : ℚ)
  | x
  | y
  | add (bound : Interval) (a b : Cert)
  | mul (bound : Interval) (a b : Cert)
  | neg (bound : Interval) (a : Cert)
  | inv (bound : Interval) (a : Cert)
  | abs (bound : Interval) (a : Cert)

noncomputable def Cert.eval (x y : ℝ) : Cert → ℝ
  | .constant q => q
  | .x => x
  | .y => y
  | .add _ a b => a.eval x y+b.eval x y
  | .mul _ a b => a.eval x y*b.eval x y
  | .neg _ a => -a.eval x y
  | .inv _ a => (a.eval x y)⁻¹
  | .abs _ a => |a.eval x y|

def Cert.bound (ix iy : Interval) : Cert → Interval
  | .constant q => ⟨q,q⟩
  | .x => ix
  | .y => iy
  | .add i _ _ | .mul i _ _ | .neg i _ | .inv i _ | .abs i _ => i

def Cert.check (ix iy : Interval) : Cert → Bool
  | .constant _ | .x | .y => true
  | .add i a b => a.check ix iy && b.check ix iy && ((a.bound ix iy).add (b.bound ix iy)).subsetCheck i
  | .mul i a b => a.check ix iy && b.check ix iy && ((a.bound ix iy).mul (b.bound ix iy)).subsetCheck i
  | .neg i a => a.check ix iy && (a.bound ix iy).neg.subsetCheck i
  | .inv i a => a.check ix iy && decide (0 < (a.bound ix iy).lo ∨ (a.bound ix iy).hi < 0) &&
      (a.bound ix iy).inv.subsetCheck i
  | .abs i a => a.check ix iy && (a.bound ix iy).abs.subsetCheck i

theorem Cert.check_sound (ix iy : Interval) (e : Cert) (x y : ℝ)
    (hx : ix.Holds x) (hy : iy.Holds y) (hc : e.check ix iy = true) :
    (e.bound ix iy).Holds (e.eval x y) := by
  induction e with
  | constant q => exact ⟨le_rfl,le_rfl⟩
  | x => exact hx
  | y => exact hy
  | add i a b ha hb =>
    simp only [check,Bool.and_eq_true_iff] at hc
    exact Interval.weaken _ _ _ hc.2 (Interval.add_sound _ _ _ _ (ha hc.1.1) (hb hc.1.2))
  | mul i a b ha hb =>
    simp only [check,Bool.and_eq_true_iff] at hc
    exact Interval.weaken _ _ _ hc.2 (Interval.mul_sound _ _ _ _ (ha hc.1.1) (hb hc.1.2))
  | neg i a ha =>
    simp only [check,Bool.and_eq_true_iff] at hc
    exact Interval.weaken _ _ _ hc.2 (Interval.neg_sound _ _ (ha hc.1))
  | inv i a ha =>
    simp only [check,Bool.and_eq_true_iff] at hc
    exact Interval.weaken _ _ _ hc.2 (Interval.inv_sound _ _ (of_decide_eq_true hc.1.2) (ha hc.1.1))
  | abs i a ha =>
    simp only [check,Bool.and_eq_true_iff] at hc
    exact Interval.weaken _ _ _ hc.2 (Interval.abs_sound _ _ (ha hc.1))

end Sq17.RationalExpression
#print axioms Sq17.RationalExpression.Cert.check_sound
