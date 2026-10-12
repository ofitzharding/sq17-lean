import Sq17Lean.PropagationAngleNormalize

/-! The capture trace seeds a different angle window for each owner. These
endpoints are the first/last I-row bounds, before any trace pruning. -/
namespace Sq17.CaptureSeedWindows

/-- One half of the decimal upper bound in `Real.pi_lt_d20`. -/
def halfPiUpper : ℚ := 314159265358979323847 / 200000000000000000000

def windowData : Array (ℚ × ℚ) := #[
  ((-3537118876018313/4503599627370496 : ℚ), (3537118876018319/4503599627370496 : ℚ)),
  ((-884279719004579/1125899906842624 : ℚ), (884279719004579/1125899906842624 : ℚ)),
  ((-884279719004579/1125899906842624 : ℚ), (884279719004579/1125899906842624 : ℚ)),
  ((-408343947878127/4503599627370496 : ℚ), (6665893804158505/4503599627370496 : ℚ)),
  ((-204171973939065/2251799813685248 : ℚ), (3332946902079251/2251799813685248 : ℚ)),
  ((-25521496742383/281474976710656 : ℚ), (833236725519813/562949953421312 : ℚ)),
  ((-3537118876018315/4503599627370496 : ℚ), (3537118876018317/4503599627370496 : ℚ)),
  ((-816687895756259/9007199254740992 : ℚ), (3332946902079251/2251799813685248 : ℚ)),
  ((-1603961308604587/1125899906842624 : ℚ), (164598129404571/1125899906842624 : ℚ)),
  ((-816687895756253/9007199254740992 : ℚ), (3332946902079253/2251799813685248 : ℚ)),
  ((-884279719004579/1125899906842624 : ℚ), (884279719004579/1125899906842624 : ℚ)),
  ((-884279719004579/1125899906842624 : ℚ), (884279719004579/1125899906842624 : ℚ)),
  ((-885926575938749/1125899906842624 : ℚ), (882632862070409/1125899906842624 : ℚ)),
  ((-816687895756261/9007199254740992 : ℚ), (3332946902079251/2251799813685248 : ℚ)),
  ((-1768559438009159/2251799813685248 : ℚ), (1768559438009157/2251799813685248 : ℚ)),
  ((-884279719004579/1125899906842624 : ℚ), (884279719004579/1125899906842624 : ℚ)),
  ((-7074237752036627/9007199254740992 : ℚ), (7074237752036637/9007199254740992 : ℚ))
]

def windows (i : Nat) : ℚ × ℚ := windowData[i]?.getD (0, 0)

/-- Every window contains zero and is strictly wider than half pi. -/
theorem rational_windows_checked : ∀ i : Fin 17,
    (windows i.val).1 ≤ 0 ∧ 0 ≤ (windows i.val).2 ∧
    halfPiUpper < (windows i.val).2 - (windows i.val).1 := by
  decide +kernel

theorem pi_half_lt_upper : Real.pi / 2 < (halfPiUpper : ℝ) := by
  have hp := Real.pi_lt_d20
  norm_num [halfPiUpper] at *
  linarith

theorem real_windows_checked (i : Fin 17) :
    ((windows i.val).1 : ℝ) ≤ 0 ∧ 0 ≤ ((windows i.val).2 : ℝ) ∧
    Real.pi / 2 < ((windows i.val).2 : ℝ) - ((windows i.val).1 : ℝ) := by
  have h := rational_windows_checked i
  have hlo : ((windows i.val).1 : ℝ) ≤ 0 := by exact_mod_cast h.1
  have hhi : 0 ≤ ((windows i.val).2 : ℝ) := by exact_mod_cast h.2.1
  have hw : (halfPiUpper : ℝ) < ((windows i.val).2 : ℝ) - ((windows i.val).1 : ℝ) := by
    exact_mod_cast h.2.2
  exact ⟨hlo, hhi, pi_half_lt_upper.trans hw⟩

end Sq17.CaptureSeedWindows
#print axioms Sq17.CaptureSeedWindows.rational_windows_checked
#print axioms Sq17.CaptureSeedWindows.real_windows_checked
