import MathResearchAnalysis.ClockLiteratureTransfer
import MathResearchAnalysis.FirstMomentClockUpper

open MathResearchAnalysis
open scoped ENNReal

#print axioms ClockLiteratureTransfer.clockProbability_mono
#print axioms ClockLiteratureTransfer.transfer
#print axioms ClockLiteratureTransfer.exists_comparison_rounds
#print axioms ClockLiteratureTransfer.tau_theta_of_odd_clock_window
#print axioms DeterministicClockRestart.endpoint_joint
#print axioms DeterministicClockRestart.endpoint_probability
#print axioms FirstMomentClockUpper.count_failure_le
#print axioms FirstMomentClockUpper.one_interval
#print axioms FirstMomentClockUpper.restartLaw
#print axioms FirstMomentClockUpper.survival_step_le
#print axioms FirstMomentClockUpper.recovery_block_tail
#print axioms FirstMomentClockUpper.tau_explicit_upper

-- Actual sides 16 and 17 bracket differently.
example : ClockLiteratureTransfer.lowerRadius 14 = 7 ∧
    ClockLiteratureTransfer.upperRadius 14 = 8 ∧
    ClockLiteratureTransfer.lowerRadius 15 = 8 ∧
    ClockLiteratureTransfer.upperRadius 15 = 8 := by decide

example (n : Nat) (s : ℝ) (hs : 0 ≤ s) (v : ClockWordMarks.Site n)
    (ω : ExponentialClocks.Sample (ClockWordMarks.Site n)) :
    ClockCounting.clockCount v s ω = 0 ↔ s < ExponentialClocks.gap v 0 ω :=
  ClockCounting.clockCount_eq_zero_iff_gap v hs ω

example : FirstMomentClockUpper.block 16 = 297271553 := by decide

example : OriginalRecoveryProfile.tau 16 ≤ (594543106 : ENNReal) := by
  have h := FirstMomentClockUpper.tau_explicit_upper 16 (by decide)
  norm_num at h
  exact h

