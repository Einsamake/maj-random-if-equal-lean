module
public import MathResearchAnalysis.CrossSquareClockBound
public import MathResearchAnalysis.SyncUpperScale
public import MathResearchAnalysis.OriginalRecoveryProfile
public import Mathlib.Tactic
set_option autoImplicit false
/-! The genuine original synchronous exact-N quadratic expectation upper bound.
Clock success, scheduling error, both checkerboard phases, true restart and
extended integration are discharged; no core tail premise remains. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.OriginalQuadraticUpper
open MeasureTheory
open SyncUpperScale (layers block)

theorem original_clock_at_scheduling_le_eighth (N : Nat) (hN : 16≤N) :
    ClockRecoveryComparison.clockProbability (N-2) (SchedulingFailure.time (layers N)) ≤ (1/8 : Real) :=
  (ClockEndpointSurvival.clockProbability_antitone (N-2)
    (SyncUpperScale.mixingTime_le_scheduling_time N (by omega))).trans
      (CrossSquareClockBound.original_clock_survival_le_eighth N hN)

/-- Both common-mark checkerboard phases and the real scheduling error are paid. -/
theorem synchronous_block_tail_le_half (N : Nat) (hN : 16≤N) :
    (SquareRandomDynamics.measure (N-2)).real
      {η | (block N : ℕ∞)<SquareRecoveryTime.synchronous (N-2)
        (SquarePWMeasure.topConfig (N-2)) η} ≤ (1/2 : Real) := by
  have h := (SquareRecoveryTime.two_way_clock_tail (N-2) false (layers N)).2
  have hc := original_clock_at_scheduling_le_eighth N hN
  have he := SyncUpperScale.scheduling_error_le_eighth N hN
  simp only [Nat.cast_add,Nat.cast_ofNat] at he
  change (SquareRandomDynamics.measure (N-2)).real
      {η | (block N : ℕ∞)<SquareRecoveryTime.synchronous (N-2)
        (SquarePWMeasure.topConfig (N-2)) η} ≤ _ at h
  linarith

/-- Actual restart supplies geometric tails for the original extended recovery time. -/
theorem recovery_block_tail (N : Nat) (hN : 16≤N) (g : SquareSpin.Config (N-2)) (j : Nat) :
    SquareRandomDynamics.measure (N-2)
      {η | ((j*block N : Nat) : ℕ∞)<SquareRecoveryTime.synchronous (N-2) g η} ≤
        (1/2 : ENNReal)^j := by
  have hp := SquareRandomRestart.recovery_block_le_pow (N-2) g (block N) j
  have hb := synchronous_block_tail_le_half N hN
  have hr := hp.trans (pow_le_pow_left₀ measureReal_nonneg hb j)
  have h := ENNReal.ofReal_le_ofReal hr
  rw [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
  simpa only [ENNReal.ofReal_pow (by norm_num : (0:Real)≤1/2),
    show ENNReal.ofReal (1/2 : Real)=(1/2 : ENNReal) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:Real)<2)]
      norm_num] using h

/-- Infinity is retained until the genuine block-tail bound implies finite mean. -/
theorem finiteExpected_le_two_blocks (N : Nat) (hN : 16≤N) (g : SquareSpin.Config (N-2)) :
    OriginalRecoveryProfile.finiteExpected (N-2) g ≤ 2*(block N : ENNReal) := by
  exact ExtendedBlockTail.lintegral_le_two_blocks (SquareRandomDynamics.measure (N-2))
    (SquareRecoveryTime.synchronous (N-2) g) (SquareRecoveryTime.synchronous_measurable (N-2) g)
    (block N) (by have h := SyncUpperScale.block_positive N; omega) (recovery_block_tail N hN g)

theorem finiteExpected_le_quadratic (N : Nat) (hN : 16≤N) (g : SquareSpin.Config (N-2)) :
    OriginalRecoveryProfile.finiteExpected (N-2) g ≤
      ENNReal.ofReal (664066*(N : Real)^2) := by
  have hb : (block N : Real)≤332033*(N : Real)^2 := by
    exact_mod_cast SyncUpperScale.block_le_quadratic N (by omega : 1≤N)
  calc
    _ ≤ 2*(block N : ENNReal) := finiteExpected_le_two_blocks N hN g
    _ = ENNReal.ofReal (2*(block N : Real)) := by simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [hb])

/-- Original exact-N worst extended expectation, including both homogeneous
backgrounds and arbitrary translated perturbations, with no probability input. -/
theorem tau_quadratic_upper_bound (N : Nat) (hN : 16≤N) :
    OriginalRecoveryProfile.tau N ≤ ENNReal.ofReal (664066*(N : Real)^2) := by
  rw [OriginalRecoveryProfile.tau_eq_normalizedTau N (by omega)]
  apply iSup_le
  intro g
  apply iSup_le
  intro _
  exact finiteExpected_le_quadratic N hN g

theorem tau_lt_top (N : Nat) (hN : 16≤N) : OriginalRecoveryProfile.tau N<⊤ :=
  (tau_quadratic_upper_bound N hN).trans_lt ENNReal.ofReal_lt_top
end MathResearchAnalysis.OriginalQuadraticUpper
