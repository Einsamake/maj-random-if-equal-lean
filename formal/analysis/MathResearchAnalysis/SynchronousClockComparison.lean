module

public import MathResearchAnalysis.SquareRandomComparison
public import MathResearchAnalysis.SquareScanOrder

set_option autoImplicit false

/-!
# Actual synchronous / clock endpoint comparisons

The same-mark two-phase splitting is converted to probabilities by a union
bound. Deleting the first scan slot aligns the opposite phase. No independence
of the two phases or probability-comparison hypothesis is used.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.SynchronousClockComparison

open SquareRandomComparison ClockRecoveryComparison

def synchronousProbability (n t : Nat) : ℝ :=
  SquareRandomComparison.synchronousProbability n (SquarePWMeasure.topConfig n) t

theorem scan_next_le_synchronous (n : Nat) (c : Bool) (k : Nat) :
    scanProbability n c (k + 1) ≤ synchronousProbability n k := by
  have h := alternatingProbability_next_le_synchronous n (SquarePWMeasure.topConfig n) (!c) k
  rw [alternatingProbability_top_eq_scanProbability, Bool.not_not] at h
  exact h

theorem synchronous_le_twice_scan (n q : Nat) :
    synchronousProbability n (2 * q + 1) ≤ 2 * scanProbability n true (2 * q) := by
  have h := synchronousProbability_le_sum_alternating n (SquarePWMeasure.topConfig n) (2 * q + 1)
  rw [alternatingProbability_top_eq_scanProbability,
    alternatingProbability_top_eq_scanProbability] at h
  have hf := SquareScanOrder.scanMean_succ_le n true 0 (2 * q)
    nonzero (nonzero_monotone n)
  have ht := SquareScanOrder.scanMean_opposite_succ_le n false 0 (2 * q)
    nonzero (nonzero_monotone n)
  change scanProbability n true (2 * q + 1) ≤ scanProbability n true (2 * q) at hf
  change scanProbability n false (2 * q + 1) ≤ scanProbability n true (2 * q) at ht
  change synchronousProbability n (2 * q + 1) ≤
    scanProbability n true (2 * q + 1) + scanProbability n false (2 * q + 1) at h
  linarith

theorem clock_le_synchronous_add_completion (n : Nat) (c : Bool) (k : Nat) (t : ℝ) :
    clockProbability n t ≤ synchronousProbability n k +
      (ExponentialClocks.clockMeasure (SquareTasks.Vertex n)).real
        {ω | (t : WithTop ℝ) < ClockMaximum.squareMaximum n c k ω} :=
  (clockProbability_le_scan_add_completion n c k t).trans
    (add_le_add (scan_next_le_synchronous n c k) le_rfl)

theorem synchronous_le_twice_clock_add_rank (n q : Nat) (t : ℝ) :
    synchronousProbability n (2 * q + 1) ≤ 2 * clockProbability n t +
      2 * (ExponentialClocks.clockMeasure (SquareTasks.Vertex n)).real
        (ClockRankTail.rankLarge n t q) := by
  have hs := synchronous_le_twice_scan n q
  have hc := scanProbability_le_clock_add_rank n q t
  linarith

theorem two_way_scheduling_scale (n : Nat) (c : Bool) (k : Nat) :
    clockProbability n (SchedulingFailure.time k) ≤ synchronousProbability n k +
        ((6 : ℝ) / 5) * (n + 2 : ℝ) ^ 2 * ((2 : ℝ)⁻¹) ^ (k + 1) ∧
      synchronousProbability n (2 * SchedulingFailure.rankThreshold k + 1) ≤
        2 * clockProbability n (SchedulingFailure.time k) +
          2 * (((6 : ℝ) / 5) * (n + 2 : ℝ) ^ 2 * ((2 : ℝ)⁻¹) ^ (k + 1)) := by
  have hc := ClockRecoveryComparison.two_way_scheduling_scale n c k
  constructor
  · exact hc.1.trans (add_le_add (scan_next_le_synchronous n c k) le_rfl)
  · have hs := synchronous_le_twice_scan n (SchedulingFailure.rankThreshold k)
    linarith [hc.2]

end MathResearchAnalysis.SynchronousClockComparison
