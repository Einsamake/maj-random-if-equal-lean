module

public import MathResearchAnalysis.ClockRankTail
public import MathResearchAnalysis.ActualClockTail

set_option autoImplicit false

/-!
# Joint clock-scheduling failure with explicit deterministic scales

The two existing model-derived tails control a single measurable clock event.
No CA extinction, censoring, or independent-path premise is used. This is a
clock-scheduling estimate, not a recovery-time theorem.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.SchedulingFailure

def time (k : Nat) : ℝ := 8 * Real.log 2 * (k + 1 : Nat)

def rankThreshold (k : Nat) : Nat := 128 * (k + 1)

def bad (n : Nat) (c : Bool) (k : Nat) :
    Set (ExponentialClocks.Sample (SquareTasks.Vertex n)) :=
  ClockRankTail.rankLarge n (time k) (rankThreshold k) ∪
    {ω | (time k : WithTop ℝ) < ClockMaximum.squareMaximum n c k ω}

theorem time_positive (k : Nat) : 0 < time k := by
  unfold time
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem bad_measurable (n : Nat) (c : Bool) (k : Nat) : MeasurableSet (bad n c k) :=
  (ClockRankTail.rankLarge_measurable n (time k) (rankThreshold k)).union
    (ActualClockTail.actual_square_eight_tail n c k (time k)).1

theorem clock_scale_identity (k : Nat) :
    (8 : ℝ) ^ (k + 1) * Real.exp (-time k / 2) = ((2 : ℝ)⁻¹) ^ (k + 1) := by
  have he : Real.exp (-4 * Real.log 2) = (16 : ℝ)⁻¹ := by
    rw [show -4 * Real.log 2 = -((4 : Nat) * Real.log 2) by norm_num,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  rw [show -time k / 2 = ((k + 1 : Nat) : ℝ) * (-4 * Real.log 2) by unfold time; ring,
    Real.exp_nat_mul, he, ← mul_pow]
  norm_num

theorem rank_scale_identity (k : Nat) :
    Real.exp (9 * time k) * ((2 : ℝ)⁻¹) ^ rankThreshold k =
      ((2 : ℝ)⁻¹) ^ (56 * (k + 1)) := by
  rw [show 9 * time k = ((72 * (k + 1) : Nat) : ℝ) * Real.log 2 by
    unfold time; push_cast; ring,
    Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have he : rankThreshold k = 72 * (k + 1) + 56 * (k + 1) := by
    unfold rankThreshold
    omega
  rw [he, pow_add, ← mul_assoc, ← mul_pow]
  norm_num

theorem bad_tail (n : Nat) (c : Bool) (k : Nat) :
    (ExponentialClocks.clockMeasure (SquareTasks.Vertex n)).real (bad n c k) ≤
      ((6 : ℝ) / 5) * (n + 2 : ℝ) ^ 2 * ((2 : ℝ)⁻¹) ^ (k + 1) := by
  have hr := ClockRankTail.rankLarge_half_tail n (time k) (rankThreshold k)
    (by unfold rankThreshold; omega)
  have hc := (ActualClockTail.actual_square_eight_tail n c k (time k)).2
  have hp : ((2 : ℝ)⁻¹) ^ (56 * (k + 1)) ≤ ((2 : ℝ)⁻¹) ^ (k + 1) := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hr' : (ExponentialClocks.clockMeasure (SquareTasks.Vertex n)).real
      (ClockRankTail.rankLarge n (time k) (rankThreshold k)) ≤
        ((n + 2 : ℝ) ^ 2 / 5) * ((2 : ℝ)⁻¹) ^ (k + 1) := by
    have hN : ((((n + 2) ^ 2 : Nat) : ℝ) / 5) = (n + 2 : ℝ) ^ 2 / 5 := by norm_cast
    rw [hN, mul_assoc, rank_scale_identity] at hr
    exact hr.trans (mul_le_mul_of_nonneg_left hp (by positivity))
  have hc' : (ExponentialClocks.clockMeasure (SquareTasks.Vertex n)).real
      {ω | (time k : WithTop ℝ) < ClockMaximum.squareMaximum n c k ω} ≤
        (n + 2 : ℝ) ^ 2 * ((2 : ℝ)⁻¹) ^ (k + 1) := by
    rw [mul_assoc, clock_scale_identity] at hc
    exact hc
  exact (measureReal_union_le _ _).trans ((add_le_add hr' hc').trans_eq (by ring))

end MathResearchAnalysis.SchedulingFailure
