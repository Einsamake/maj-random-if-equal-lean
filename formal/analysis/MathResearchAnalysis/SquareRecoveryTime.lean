module

public import MathResearchAnalysis.SquareRandomComparison
public import MathResearchAnalysis.ExtendedRecoveryTime
public import MathResearchAnalysis.SynchronousClockComparison

set_option autoImplicit false

/-!
# Actual extended recovery times of the finite-square random dynamics

The first zero times are genuine ENat-valued random variables. Absorption is
discharged from the actual rule, so their tails equal current nonzero events
without any finite-hitting premise. Initial-state domination is pathwise.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.SquareRecoveryTime

abbrev Config (n : Nat) := SquareSpin.Config n
abbrev Sample (n : Nat) := SquareRandomDynamics.Sample n

def synchronous (n : Nat) (initial : Config n) : Sample n → ℕ∞ :=
  ExtendedRecoveryTime.time (SquareRandomDynamics.synchronous n initial)
    (SquareRandomComparison.zeroConfig n)

def alternating (n : Nat) (initial : Config n) (phase : Bool) : Sample n → ℕ∞ :=
  ExtendedRecoveryTime.time (SquareRandomDynamics.alternating n initial phase)
    (SquareRandomComparison.zeroConfig n)

theorem synchronous_absorbing (n : Nat) (initial : Config n) :
    ExtendedRecoveryTime.Absorbing (SquareRandomDynamics.synchronous n initial)
      (SquareRandomComparison.zeroConfig n) := by
  intro η s t hst hs
  exact (SquareRandomComparison.isZero_iff_eq_zero _).mp
    (SquareDynamics.synchronous_zero_persists (SquareRandomDynamics.marks η) initial
      ((SquareRandomComparison.isZero_iff_eq_zero _).mpr hs) hst)

theorem alternating_absorbing (n : Nat) (initial : Config n) (phase : Bool) :
    ExtendedRecoveryTime.Absorbing (SquareRandomDynamics.alternating n initial phase)
      (SquareRandomComparison.zeroConfig n) := by
  intro η s t hst hs
  exact (SquareRandomComparison.isZero_iff_eq_zero _).mp
    (SquareDynamics.alternating_zero_persists (SquareRandomDynamics.marks η) initial phase
      ((SquareRandomComparison.isZero_iff_eq_zero _).mpr hs) hst)

theorem synchronous_measurable (n : Nat) (initial : Config n) :
    Measurable (synchronous n initial) :=
  ExtendedRecoveryTime.time_measurable _ _ (SquareRandomDynamics.synchronous_measurable n initial)

theorem alternating_measurable (n : Nat) (initial : Config n) (phase : Bool) :
    Measurable (alternating n initial phase) :=
  ExtendedRecoveryTime.time_measurable _ _ (SquareRandomDynamics.alternating_measurable n initial phase)

theorem synchronous_le_nat_iff (n : Nat) (initial : Config n) (η : Sample n) (t : Nat) :
    synchronous n initial η ≤ (t : ℕ∞) ↔
      SquareRandomDynamics.synchronous n initial t η = SquareRandomComparison.zeroConfig n :=
  ExtendedRecoveryTime.time_le_nat_iff_of_absorbing _ _ (synchronous_absorbing n initial) η t

theorem alternating_le_nat_iff (n : Nat) (initial : Config n) (phase : Bool)
    (η : Sample n) (t : Nat) :
    alternating n initial phase η ≤ (t : ℕ∞) ↔
      SquareRandomDynamics.alternating n initial phase t η = SquareRandomComparison.zeroConfig n :=
  ExtendedRecoveryTime.time_le_nat_iff_of_absorbing _ _ (alternating_absorbing n initial phase) η t

theorem synchronous_tail_iff (n : Nat) (initial : Config n) (η : Sample n) (t : Nat) :
    (t : ℕ∞) < synchronous n initial η ↔
      SquareRandomDynamics.synchronous n initial t η ≠ SquareRandomComparison.zeroConfig n :=
  ExtendedRecoveryTime.time_gt_nat_iff_of_absorbing _ _ (synchronous_absorbing n initial) η t

theorem alternating_tail_iff (n : Nat) (initial : Config n) (phase : Bool)
    (η : Sample n) (t : Nat) :
    (t : ℕ∞) < alternating n initial phase η ↔
      SquareRandomDynamics.alternating n initial phase t η ≠ SquareRandomComparison.zeroConfig n :=
  ExtendedRecoveryTime.time_gt_nat_iff_of_absorbing _ _ (alternating_absorbing n initial phase) η t

theorem synchronous_tail_probability (n : Nat) (initial : Config n) (t : Nat) :
    (SquareRandomDynamics.measure n).real {η | (t : ℕ∞) < synchronous n initial η} =
      SquareRandomComparison.synchronousProbability n initial t := by
  congr 1
  ext η
  exact synchronous_tail_iff n initial η t

theorem alternating_tail_probability (n : Nat) (initial : Config n) (phase : Bool) (t : Nat) :
    (SquareRandomDynamics.measure n).real {η | (t : ℕ∞) < alternating n initial phase η} =
      SquareRandomComparison.alternatingProbability n initial phase t := by
  congr 1
  ext η
  exact alternating_tail_iff n initial phase η t

theorem synchronous_initial_mono {n : Nat} {first second : Config n}
    (h : first ≤ second) (η : Sample n) : synchronous n first η ≤ synchronous n second η := by
  cases htime : synchronous n second η using ENat.recTopCoe with
  | top => simp only [le_top]
  | coe t =>
    have hz : SquareRandomDynamics.synchronous n second t η = SquareRandomComparison.zeroConfig n :=
      (synchronous_le_nat_iff n second η t).mp (by rw [htime])
    have hfirst : SquareRandomDynamics.synchronous n first t η =
        SquareRandomComparison.zeroConfig n :=
      le_antisymm
        (by simpa only [hz] using SquareRandomComparison.synchronous_initial_mono η h t)
        (fun _ => Bool.false_le _)
    exact (synchronous_le_nat_iff n first η t).mpr hfirst

theorem synchronous_le_top (n : Nat) (initial : Config n) (η : Sample n) :
    synchronous n initial η ≤ synchronous n (SquarePWMeasure.topConfig n) η :=
  synchronous_initial_mono (fun _ => Bool.le_true _) η

theorem two_way_clock_tail (n : Nat) (c : Bool) (k : Nat) :
    ClockRecoveryComparison.clockProbability n (SchedulingFailure.time k) ≤
        (SquareRandomDynamics.measure n).real
          {η | (k : ℕ∞) < synchronous n (SquarePWMeasure.topConfig n) η} +
        ((6 : ℝ) / 5) * (n + 2 : ℝ) ^ 2 * ((2 : ℝ)⁻¹) ^ (k + 1) ∧
      (SquareRandomDynamics.measure n).real
          {η | ((2 * SchedulingFailure.rankThreshold k + 1 : Nat) : ℕ∞) <
            synchronous n (SquarePWMeasure.topConfig n) η} ≤
        2 * ClockRecoveryComparison.clockProbability n (SchedulingFailure.time k) +
          2 * (((6 : ℝ) / 5) * (n + 2 : ℝ) ^ 2 * ((2 : ℝ)⁻¹) ^ (k + 1)) := by
  rw [synchronous_tail_probability, synchronous_tail_probability]
  exact SynchronousClockComparison.two_way_scheduling_scale n c k

end MathResearchAnalysis.SquareRecoveryTime
