module

public import MathResearchAnalysis.PhysicalWeightedDrift
public import MathResearchAnalysis.SquareGridLaw
public import MathResearchAnalysis.SyncLowerScale

set_option autoImplicit false

/-!
# True clock survival and the synchronous quadratic lower tail

The original laws and actual scheduling comparison are used. Infinite recovery
times are retained. The final quadratic result has no probability premise.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.SynchronousQuadraticTail

open MeasureTheory

/-- Complementation uses the genuine probability law and measurable endpoint. -/
theorem clockProbability_eq_one_sub_extinction (n : Nat) (t : Real) :
    ClockRecoveryComparison.clockProbability n t = 1 -
      (ClockWordMarks.measure n).real {z | ClockExecutionLaw.endpoint n t
        (SquarePWMeasure.topConfig n) z = fun _ => false} := by
  exact probReal_compl_eq_one_sub
    ((ClockExecutionLaw.endpoint_measurable n t (SquarePWMeasure.topConfig n))
      (measurableSet_singleton (fun _ => false)))

/-- The same bound at every earlier horizon follows from the true mean bound. -/
theorem original_clock_survival_ge_half (L : Nat) (hL : 12288000 ≤ L)
    (T : NNReal) (hT : T ≤ PhysicalWeightedDrift.quadraticHorizon L) :
    (1/2 : Real) ≤ ClockRecoveryComparison.clockProbability
      (ClippedSquareCoordinates.parameter L) T := by
  have hp := WeightedAreaTail.threshold_pos L (by omega : 80 ≤ L)
  have hbound := PhysicalWeightedDrift.original_clock_extinction_le_linear_time L
    (by omega : 80 ≤ L) T
  have htime : (T : Real) ≤ (PhysicalWeightedDrift.quadraticHorizon L : Real) := hT
  have hcoef : 0 ≤ (18 * L + 12 : Real) := by positivity
  have hnum : (18 * L + 12 : Real) * (T : Real) + ((L : Real)+2)*(4*L+2) ≤
      ((L : Real)^3/128000)/2 :=
    calc
      _ ≤ (18 * L + 12 : Real) *
          (PhysicalWeightedDrift.quadraticHorizon L : Real) + ((L : Real)+2)*(4*L+2) :=
        add_le_add (mul_le_mul_of_nonneg_left htime hcoef) le_rfl
      _ ≤ _ := PhysicalWeightedDrift.quadratic_bound_le_half_threshold L hL
  have hhalf : ((18 * L + 12 : Real) * (T : Real) + ((L : Real)+2)*(4*L+2)) /
      ((L : Real)^3/128000) ≤ (1/2 : Real) := by
    apply (div_le_iff₀ hp).mpr
    linarith
  have hz : (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)).real
      {z | ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L) (T : Real)
        (SquarePWMeasure.topConfig (ClippedSquareCoordinates.parameter L)) z =
          fun _ => false} ≤ (1/2 : Real) := hbound.trans hhalf
  rw [clockProbability_eq_one_sub_extinction]
  linarith


/-- A genuine quadratic-scale survival bound in the original infinite-grid
synchronous law; the clock survival and scheduling error are proved inputs. -/
theorem synchronous_tail_ge_quarter (L : Nat) (hL : 196608000 ≤ L) :
    (1/4 : Real) ≤ InfiniteGridRandomDynamics.measure.real
      {η | (SyncLowerScale.rounds L : ℕ∞) < InfiniteGridRecoveryTime.synchronous
        (SquareGridEmbedding.extend (ClippedSquareCoordinates.parameter L)
          (SquarePWMeasure.topConfig (ClippedSquareCoordinates.parameter L))) η} := by
  have hclock := original_clock_survival_ge_half L (by omega : 12288000 ≤ L)
    ⟨SchedulingFailure.time (SyncLowerScale.rounds L),
      (SchedulingFailure.time_positive _).le⟩
    (SyncLowerScale.scheduling_time_le_horizon L hL)
  have hcompare := (SquareGridLaw.two_way_clock_tail
    (ClippedSquareCoordinates.parameter L) false (SyncLowerScale.rounds L)).1
  have herror := SyncLowerScale.scheduling_error_le_quarter L hL
  change (1/2 : Real) ≤ ClockRecoveryComparison.clockProbability
    (ClippedSquareCoordinates.parameter L)
    (SchedulingFailure.time (SyncLowerScale.rounds L)) at hclock
  linarith

end MathResearchAnalysis.SynchronousQuadraticTail

