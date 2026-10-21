module
public import MathResearchAnalysis.ClockGapReset
public import MathResearchAnalysis.MarkedClockFiltration
set_option autoImplicit false
/-! Resetting any gap whose ring is still in the future preserves the actual
clock and marked histories. No assumption that its preceding ring has already
occurred is required. These are pointwise statements about histories, not a
future distribution, conditional count, or compensation theorem. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.FutureGapHistory
open MeasureTheory Set

variable {V : Type*}

/-- The only timing assumption needed is that the reset identity is still
unobserved at r; the preceding time may itself be later than r. -/
theorem reset_generator_event_iff (v : V) (k : Nat) (r : Real)
    (ω : ExponentialClocks.Sample V)
    (hf : r < ArrivalFiltration.chronologicalArrival v k ω)
    (w : V) (j : Nat) (u : Real) (hu : u ≤ r) :
    (ArrivalFiltration.chronologicalArrival w j ω ≤ u ↔
      ArrivalFiltration.chronologicalArrival w j
        (ClockGapReset.reset v k r (RandomThresholdSurvival.restCoordinates v k ω)) ≤ u) := by
  by_cases hwv : w = v
  · subst w
    by_cases hjk : j < k
    · rw [ClockGapReset.arrival_before_gap_eq v k j r ω hjk]
    · have hkj : k ≤ j := Nat.le_of_not_gt hjk
      have horig : u < ArrivalFiltration.chronologicalArrival v j ω :=
        hu.trans_lt (hf.trans_le (ArrivalFiltration.chronologicalArrival_monotone v ω hkj))
      have hreset : u < ArrivalFiltration.chronologicalArrival v j
          (ClockGapReset.reset v k r (RandomThresholdSurvival.restCoordinates v k ω)) :=
        hu.trans_lt (ClockGapReset.reset_arrival_later_gt v k j r _ hkj)
      simp only [not_le.mpr horig, not_le.mpr hreset]
  · rw [ClockGapReset.arrival_other_site_eq v w k j r ω hwv]

theorem reset_history_event_iff (v : V) (k : Nat) (r : Real)
    (ω : ExponentialClocks.Sample V)
    (hf : r < ArrivalFiltration.chronologicalArrival v k ω)
    (E : Set (ExponentialClocks.Sample V))
    (hE : MeasurableSet[ArrivalFiltration.clockHistory V r] E) :
    (ω ∈ E ↔ ClockGapReset.reset v k r (RandomThresholdSurvival.restCoordinates v k ω) ∈ E) :=
  HistoryEventInvariant.clock_event_invariant r E hE ω _
    (reset_generator_event_iff v k r ω hf)

/-- The clipped nonnegative gap makes the previous time a lower bound even
on exceptional negative-coordinate samples. -/
theorem prior_le_current (v : V) (k : Nat) (ω : ExponentialClocks.Sample V) :
    ClockGapReset.prior v k (RandomThresholdSurvival.restCoordinates v k ω) ≤
      ArrivalFiltration.chronologicalArrival v k ω := by
  rw [ClockGapReset.prior_rest_eq_sum]
  unfold ArrivalFiltration.chronologicalArrival
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (le_max_right _ _)

/-- In particular the actual history is preserved when even the previous
ring is still later than r, outside the old candidate-interval hypothesis. -/
theorem prior_future_history_event_iff (v : V) (k : Nat) (r : Real)
    (ω : ExponentialClocks.Sample V)
    (hp : r < ClockGapReset.prior v k (RandomThresholdSurvival.restCoordinates v k ω))
    (E : Set (ExponentialClocks.Sample V))
    (hE : MeasurableSet[ArrivalFiltration.clockHistory V r] E) :
    (ω ∈ E ↔ ClockGapReset.reset v k r (RandomThresholdSurvival.restCoordinates v k ω) ∈ E) :=
  reset_history_event_iff v k r ω (hp.trans_le (prior_le_current v k ω)) E hE

open DropletClockLaw (Sample Event Vertex)

/-- The same reset on the actual joint sample, leaving every identity mark unchanged. -/
def resetSample (L : Nat) (v : Vertex L) (k : Nat) (r : Real)
    (z : Sample L) : Sample L :=
  (ClockGapReset.reset v k r (RandomThresholdSurvival.restCoordinates v k z.1), z.2)

theorem resetSample_measurable (L : Nat) (v : Vertex L) (k : Nat) (r : Real) :
    Measurable (resetSample L v k r) :=
  ((ClockGapReset.reset_measurable v k r).comp
    ((RandomThresholdSurvival.restCoordinates_measurable v k).comp measurable_fst)).prodMk
      measurable_snd

theorem resetSample_mark_eq (L : Nat) (v : Vertex L) (k : Nat) (r : Real)
    (z : Sample L) (e : Event L) : (resetSample L v k r z).2 e = z.2 e := rfl

theorem resetSample_generator_event_iff (L : Nat) (v : Vertex L) (k : Nat) (r : Real)
    (z : Sample L) (hf : r < ClockEventWord.eventTime z.1 (v,k))
    (e : Event L) (u : Real) (hu : u ≤ r) :
    (ClockEventWord.eventTime z.1 e ≤ u ↔
      ClockEventWord.eventTime (resetSample L v k r z).1 e ≤ u) :=
  reset_generator_event_iff v k r z.1 hf e.1 e.2 u hu

/-- All events in the original joint arrival/mark filtration are invariant;
no independent replacement filtration or future information is introduced. -/
theorem resetSample_history_event_iff (L : Nat) (v : Vertex L) (k : Nat) (r : Real)
    (z : Sample L) (hf : r < ClockEventWord.eventTime z.1 (v,k))
    (E : Set (Sample L)) (hE : MeasurableSet[MarkedClockFiltration.history L r] E) :
    z ∈ E ↔ resetSample L v k r z ∈ E :=
  MarkedClockFiltration.measurable_event_past_invariant L r z (resetSample L v k r z)
    (resetSample_generator_event_iff L v k r z hf) (fun _ _ => rfl) hE

theorem prior_future_marked_history_event_iff (L : Nat) (v : Vertex L) (k : Nat) (r : Real)
    (z : Sample L)
    (hp : r < ClockGapReset.prior v k (RandomThresholdSurvival.restCoordinates v k z.1))
    (E : Set (Sample L)) (hE : MeasurableSet[MarkedClockFiltration.history L r] E) :
    z ∈ E ↔ resetSample L v k r z ∈ E :=
  resetSample_history_event_iff L v k r z (hp.trans_le (prior_le_current v k z.1)) E hE

end MathResearchAnalysis.FutureGapHistory
