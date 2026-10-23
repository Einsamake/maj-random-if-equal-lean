module
public import MathResearchAnalysis.ObservedPreState
public import MathResearchAnalysis.StrictClockPrefix
set_option autoImplicit false
/-! The predictable representative equals the real strictly-before frozen state
on one common full-measure set, simultaneously at every nonnegative time.
The eventwise jump uses the original identity mark and existing frozen step. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.ActualPreState
open MeasureTheory
open DropletClockLaw (Sample Event)
open InfiniteGridModel (Site)

def strictStateAt (L : Nat) (D I S : Finset Site) (t : Real) (z : Sample L) : Finset Site :=
  DropletStoppedWord.stoppedWord D I S
    (DropletClockLaw.markedEvents L (StrictClockPrefix.strictWord z.1 t) z.2)

theorem marked_all_events_positive_ae (L : Nat) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e :=
  (Measure.quasiMeasurePreserving_fst
    (μ := ExponentialClocks.clockMeasure (DropletClockLaw.Vertex L))
    (ν := FairMarks.markMeasure (Event L))).ae
      (ClockEventWord.eventTime_positive_ae (V := DropletClockLaw.Vertex L))

theorem strictStateAt_zero (L : Nat) (D I S : Finset Site) (z : Sample L)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) :
    strictStateAt L D I S 0 z = S := by
  simp only [strictStateAt,StrictClockPrefix.strictWord_zero_of_positive z.1 hp,
    DropletClockLaw.markedEvents,List.reverse_nil,List.map_nil,DropletStoppedWord.stoppedWord_nil]

theorem beforeState_eq_strictStateAt_pos (L : Nat) (D I S : Finset Site) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t) (t : NNReal) (ht : 0 < t) :
    ObservedPreState.beforeState L D I S t z = strictStateAt L D I S (t : Real) z := by
  obtain ⟨a,ha0,hat,hgap⟩ := StrictClockPrefix.word_left_locally_strict z.1 (t : Real)
    (hg (t : Real)) (by exact_mod_cast ht)
  obtain ⟨q,haq,hqt⟩ := exists_rat_btwn hat
  apply ObservedPreState.state_eq_of_graph L D I S t z _
  refine ⟨q,?_,hqt,?_⟩
  · exact_mod_cast (ha0.trans haq.le)
  · intro r hqr hrt
    rw [ObservedFrozenProcess.state_eq_stateAt L D I S (r : Real) z (hg _)]
    unfold DropletStoppedClockLaw.stateAt strictStateAt
    rw [hgap (r : Real) (haq.trans (by exact_mod_cast hqr)) hrt]

theorem beforeState_eq_strictStateAt (L : Nat) (D I S : Finset Site) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) (t : NNReal) :
    ObservedPreState.beforeState L D I S t z = strictStateAt L D I S (t : Real) z := by
  by_cases ht : t = 0
  · subst t
    rw [ObservedPreState.state_zero]
    exact (strictStateAt_zero L D I S z hp).symm
  · exact beforeState_eq_strictStateAt_pos L D I S z hg t (lt_of_le_of_ne bot_le (Ne.symm ht))

/-- A single common set of original samples, not a separate exceptional set for
individual times. It can therefore be used at a random ringing time. -/
theorem beforeState_all_times_ae (L : Nat) (D I S : Finset Site) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ t : NNReal,
      ObservedPreState.beforeState L D I S t z = strictStateAt L D I S (t : Real) z := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L,
    marked_all_events_positive_ae L] with z hg hp
  exact fun t => beforeState_eq_strictStateAt L D I S z hg hp t

theorem strictStateAt_event_update (L : Nat) (D I S : Finset Site) (z : Sample L)
    (e : Event L) (hg : ClockEventWord.Good z.1 (ClockEventWord.eventTime z.1 e)) :
    DropletStoppedClockLaw.stateAt L D I S (ClockEventWord.eventTime z.1 e) z =
      DropletStoppedWord.stoppedStep D I
        (strictStateAt L D I S (ClockEventWord.eventTime z.1 e) z)
        (ClippedSquareCoordinates.recenter L e.1,z.2 e) := by
  unfold DropletStoppedClockLaw.stateAt
  rw [StrictClockPrefix.word_at_event_eq_cons_strict z.1 e hg]
  simp only [DropletClockLaw.markedEvents,List.reverse_cons,List.map_append,List.map_singleton,
    DropletStoppedWord.stoppedWord_append,DropletStoppedWord.stoppedWord_cons,
    DropletStoppedWord.stoppedWord_nil]
  rfl

theorem stateAt_event_update (L : Nat) (D I S : Finset Site) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) (e : Event L) :
    DropletStoppedClockLaw.stateAt L D I S (ClockEventWord.eventTime z.1 e) z =
      DropletStoppedWord.stoppedStep D I
        (ObservedPreState.beforeState L D I S (ClockEventWord.eventTime z.1 e).toNNReal z)
        (ClippedSquareCoordinates.recenter L e.1,z.2 e) := by
  rw [beforeState_eq_strictStateAt L D I S z hg hp,
    Real.coe_toNNReal _ (hp e).le]
  exact strictStateAt_event_update L D I S z e (hg _)

theorem stateAt_all_events_update_ae (L : Nat) (D I S : Finset Site) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ e : Event L,
      DropletStoppedClockLaw.stateAt L D I S (ClockEventWord.eventTime z.1 e) z =
        DropletStoppedWord.stoppedStep D I
          (ObservedPreState.beforeState L D I S (ClockEventWord.eventTime z.1 e).toNNReal z)
          (ClippedSquareCoordinates.recenter L e.1,z.2 e) := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L,
    marked_all_events_positive_ae L] with z hg hp
  exact fun e => stateAt_event_update L D I S z hg hp e

theorem observedState_all_events_update_ae (L : Nat) (D I S : Finset Site) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ e : Event L,
      ObservedFrozenProcess.state L D I S (ClockEventWord.eventTime z.1 e) z =
        DropletStoppedWord.stoppedStep D I
          (ObservedPreState.beforeState L D I S (ClockEventWord.eventTime z.1 e).toNNReal z)
          (ClippedSquareCoordinates.recenter L e.1,z.2 e) := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L,
    stateAt_all_events_update_ae L D I S] with z hg he
  intro e
  rw [ObservedFrozenProcess.state_eq_stateAt L D I S _ z (hg _)]
  exact he e
end MathResearchAnalysis.ActualPreState
