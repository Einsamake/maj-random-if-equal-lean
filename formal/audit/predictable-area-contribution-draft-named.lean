module
public import MathResearchAnalysis.ActualPreState
public import MathResearchAnalysis.MarkedPredictableCompensation
set_option autoImplicit false
/-! The genuine area change caused by one marked clock ring. The area always
means missing sites inside `D`, so its bound does not require the initial state
to lie in `D`. Positive and negative changes are compensated separately,
retaining extended nonnegative sums. This does not assert a signed pathwise
telescope, a total-area Dynkin identity, or a geometric drift bound. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.PredictableAreaContribution
open MeasureTheory
open DropletClockLaw (Sample Vertex)
open InfiniteGridModel (Site)

/-- The missing-area change for this site's specified mark at the actual
predictable state immediately before time. -/
def increment (L : Nat) (D I S : Finset Site) (v : Vertex L) (b : Bool)
    (p : NNReal × Sample L) : Real :=
  ((D \ DropletStoppedWord.stoppedStep D I
      (ObservedPreState.beforeState L D I S p.1 p.2)
      (ClippedSquareCoordinates.recenter L v,b)).card : Real) -
    ((D \ ObservedPreState.beforeState L D I S p.1 p.2).card : Real)

/-- Positive part of the actual single-ring area increment. -/
def gain (L : Nat) (D I S : Finset Site) (v : Vertex L) (b : Bool)
    (p : NNReal × Sample L) : ENNReal := ENNReal.ofReal (increment L D I S v b p)

/-- Negative part, stored nonnegatively rather than subtracting infinities. -/
def loss (L : Nat) (D I S : Finset Site) (v : Vertex L) (b : Bool)
    (p : NNReal × Sample L) : ENNReal := ENNReal.ofReal (-increment L D I S v b p)

theorem increment_measurable (L : Nat) (D I S : Finset Site) (v : Vertex L) (b : Bool) :
    Measurable[(RationalProtectedExit.nnHistory L).predictable] (increment L D I S v b) :=
  ObservedPreState.observable_measurable L D I S (fun U : Finset Site =>
    ((D \ DropletStoppedWord.stoppedStep D I U
      (ClippedSquareCoordinates.recenter L v,b)).card : Real) - ((D \ U).card : Real))

theorem increment_stronglyMeasurable (L : Nat) (D I S : Finset Site)
    (v : Vertex L) (b : Bool) :
    StronglyMeasurable[(RationalProtectedExit.nnHistory L).predictable]
      (increment L D I S v b) := (increment_measurable L D I S v b).stronglyMeasurable

/-- Both areas belong to `[0,D.card]`, even for an arbitrary initial `S`. -/
theorem increment_norm_le (L : Nat) (D I S : Finset Site)
    (v : Vertex L) (b : Bool) (p : NNReal × Sample L) :
    ‖increment L D I S v b p‖ ≤ (D.card : Real) := by
  let U := ObservedPreState.beforeState L D I S p.1 p.2
  let W := DropletStoppedWord.stoppedStep D I U (ClippedSquareCoordinates.recenter L v,b)
  have hU0 : (0 : Real) ≤ ((D \ U).card : Real) := Nat.cast_nonneg _
  have hW0 : (0 : Real) ≤ ((D \ W).card : Real) := Nat.cast_nonneg _
  have hUD : ((D \ U).card : Real) ≤ (D.card : Real) :=
    Nat.cast_le.mpr (Finset.card_le_card Finset.sdiff_subset)
  have hWD : ((D \ W).card : Real) ≤ (D.card : Real) :=
    Nat.cast_le.mpr (Finset.card_le_card Finset.sdiff_subset)
  rw [Real.norm_eq_abs]
  change |((D \ W).card : Real) - ((D \ U).card : Real)| ≤ (D.card : Real)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem gain_measurable (L : Nat) (D I S : Finset Site) (v : Vertex L) (b : Bool) :
    Measurable[(RationalProtectedExit.nnHistory L).predictable] (gain L D I S v b) :=
  (increment_measurable L D I S v b).ennreal_ofReal

theorem loss_measurable (L : Nat) (D I S : Finset Site) (v : Vertex L) (b : Bool) :
    Measurable[(RationalProtectedExit.nnHistory L).predictable] (loss L D I S v b) :=
  (increment_measurable L D I S v b).neg.ennreal_ofReal

/-- Positive area changes summed over genuine marked arrivals have the actual
rate-one-half time integral; no compensation assertion is an input. -/
theorem gain_compensation (L : Nat) (D I S : Finset Site)
    (v : Vertex L) (b : Bool) (T : NNReal) :
    (∫⁻ z : Sample L, ∑' k : Nat, (MarkedClockPointMeasure.window L v b T k).indicator
      (fun z => gain L D I S v b (MarkedClockPointMeasure.point L v k z)) z
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    (2 : ENNReal)⁻¹ * ∫⁻ u : Real in Set.Ioc 0 (T : Real),
      ∫⁻ z : Sample L, gain L D I S v b (u.toNNReal,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) :=
  MarkedPredictableCompensation.pathwise_lintegral_eq_time L v b T
    (gain L D I S v b) (gain_measurable L D I S v b)

theorem loss_compensation (L : Nat) (D I S : Finset Site)
    (v : Vertex L) (b : Bool) (T : NNReal) :
    (∫⁻ z : Sample L, ∑' k : Nat, (MarkedClockPointMeasure.window L v b T k).indicator
      (fun z => loss L D I S v b (MarkedClockPointMeasure.point L v k z)) z
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    (2 : ENNReal)⁻¹ * ∫⁻ u : Real in Set.Ioc 0 (T : Real),
      ∫⁻ z : Sample L, loss L D I S v b (u.toNNReal,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) :=
  MarkedPredictableCompensation.pathwise_lintegral_eq_time L v b T
    (loss L D I S v b) (loss_measurable L D I S v b)

theorem increment_integrable_point (L : Nat) (D I S : Finset Site)
    (v : Vertex L) (b : Bool) (T : NNReal) :
    Integrable (increment L D I S v b) (MarkedClockPointMeasure.measure L v b T) :=
  MarkedPredictableCompensation.integrable_point_of_bounded L v b T
    (increment L D I S v b) (increment_stronglyMeasurable L D I S v b)
    (D.card : Real) (increment_norm_le L D I S v b)

theorem increment_integrable_reference (L : Nat) (D I S : Finset Site)
    (v : Vertex L) (b : Bool) (T : NNReal) :
    Integrable (increment L D I S v b) (PredictableClockReference.reference L T) :=
  MarkedPredictableCompensation.integrable_reference_of_bounded L v b T
    (increment L D I S v b) (increment_stronglyMeasurable L D I S v b)
    (D.card : Real) (increment_norm_le L D I S v b)

/-- On one common set of original samples, all marked event contributions
are the differences between the actual post-event and strict pre-event area.
Thus the predictable hypothetical mark is the real mark on every matching
window, including the event at which the first-loss freeze occurs. -/
theorem event_increment_ae (L : Nat) (D I S : Finset Site)
    (v : Vertex L) (b : Bool) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ k : Nat,
      z.2 (v,k) = b → increment L D I S v b (MarkedClockPointMeasure.point L v k z) =
        ((D \ DropletStoppedClockLaw.stateAt L D I S
          (ClockEventWord.eventTime z.1 (v,k)) z).card : Real) -
        ((D \ ActualPreState.strictStateAt L D I S
          (ClockEventWord.eventTime z.1 (v,k)) z).card : Real) := by
  filter_upwards [ActualPreState.beforeState_all_times_ae L D I S,
    ActualPreState.stateAt_all_events_update_ae L D I S,
    ActualPreState.marked_all_events_positive_ae L] with z hbefore hpost hpos
  intro k hb
  have hpre := hbefore (ClockEventWord.eventTime z.1 (v,k)).toNNReal
  rw [Real.coe_toNNReal _ (hpos (v,k)).le] at hpre
  have hjump := hpost (v,k)
  rw [hb] at hjump
  unfold increment MarkedClockPointMeasure.point
  rw [← hjump,hpre]

theorem event_gain_ae (L : Nat) (D I S : Finset Site)
    (v : Vertex L) (b : Bool) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ k : Nat,
      z.2 (v,k) = b → gain L D I S v b (MarkedClockPointMeasure.point L v k z) =
        ENNReal.ofReal (((D \ DropletStoppedClockLaw.stateAt L D I S
          (ClockEventWord.eventTime z.1 (v,k)) z).card : Real) -
        ((D \ ActualPreState.strictStateAt L D I S
          (ClockEventWord.eventTime z.1 (v,k)) z).card : Real)) := by
  filter_upwards [event_increment_ae L D I S v b] with z hz
  intro k hb
  exact congrArg ENNReal.ofReal (hz k hb)

theorem event_loss_ae (L : Nat) (D I S : Finset Site)
    (v : Vertex L) (b : Bool) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ k : Nat,
      z.2 (v,k) = b → loss L D I S v b (MarkedClockPointMeasure.point L v k z) =
        ENNReal.ofReal (-(((D \ DropletStoppedClockLaw.stateAt L D I S
          (ClockEventWord.eventTime z.1 (v,k)) z).card : Real) -
        ((D \ ActualPreState.strictStateAt L D I S
          (ClockEventWord.eventTime z.1 (v,k)) z).card : Real))) := by
  filter_upwards [event_increment_ae L D I S v b] with z hz
  intro k hb
  exact congrArg (fun x : Real => ENNReal.ofReal (-x)) (hz k hb)
end MathResearchAnalysis.PredictableAreaContribution

#print axioms MathResearchAnalysis.PredictableAreaContribution.increment
#print axioms MathResearchAnalysis.PredictableAreaContribution.gain
#print axioms MathResearchAnalysis.PredictableAreaContribution.loss
#print axioms MathResearchAnalysis.PredictableAreaContribution.increment_measurable
#print axioms MathResearchAnalysis.PredictableAreaContribution.increment_stronglyMeasurable
#print axioms MathResearchAnalysis.PredictableAreaContribution.increment_norm_le
#print axioms MathResearchAnalysis.PredictableAreaContribution.gain_measurable
#print axioms MathResearchAnalysis.PredictableAreaContribution.loss_measurable
#print axioms MathResearchAnalysis.PredictableAreaContribution.gain_compensation
#print axioms MathResearchAnalysis.PredictableAreaContribution.loss_compensation
#print axioms MathResearchAnalysis.PredictableAreaContribution.increment_integrable_point
#print axioms MathResearchAnalysis.PredictableAreaContribution.increment_integrable_reference
#print axioms MathResearchAnalysis.PredictableAreaContribution.event_increment_ae
#print axioms MathResearchAnalysis.PredictableAreaContribution.event_gain_ae
#print axioms MathResearchAnalysis.PredictableAreaContribution.event_loss_ae
