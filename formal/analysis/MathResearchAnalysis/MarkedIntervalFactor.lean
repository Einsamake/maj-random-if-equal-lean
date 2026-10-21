module
public import MathResearchAnalysis.StoppedMarkSlices
set_option autoImplicit false
/-! Fair-mark factorization for actual future identities under arbitrary
original joint-past events. The fixed identity is not necessarily the next
ring. The actual coordinate flip preserves the complete past while that
identity remains unrevealed. No future-law or compensation premise is used. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MarkedIntervalFactor
open MeasureTheory
open DropletClockLaw (Sample Event Vertex)
open UnrevealedMarkInvariance (flipSample)

/-- Any clock-only event that places this identity strictly after the past
cutoff can be combined with an arbitrary original joint-history event. -/
theorem clock_event_factor (L : Nat) (e : Event L) (s : Real)
    (E : Set (Sample L)) (hE : MeasurableSet[MarkedClockFiltration.history L s] E)
    (B : Set (ExponentialClocks.Sample (Vertex L))) (hB : MeasurableSet B)
    (hfuture : ∀ ω ∈ B, s < ClockEventWord.eventTime ω e) (b : Bool) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      (E ∩ {z : Sample L | z.1 ∈ B} ∩ {z | z.2 e = b}) =
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
        (E ∩ {z : Sample L | z.1 ∈ B}) * (2 : ENNReal)⁻¹ := by
  apply StoppedMarkSlices.fair_slice_factor L e _
    (((MarkedClockFiltration.history L).le s E hE).inter (hB.preimage measurable_fst))
  intro z
  change (z ∈ E ∧ z.1 ∈ B) ↔ (flipSample L e z ∈ E ∧ z.1 ∈ B)
  by_cases hz : z.1 ∈ B
  · simp only [hz, and_true]
    exact UnrevealedMarkInvariance.history_invariant L e (!(z.2 e)) z s
      (hfuture z.1 hz) E hE
  · simp only [hz, and_false]

/-- Future arrival windows inherit the fair factor even after conditioning
on any event in the actual joint arrival/revealed-mark history. -/
theorem window_event_factor (L : Nat) (e : Event L) (s t : Real)
    (E : Set (Sample L)) (hE : MeasurableSet[MarkedClockFiltration.history L s] E)
    (b : Bool) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      (E ∩ {z : Sample L | s < ClockEventWord.eventTime z.1 e ∧
        ClockEventWord.eventTime z.1 e ≤ t} ∩ {z | z.2 e = b}) =
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
        (E ∩ {z : Sample L | s < ClockEventWord.eventTime z.1 e ∧
          ClockEventWord.eventTime z.1 e ≤ t}) * (2 : ENNReal)⁻¹ := by
  exact clock_event_factor L e s E hE
    {ω | s < ClockEventWord.eventTime ω e ∧ ClockEventWord.eventTime ω e ≤ t}
    ((measurableSet_lt measurable_const (ClockEventWord.eventTime_measurable e)).inter
      (measurableSet_le (ClockEventWord.eventTime_measurable e) measurable_const))
    (fun _ h => h.1) b

/-- The same factorization in a single set-builder, for summing the actual
identity indicators. Marks are counted, not actual color changes. -/
theorem window_set_factor (L : Nat) (v : Vertex L) (k : Nat) (s t : Real)
    (E : Set (Sample L)) (hE : MeasurableSet[MarkedClockFiltration.history L s] E)
    (b : Bool) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z : Sample L | z ∈ E ∧ s < ClockEventWord.eventTime z.1 (v,k) ∧
        ClockEventWord.eventTime z.1 (v,k) ≤ t ∧ z.2 (v,k) = b} =
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
        {z : Sample L | z ∈ E ∧ s < ClockEventWord.eventTime z.1 (v,k) ∧
          ClockEventWord.eventTime z.1 (v,k) ≤ t} * (2 : ENNReal)⁻¹ := by
  have ha : E ∩ {z : Sample L | s < ClockEventWord.eventTime z.1 (v,k) ∧
        ClockEventWord.eventTime z.1 (v,k) ≤ t} ∩ {z | z.2 (v,k) = b} =
      {z : Sample L | z ∈ E ∧ s < ClockEventWord.eventTime z.1 (v,k) ∧
        ClockEventWord.eventTime z.1 (v,k) ≤ t ∧ z.2 (v,k) = b} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]
  have hc : E ∩ {z : Sample L | s < ClockEventWord.eventTime z.1 (v,k) ∧
        ClockEventWord.eventTime z.1 (v,k) ≤ t} =
      {z : Sample L | z ∈ E ∧ s < ClockEventWord.eventTime z.1 (v,k) ∧
        ClockEventWord.eventTime z.1 (v,k) ≤ t} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  have h := window_event_factor L (v,k) s t E hE b
  rwa [ha, hc] at h
end MathResearchAnalysis.MarkedIntervalFactor
