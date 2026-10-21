module
public import MathResearchAnalysis.ClockRingMean
set_option autoImplicit false
/-! Exact means of the actual color-marked ring counts. The independent
fair mark at each fixed event identity is integrated under the original
clock/mark product measure. Counts retain infinity on exceptional samples.
No conditional-increment or predictable-compensation statement is asserted. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MarkedRingMean
open MeasureTheory ProbabilityTheory Set
open DropletClockLaw (Sample Event Vertex)

/-- A fixed arrival event and its fair coordinate mark have their actual product mass. -/
theorem arrival_mark_event_measure (L : Nat) (v : Vertex L) (k : Nat) (b : Bool) (t : Real) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z : Sample L | ClockEventWord.eventTime z.1 (v,k) ≤ t ∧ z.2 (v,k) = b} =
      ExponentialClocks.clockMeasure (Vertex L)
        {ω | ClockEventWord.eventTime ω (v,k) ≤ t} * (2 : ENNReal)⁻¹ := by
  have heq : {z : Sample L | ClockEventWord.eventTime z.1 (v,k) ≤ t ∧ z.2 (v,k) = b} =
      {ω : ExponentialClocks.Sample (Vertex L) | ClockEventWord.eventTime ω (v,k) ≤ t} ×ˢ
        {η : FairMarks.Sample (Event L) | η (v,k) = b} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_prod]
  have hm : FairMarks.markMeasure (Event L) {η | η (v,k) = b} = FairMarks.fair {b} :=
    (FairMarks.mark_hasLaw (v,k)).measure_eq (p := fun c => c = b) (measurableSet_singleton b)
  change (ExponentialClocks.clockMeasure (Vertex L)).prod (FairMarks.markMeasure (Event L)) _ = _
  rw [heq, Measure.prod_prod, hm, FairMarks.fair_singleton b]

/-- The mean of either color-marked count is half the total mean, as an ENNReal identity. -/
theorem lintegral_markedCount_eq_half_count (L : Nat) (v : Vertex L) (b : Bool) (t : Real) :
    (∫⁻ z : Sample L, MarkedRingCount.markedCount L v b t z
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      (∫⁻ z : Sample L, MarkedRingCount.count L v t z
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) * (2 : ENNReal)⁻¹ := by
  rw [MarkedRingCount.lintegral_markedCount_eq_tsum, MarkedRingCount.lintegral_count_eq_clock_tsum]
  calc
    _ = ∑' k : Nat, ExponentialClocks.clockMeasure (Vertex L)
        {ω | ClockEventWord.eventTime ω (v,k) ≤ t} * (2 : ENNReal)⁻¹ :=
      tsum_congr (fun k => arrival_mark_event_measure L v k b t)
    _ = _ := ENNReal.tsum_mul_right

/-- At a finite nonnegative time, the expected count of either fair mark is t/2. -/
theorem lintegral_markedCount_eq_time (L : Nat) (v : Vertex L) (b : Bool)
    (t : Real) (ht : 0 ≤ t) :
    (∫⁻ z : Sample L, MarkedRingCount.markedCount L v b t z
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) = ENNReal.ofReal (t/2) := by
  rw [lintegral_markedCount_eq_half_count, ClockRingMean.lintegral_count_eq_time L v t ht,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real) < 2)]
  norm_num [div_eq_mul_inv]

/-- The real integral is obtained only after the actual marked count is known a.e. finite. -/
theorem integral_markedCount_eq_time (L : Nat) (v : Vertex L) (b : Bool)
    (t : Real) (ht : 0 ≤ t) :
    (∫ z : Sample L, (MarkedRingCount.markedCount L v b t z).toReal
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) = t/2 := by
  rw [integral_toReal (MarkedRingCount.markedCount_measurable L v b t).aemeasurable
    ((MarkedRingCount.markedCount_finite_ae L).mono (fun z hz => (hz v b t).lt_top)),
    lintegral_markedCount_eq_time L v b t ht, ENNReal.toReal_ofReal (by positivity : 0 ≤ t/2)]

end MathResearchAnalysis.MarkedRingMean

