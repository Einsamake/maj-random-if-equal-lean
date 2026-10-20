module
public import MathResearchAnalysis.MarkedClockFiltration
public import MathResearchAnalysis.ClockStoppedResidual
set_option autoImplicit false
/-! Actual deterministic residual waiting with the joint arrival/revealed-mark history. Fixed-mark sections reduce to the already proved common clock history law; Fubini transports it through the genuine independent mark product. No right-continuation or marked-stopping-time law is assumed. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MarkedDeterministicResidual
open MeasureTheory ProbabilityTheory
open DropletClockLaw (Sample Event Vertex)

theorem fixed_marks_measurable (L : Nat) (r : Real) (η : Event L → Bool) :
    @Measurable (ExponentialClocks.Sample (Vertex L)) (Sample L)
      (ArrivalFiltration.clockHistory (Vertex L) r) (MarkedClockFiltration.history L r)
      (fun ω => (ω,η)) := by
  let : MeasurableSpace (ExponentialClocks.Sample (Vertex L)) := ArrivalFiltration.clockHistory (Vertex L) r
  apply measurable_generateFrom
  rintro B ⟨e,u,hu,hB⟩
  rcases hB with rfl | ⟨b,rfl⟩
  · exact ArrivalFiltration.arrival_event_measurable ArrivalFiltration.chronologicalArrival
      ArrivalFiltration.chronologicalArrival_measurable e.1 e.2 hu
  · change MeasurableSet {ω : ExponentialClocks.Sample (Vertex L) |
      ClockEventWord.eventTime ω e ≤ u ∧ η e = b}
    exact (ArrivalFiltration.arrival_event_measurable ArrivalFiltration.chronologicalArrival
      ArrivalFiltration.chronologicalArrival_measurable e.1 e.2 hu).inter (MeasurableSet.const _)

theorem history_section_measurable (L : Nat) (r : Real) (η : Event L → Bool)
    (E : Set (Sample L)) (hE : MeasurableSet[MarkedClockFiltration.history L r] E) :
    MeasurableSet[ArrivalFiltration.clockHistory (Vertex L) r] ((fun ω => (ω,η)) ⁻¹' E) :=
  hE.preimage (fixed_marks_measurable L r η)

def waiting (L : Nat) (v : Vertex L) (r : Real) (z : Sample L) : Real :=
  ClockWaitingLimit.waiting (ArrivalFiltration.chronologicalArrival v) (fun _ => (r : WithTop Real)) z.1

theorem waiting_measurable (L : Nat) (v : Vertex L) (r : Real) : Measurable (waiting L v r) :=
  (CountableClockSurvival.clock_waiting_measurable v (fun _ => (r : WithTop Real))
    (isStoppingTime_const (ArrivalFiltration.clockHistory (Vertex L)) r)).comp measurable_fst

theorem waiting_nonnegative (L : Nat) (v : Vertex L) (r : Real) (z : Sample L) :
    0 ≤ waiting L v r z := le_max_right _ _

theorem waiting_jointSurvival (L : Nat) (v : Vertex L) (r : Real) (hr : 0 ≤ r) :
    @SurvivalLaw.JointSurvival (Sample L) inferInstance (waiting L v r)
      (MarkedClockFiltration.history L r) (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  intro t ht E hE
  have hEa : MeasurableSet E := (MarkedClockFiltration.history L).le r E hE
  have hsurv : MeasurableSet (E ∩ {z : Sample L | t < waiting L v r z}) :=
    hEa.inter (measurableSet_lt measurable_const (waiting_measurable L v r))
  change (ExponentialClocks.clockMeasure (Vertex L)).prod (FairMarks.markMeasure (Event L)) _ = _
  rw [Measure.prod_apply_symm hsurv]
  change _ = ENNReal.ofReal (Real.exp (-t)) *
    (ExponentialClocks.clockMeasure (Vertex L)).prod (FairMarks.markMeasure (Event L)) E
  rw [Measure.prod_apply_symm hEa]
  calc
    _ = ∫⁻ η, ENNReal.ofReal (Real.exp (-t)) *
        ExponentialClocks.clockMeasure (Vertex L) ((fun ω => (ω,η)) ⁻¹' E)
        ∂FairMarks.markMeasure (Event L) := by
      apply lintegral_congr
      intro η
      exact ClockStoppedResidual.clock_wait_jointSurvival v (fun _ => (r : WithTop Real))
        (isStoppingTime_const (ArrivalFiltration.clockHistory (Vertex L)) r)
        (fun _ => by exact_mod_cast hr) (Filter.Eventually.of_forall (fun _ => WithTop.coe_ne_top))
        t ht ((fun ω => (ω,η)) ⁻¹' E) (((isStoppingTime_const (ArrivalFiltration.clockHistory (Vertex L)) r).le_measurableSpace_of_const_le
          (i := r) (fun _ => le_rfl)) _ (history_section_measurable L r η E hE))
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem waiting_hasLaw (L : Nat) (v : Vertex L) (r : Real) (hr : 0 ≤ r) :
    HasLaw (waiting L v r) (expMeasure 1) (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  SurvivalLaw.hasLaw_of_jointSurvival (waiting_measurable L v r) (waiting_nonnegative L v r)
    ((MarkedClockFiltration.history L).le r) (waiting_jointSurvival L v r hr)

theorem waiting_independent_history (L : Nat) (v : Vertex L) (r : Real) (hr : 0 ≤ r) :
    Indep ((borel Real).comap (waiting L v r)) (MarkedClockFiltration.history L r)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  SurvivalLaw.indep_of_jointSurvival (waiting_measurable L v r) (waiting_nonnegative L v r)
    ((MarkedClockFiltration.history L).le r) (waiting_jointSurvival L v r hr)
end MathResearchAnalysis.MarkedDeterministicResidual
