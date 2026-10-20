module
public import MathResearchAnalysis.MarkedDeterministicResidual
set_option autoImplicit false
/-! Genuine stopped residual law in the original marked joint history. The stopping time may depend on revealed marks. Its fixed-mark sections are actual clock stopping times; the actual product measure transports the proved clock law. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MarkedStoppedResidual
open MeasureTheory ProbabilityTheory
open DropletClockLaw (Sample Event Vertex)

theorem fixed_marks_full_history_measurable (L : Nat) (η : Event L → Bool) :
    @Measurable (ExponentialClocks.Sample (Vertex L)) (Sample L)
      (⨆ t : Real, ArrivalFiltration.clockHistory (Vertex L) t)
      (⨆ t : Real, MarkedClockFiltration.history L t) (fun ω => (ω,η)) := by
  apply Measurable.of_le_map
  apply iSup_le
  intro t
  exact ((MarkedDeterministicResidual.fixed_marks_measurable L t η).mono
    (le_iSup (ArrivalFiltration.clockHistory (Vertex L)) t) le_rfl).le_map

theorem section_isStoppingTime (L : Nat) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) (η : Event L → Bool) :
    IsStoppingTime (ArrivalFiltration.clockHistory (Vertex L)) (fun ω => R (ω,η)) := by
  intro t
  exact MarkedDeterministicResidual.history_section_measurable L t η {z | R z ≤ t} (hR t)

theorem stopped_history_section_measurable (L : Nat) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) (η : Event L → Bool)
    (E : Set (Sample L)) (hE : MeasurableSet[hR.measurableSpace] E) :
    MeasurableSet[(section_isStoppingTime L R hR η).measurableSpace] ((fun ω => (ω,η)) ⁻¹' E) := by
  rcases (hR.measurableSet E).mp hE with ⟨hEa,hEt⟩
  apply ((section_isStoppingTime L R hR η).measurableSet _).mpr
  refine ⟨hEa.preimage (fixed_marks_full_history_measurable L η),?_⟩
  intro t
  exact MarkedDeterministicResidual.history_section_measurable L t η (E ∩ {z | R z ≤ t}) (hEt t)

def waiting (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real) : Sample L → Real :=
  ClockWaitingLimit.waiting (fun k z => ArrivalFiltration.chronologicalArrival v k z.1) R

theorem waiting_measurable (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) : Measurable (waiting L v R) := by
  have hC := ExtendedNextRing.after_isStoppingTime (MarkedClockFiltration.history L)
    (fun k z => ArrivalFiltration.chronologicalArrival v k z.1) R
    (fun z => ArrivalFiltration.chronologicalArrival_monotone v z.1) hR
    (fun k => MarkedClockFiltration.arrival_isStoppingTime L (v,k))
  exact ((hC.measurable'.untopD 0).sub (hR.measurable'.untopD 0)).max measurable_const

theorem waiting_nonnegative (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real) (z : Sample L) :
    0 ≤ waiting L v R z := le_max_right _ _

theorem waiting_jointSurvival (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) (hpos : ∀ z, 0 ≤ R z)
    (hfinite : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), R z ≠ ⊤) :
    @SurvivalLaw.JointSurvival (Sample L) inferInstance (waiting L v R) hR.measurableSpace
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  intro t ht E hE
  have hEa : MeasurableSet E := hR.measurableSpace_le E hE
  have hsurv : MeasurableSet (E ∩ {z : Sample L | t < waiting L v R z}) :=
    hEa.inter (measurableSet_lt measurable_const (waiting_measurable L v R hR))
  have hfinsections : ∀ᵐ η ∂FairMarks.markMeasure (Event L),
      ∀ᵐ ω ∂ExponentialClocks.clockMeasure (Vertex L), R (ω,η) ≠ ⊤ := by
    apply (Measure.ae_ae_comm (hR.measurableSet_eq_top.compl)).mp
    exact Measure.ae_ae_of_ae_prod hfinite
  change (ExponentialClocks.clockMeasure (Vertex L)).prod (FairMarks.markMeasure (Event L)) _ = _
  rw [Measure.prod_apply_symm hsurv]
  change _ = ENNReal.ofReal (Real.exp (-t)) *
    (ExponentialClocks.clockMeasure (Vertex L)).prod (FairMarks.markMeasure (Event L)) E
  rw [Measure.prod_apply_symm hEa]
  calc
    _ = ∫⁻ η, ENNReal.ofReal (Real.exp (-t)) *
        ExponentialClocks.clockMeasure (Vertex L) ((fun ω => (ω,η)) ⁻¹' E)
        ∂FairMarks.markMeasure (Event L) := by
      apply lintegral_congr_ae
      filter_upwards [hfinsections] with η hη
      exact ClockStoppedResidual.clock_wait_jointSurvival v (fun ω => R (ω,η))
        (section_isStoppingTime L R hR η) (fun ω => hpos (ω,η)) hη t ht
        ((fun ω => (ω,η)) ⁻¹' E) (stopped_history_section_measurable L R hR η E hE)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem waiting_hasLaw (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) (hpos : ∀ z, 0 ≤ R z)
    (hfinite : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), R z ≠ ⊤) :
    HasLaw (waiting L v R) (expMeasure 1) (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  SurvivalLaw.hasLaw_of_jointSurvival (waiting_measurable L v R hR) (waiting_nonnegative L v R)
    hR.measurableSpace_le (waiting_jointSurvival L v R hR hpos hfinite)

theorem waiting_independent_stopped_history (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) (hpos : ∀ z, 0 ≤ R z)
    (hfinite : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), R z ≠ ⊤) :
    Indep ((borel Real).comap (waiting L v R)) hR.measurableSpace
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  SurvivalLaw.indep_of_jointSurvival (waiting_measurable L v R hR) (waiting_nonnegative L v R)
    hR.measurableSpace_le (waiting_jointSurvival L v R hR hpos hfinite)
end MathResearchAnalysis.MarkedStoppedResidual
