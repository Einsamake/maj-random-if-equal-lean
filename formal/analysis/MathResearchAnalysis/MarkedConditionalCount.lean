module
public import MathResearchAnalysis.ClockIntervalHistory
public import MathResearchAnalysis.ClockIntervalCount
public import MathResearchAnalysis.MarkedIntervalFactor
public import MathResearchAnalysis.MarkedDeterministicResidual
set_option autoImplicit false
/-! Conditional means of actual interval counts in the original joint history.
The clock-history identity is transported by fixed-mark sections under the true
product law, and actual gap occupation is summed. Counts retain infinity;
real differences are identified only after actual a.e. finiteness. No Poisson,
compensation, Dynkin or recovery-time bound is an input. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MarkedConditionalCount
open MeasureTheory Set
open DropletClockLaw (Sample Event Vertex)

theorem gap_increment_lintegral_on_history (L : Nat) (v : Vertex L) (k : Nat)
    (s t : Real) (hst : s ≤ t) (E : Set (Sample L))
    (hE : MeasurableSet[MarkedClockFiltration.history L s] E) :
    (∫⁻ z in E, ENNReal.ofReal
      (ClockGapOccupation.exposure v k t z.1 - ClockGapOccupation.exposure v k s z.1)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
        (E ∩ {z | s < ClockEventWord.eventTime z.1 (v,k) ∧
          ClockEventWord.eventTime z.1 (v,k) ≤ t}) := by
  have hEa : MeasurableSet E := (MarkedClockFiltration.history L).le s E hE
  have hw : MeasurableSet {z : Sample L | s < ClockEventWord.eventTime z.1 (v,k) ∧
      ClockEventWord.eventTime z.1 (v,k) ≤ t} :=
    (measurableSet_lt measurable_const (MarkedClockFiltration.arrival_measurable L (v,k))).inter
      (measurableSet_le (MarkedClockFiltration.arrival_measurable L (v,k)) measurable_const)
  have hf : Measurable (fun z : Sample L => ENNReal.ofReal
      (ClockGapOccupation.exposure v k t z.1 - ClockGapOccupation.exposure v k s z.1)) :=
    ((ClockIntervalCount.exposure_increment_measurable v k s t).comp measurable_fst).ennreal_ofReal
  rw [← lintegral_indicator hEa]
  change (∫⁻ z : Sample L, E.indicator (fun z => ENNReal.ofReal
    (ClockGapOccupation.exposure v k t z.1 - ClockGapOccupation.exposure v k s z.1)) z
    ∂(ExponentialClocks.clockMeasure (Vertex L)).prod (FairMarks.markMeasure (Event L))) = _
  rw [lintegral_prod_symm _ (hf.indicator hEa).aemeasurable]
  change _ = (ExponentialClocks.clockMeasure (Vertex L)).prod (FairMarks.markMeasure (Event L)) _
  rw [Measure.prod_apply_symm (hEa.inter hw)]
  apply lintegral_congr
  intro η
  have hsection := MarkedDeterministicResidual.history_section_measurable L s η E hE
  have hsectiona := (ArrivalFiltration.clockHistory (Vertex L)).le s _ hsection
  change (∫⁻ ω : ExponentialClocks.Sample (Vertex L),
      ((fun ω => (ω,η)) ⁻¹' E).indicator (fun ω => ENNReal.ofReal
        (ClockGapOccupation.exposure v k t ω - ClockGapOccupation.exposure v k s ω)) ω
      ∂ExponentialClocks.clockMeasure (Vertex L)) =
    ExponentialClocks.clockMeasure (Vertex L)
      (((fun ω => (ω,η)) ⁻¹' E) ∩ {ω | s < ArrivalFiltration.chronologicalArrival v k ω ∧
        ArrivalFiltration.chronologicalArrival v k ω ≤ t})
  rw [lintegral_indicator hsectiona]
  exact ClockIntervalHistory.gap_increment_lintegral_on_history v k s t hst _ hsection

theorem count_lintegral_on_history (L : Nat) (v : Vertex L) (s t : Real)
    (hs : 0 ≤ s) (hst : s ≤ t) (E : Set (Sample L))
    (hE : MeasurableSet[MarkedClockFiltration.history L s] E) :
    (∫⁻ z in E, ClockIntervalCount.count L v s t z
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      ENNReal.ofReal (t-s) * ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) E := by
  rw [ClockIntervalCount.lintegral_count_eq_tsum_restrict]
  calc
    _ = ∑' k : Nat, ∫⁻ z in E, ENNReal.ofReal
        (ClockGapOccupation.exposure v k t z.1 - ClockGapOccupation.exposure v k s z.1)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) :=
      tsum_congr (fun k => (gap_increment_lintegral_on_history L v k s t hst E hE).symm)
    _ = ∫⁻ z in E, ∑' k : Nat, ENNReal.ofReal
        (ClockGapOccupation.exposure v k t z.1 - ClockGapOccupation.exposure v k s z.1)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) :=
      (lintegral_tsum (fun k =>
        (((ClockIntervalCount.exposure_increment_measurable v k s t).comp
          measurable_fst).ennreal_ofReal).aemeasurable)).symm
    _ = ∫⁻ _z : Sample L in E, ENNReal.ofReal (t-s)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
      apply lintegral_congr_ae
      have hsum := (Measure.quasiMeasurePreserving_fst
        (μ := ExponentialClocks.clockMeasure (Vertex L)) (ν := FairMarks.markMeasure (Event L))).ae
        (ClockIntervalCount.tsum_exposure_increment_ae (V := Vertex L))
      filter_upwards [ae_restrict_of_ae hsum] with z hz
      exact hz v s t hs hst
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

theorem count_integral_on_history (L : Nat) (v : Vertex L) (s t : Real)
    (hs : 0 ≤ s) (hst : s ≤ t) (E : Set (Sample L))
    (hE : MeasurableSet[MarkedClockFiltration.history L s] E) :
    (∫ z in E, (ClockIntervalCount.count L v s t z).toReal
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      (t-s) * (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)).real E := by
  rw [integral_toReal (ClockIntervalCount.count_measurable L v s t).aemeasurable
    ((ae_restrict_of_ae (ClockIntervalCount.count_finite_ae L)).mono
      (fun z hz => (hz v s t).lt_top)), count_lintegral_on_history L v s t hs hst E hE,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hst)]
  rfl

theorem original_count_increment_integral (L : Nat) (v : Vertex L) (s t : Real)
    (hs : 0 ≤ s) (hst : s ≤ t) (E : Set (Sample L))
    (hE : MeasurableSet[MarkedClockFiltration.history L s] E) :
    (∫ z in E, ((MarkedRingCount.count L v t z).toReal -
      (MarkedRingCount.count L v s z).toReal)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      (t-s) * (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)).real E := by
  calc
    _ = ∫ z in E, (ClockIntervalCount.count L v s t z).toReal
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) :=
      by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (ClockIntervalCount.count_toReal_eq_sub_ae L v s t hst)] with z hz
        exact hz.symm
    _ = _ := count_integral_on_history L v s t hs hst E hE

def markedCount (L : Nat) (v : Vertex L) (b : Bool) (s t : Real) (z : Sample L) : ENNReal :=
  ∑' k : Nat, if s < ClockEventWord.eventTime z.1 (v,k) ∧
    ClockEventWord.eventTime z.1 (v,k) ≤ t ∧ z.2 (v,k) = b then 1 else 0

theorem markedCount_measurable (L : Nat) (v : Vertex L) (b : Bool) (s t : Real) :
    Measurable (markedCount L v b s t) := by
  apply Measurable.tsum
  intro k
  exact Measurable.ite
    ((measurableSet_lt measurable_const (MarkedClockFiltration.arrival_measurable L (v,k))).inter
      ((measurableSet_le (MarkedClockFiltration.arrival_measurable L (v,k)) measurable_const).inter
        (measurableSet_eq_fun (MarkedClockFiltration.mark_measurable L (v,k)) measurable_const)))
    measurable_const measurable_const

theorem markedCount_le_count (L : Nat) (v : Vertex L) (b : Bool) (s t : Real) (z : Sample L) :
    markedCount L v b s t z ≤ ClockIntervalCount.count L v s t z := by
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases h : s < ClockEventWord.eventTime z.1 (v,k) ∧
      ClockEventWord.eventTime z.1 (v,k) ≤ t ∧ z.2 (v,k) = b
  · simp only [ite_eq_left h, ite_eq_left (show s < ClockEventWord.eventTime z.1 (v,k) ∧
        ClockEventWord.eventTime z.1 (v,k) ≤ t from ⟨h.1,h.2.1⟩), le_refl]
  · simp only [ite_eq_right h]
    exact bot_le

theorem markedCount_finite_ae (L : Nat) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      ∀ v b s t, markedCount L v b s t z ≠ ⊤ := by
  filter_upwards [ClockIntervalCount.count_finite_ae L] with z hz
  exact fun v b s t => ne_top_of_le_ne_top (hz v s t) (markedCount_le_count L v b s t z)

theorem markedCount_add (L : Nat) (v : Vertex L) (b : Bool) (s t : Real) (hst : s ≤ t)
    (z : Sample L) : MarkedRingCount.markedCount L v b s z + markedCount L v b s t z =
      MarkedRingCount.markedCount L v b t z := by
  rw [MarkedRingCount.markedCount, markedCount, ← ENNReal.tsum_add, MarkedRingCount.markedCount]
  apply tsum_congr
  intro k
  by_cases hb : z.2 (v,k) = b
  · by_cases hs : ClockEventWord.eventTime z.1 (v,k) ≤ s
    · simp only [hs, hs.trans hst, not_lt.mpr hs, hb, and_true,
        ite_true, ite_false, add_zero]
    · by_cases ht : ClockEventWord.eventTime z.1 (v,k) ≤ t
      · simp only [hs, ht, lt_of_not_ge hs, hb, and_true, and_self, ite_false, ite_true, zero_add]
      · simp only [hs, ht, hb, and_false, and_true, ite_false, add_zero]
  · simp only [hb, and_false, ite_false, add_zero]

theorem markedCount_toReal_eq_sub_ae (L : Nat) (v : Vertex L) (b : Bool) (s t : Real)
    (hst : s ≤ t) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      (markedCount L v b s t z).toReal = (MarkedRingCount.markedCount L v b t z).toReal -
        (MarkedRingCount.markedCount L v b s z).toReal := by
  filter_upwards [MarkedRingCount.markedCount_finite_ae L, markedCount_finite_ae L] with z hz hw
  have h := congrArg ENNReal.toReal (markedCount_add L v b s t hst z)
  rw [ENNReal.toReal_add (hz v b s) (hw v b s t)] at h
  linarith

theorem lintegral_markedCount_eq_tsum (L : Nat) (v : Vertex L) (b : Bool) (s t : Real)
    (E : Set (Sample L)) :
    (∫⁻ z in E, markedCount L v b s t z
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      ∑' k : Nat, ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
        {z : Sample L | z ∈ E ∧ s < ClockEventWord.eventTime z.1 (v,k) ∧
          ClockEventWord.eventTime z.1 (v,k) ≤ t ∧ z.2 (v,k) = b} := by
  unfold markedCount
  trans ∑' k : Nat, ∫⁻ z in E,
    (if s < ClockEventWord.eventTime z.1 (v,k) ∧ ClockEventWord.eventTime z.1 (v,k) ≤ t ∧
      z.2 (v,k) = b then (1 : ENNReal) else 0)
    ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
  · exact lintegral_tsum (fun k => (Measurable.ite
      ((measurableSet_lt measurable_const (MarkedClockFiltration.arrival_measurable L (v,k))).inter
        ((measurableSet_le (MarkedClockFiltration.arrival_measurable L (v,k)) measurable_const).inter
          (measurableSet_eq_fun (MarkedClockFiltration.mark_measurable L (v,k)) measurable_const)))
      measurable_const measurable_const).aemeasurable)
  · apply tsum_congr
    intro k
    let W : Set (Sample L) := {z | s < ClockEventWord.eventTime z.1 (v,k) ∧
      ClockEventWord.eventTime z.1 (v,k) ≤ t ∧ z.2 (v,k) = b}
    have hW : MeasurableSet W :=
      (measurableSet_lt measurable_const (MarkedClockFiltration.arrival_measurable L (v,k))).inter
        ((measurableSet_le (MarkedClockFiltration.arrival_measurable L (v,k)) measurable_const).inter
          (measurableSet_eq_fun (MarkedClockFiltration.mark_measurable L (v,k)) measurable_const))
    have hfun : (fun z : Sample L => if s < ClockEventWord.eventTime z.1 (v,k) ∧
        ClockEventWord.eventTime z.1 (v,k) ≤ t ∧ z.2 (v,k) = b then (1 : ENNReal) else 0) =
        W.indicator (fun _ => (1 : ENNReal)) := by
      funext z
      simp only [W, Set.indicator, Set.mem_ofPred_eq]
    rw [hfun, lintegral_indicator_const hW, one_mul, Measure.restrict_apply hW]
    congr 1
    ext z
    simp only [W, Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto

theorem markedCount_lintegral_on_history (L : Nat) (v : Vertex L) (b : Bool) (s t : Real)
    (hs : 0 ≤ s) (hst : s ≤ t) (E : Set (Sample L))
    (hE : MeasurableSet[MarkedClockFiltration.history L s] E) :
    (∫⁻ z in E, markedCount L v b s t z
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      ENNReal.ofReal ((t-s)/2) * ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) E := by
  rw [lintegral_markedCount_eq_tsum]
  calc
    _ = (∑' k : Nat, ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
        {z : Sample L | z ∈ E ∧ s < ClockEventWord.eventTime z.1 (v,k) ∧
          ClockEventWord.eventTime z.1 (v,k) ≤ t}) * (2 : ENNReal)⁻¹ := by
      simp_rw [MarkedIntervalFactor.window_set_factor L v _ s t E hE b]
      exact ENNReal.tsum_mul_right
    _ = (∫⁻ z in E, ClockIntervalCount.count L v s t z
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) * (2 : ENNReal)⁻¹ := by
      rw [ClockIntervalCount.lintegral_count_eq_tsum_restrict]
      congr 1
    _ = _ := by
      rw [count_lintegral_on_history L v s t hs hst E hE,
        ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real) < 2)]
      norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

theorem markedCount_integral_on_history (L : Nat) (v : Vertex L) (b : Bool) (s t : Real)
    (hs : 0 ≤ s) (hst : s ≤ t) (E : Set (Sample L))
    (hE : MeasurableSet[MarkedClockFiltration.history L s] E) :
    (∫ z in E, (markedCount L v b s t z).toReal
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      ((t-s)/2) * (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)).real E := by
  rw [integral_toReal (markedCount_measurable L v b s t).aemeasurable
    ((ae_restrict_of_ae (markedCount_finite_ae L)).mono (fun z hz => (hz v b s t).lt_top)),
    markedCount_lintegral_on_history L v b s t hs hst E hE, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (t-s)/2)]
  rfl

theorem original_marked_increment_integral (L : Nat) (v : Vertex L) (b : Bool) (s t : Real)
    (hs : 0 ≤ s) (hst : s ≤ t) (E : Set (Sample L))
    (hE : MeasurableSet[MarkedClockFiltration.history L s] E) :
    (∫ z in E, ((MarkedRingCount.markedCount L v b t z).toReal -
      (MarkedRingCount.markedCount L v b s z).toReal)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      ((t-s)/2) * (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)).real E := by
  calc
    _ = ∫ z in E, (markedCount L v b s t z).toReal
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) :=
      by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (markedCount_toReal_eq_sub_ae L v b s t hst)] with z hz
        exact hz.symm
    _ = _ := markedCount_integral_on_history L v b s t hs hst E hE

theorem markedCount_toReal_integrable (L : Nat) (v : Vertex L) (b : Bool) (s t : Real) :
    Integrable (fun z => (markedCount L v b s t z).toReal)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  integrable_toReal_of_lintegral_ne_top (markedCount_measurable L v b s t).aemeasurable
    (ne_top_of_le_ne_top (ClockIntervalCount.count_lintegral_ne_top L v s t)
      (lintegral_mono (markedCount_le_count L v b s t)))
end MathResearchAnalysis.MarkedConditionalCount
