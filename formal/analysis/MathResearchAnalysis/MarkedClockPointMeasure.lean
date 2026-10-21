module
public import MathResearchAnalysis.MarkedRingMean
public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
set_option autoImplicit false
/-! A finite expected point measure of the genuine marked clock events.
Each actual positive arrival up to the finite horizon contributes its own
(time,sample) point. Infinite pathwise counts are retained by a countable
measure sum. No Poisson process, predictable sigma or compensation law is
an input or conclusion here. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MarkedClockPointMeasure
open MeasureTheory Set
open DropletClockLaw (Sample Event Vertex)

def window (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal) (k : Nat) : Set (Sample L) :=
  {z | 0 < ClockEventWord.eventTime z.1 (v,k) ∧
    ClockEventWord.eventTime z.1 (v,k) ≤ (T : Real) ∧ z.2 (v,k) = b}

def point (L : Nat) (v : Vertex L) (k : Nat) (z : Sample L) : NNReal × Sample L :=
  ((ClockEventWord.eventTime z.1 (v,k)).toNNReal,z)

def measure (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal) : Measure (NNReal × Sample L) :=
  Measure.sum (fun k : Nat =>
    ((ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)).restrict
      (window L v b T k)).map (point L v k))

def carrier (L : Nat) (T : NNReal) : Set (NNReal × Sample L) :=
  Ioc (0 : NNReal) T ×ˢ univ

theorem window_measurable (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal) (k : Nat) :
    MeasurableSet (window L v b T k) :=
  (measurableSet_lt measurable_const (MarkedClockFiltration.arrival_measurable L (v,k))).inter
    ((measurableSet_le (MarkedClockFiltration.arrival_measurable L (v,k)) measurable_const).inter
      (measurableSet_eq_fun (MarkedClockFiltration.mark_measurable L (v,k)) measurable_const))

theorem point_measurable (L : Nat) (v : Vertex L) (k : Nat) : Measurable (point L v k) :=
  (MarkedClockFiltration.arrival_measurable L (v,k)).real_toNNReal.prodMk measurable_id

theorem point_sample (L : Nat) (v : Vertex L) (k : Nat) (z : Sample L) :
    (point L v k z).2 = z := rfl

theorem point_time_of_window (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (k : Nat) (z : Sample L) (hz : z ∈ window L v b T k) :
    ((point L v k z).1 : Real) = ClockEventWord.eventTime z.1 (v,k) :=
  Real.coe_toNNReal _ hz.1.le

theorem arrival_positive_ae (L : Nat) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e :=
  (Measure.quasiMeasurePreserving_fst (μ := ExponentialClocks.clockMeasure (Vertex L))
    (ν := FairMarks.markMeasure (Event L))).ae
      (ClockEventWord.eventTime_positive_ae (V := Vertex L))

/-- Discarding time-zero events loses no mass under the actual clock law. -/
theorem window_measure_eq (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal) (k : Nat) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) (window L v b T k) =
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
        {z : Sample L | ClockEventWord.eventTime z.1 (v,k) ≤ (T : Real) ∧ z.2 (v,k) = b} := by
  apply measure_congr
  filter_upwards [arrival_positive_ae L] with z hz
  simp only [window, Set.mem_ofPred_eq, hz (v,k), true_and]

/-- Actual application to any measurable subset of time times original samples. -/
theorem measure_apply (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (A : Set (NNReal × Sample L)) (hA : MeasurableSet A) :
    measure L v b T A = ∑' k : Nat,
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
        (window L v b T k ∩ (point L v k ⁻¹' A)) := by
  rw [measure, Measure.sum_apply _ hA]
  apply tsum_congr
  intro k
  rw [Measure.map_apply (point_measurable L v k) hA,
    Measure.restrict_apply (hA.preimage (point_measurable L v k)), Set.inter_comm]

theorem carrier_measurable (L : Nat) (T : NNReal) : MeasurableSet (carrier L T) :=
  measurableSet_Ioc.prod MeasurableSet.univ

theorem point_mem_carrier (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (k : Nat) (z : Sample L) (hz : z ∈ window L v b T k) :
    point L v k z ∈ carrier L T := by
  change ((0 : NNReal) < (ClockEventWord.eventTime z.1 (v,k)).toNNReal ∧
      (ClockEventWord.eventTime z.1 (v,k)).toNNReal ≤ T) ∧ z ∈ (univ : Set (Sample L))
  exact ⟨⟨Real.toNNReal_pos.mpr hz.1,Real.toNNReal_le_iff_le_coe.mpr hz.2.1⟩,Set.mem_univ _⟩

/-- Concentration on (0,T]; this is not a claim about topological support. -/
theorem measure_compl_carrier (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal) :
    measure L v b T (carrier L T)ᶜ = 0 := by
  rw [measure_apply L v b T _ (carrier_measurable L T).compl]
  have hempty (k : Nat) : window L v b T k ∩ (point L v k ⁻¹' (carrier L T)ᶜ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz,hc⟩
    exact hc (point_mem_carrier L v b T k z hz)
  simp only [hempty,measure_empty,tsum_zero]

theorem ae_carrier (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal) :
    ∀ᵐ q ∂measure L v b T, q ∈ carrier L T := by
  rw [ae_iff]
  exact measure_compl_carrier L v b T

theorem measure_univ_eq_tsum (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal) :
    measure L v b T univ = ∑' k : Nat,
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) (window L v b T k) := by
  rw [measure_apply L v b T _ MeasurableSet.univ]
  simp only [Set.preimage_univ,Set.inter_univ]

/-- The mass is the actual expected number of these fair-mark arrivals. -/
theorem measure_univ_eq (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal) :
    measure L v b T univ = ENNReal.ofReal ((T : Real)/2) := by
  rw [measure_univ_eq_tsum]
  simp_rw [window_measure_eq]
  rw [← MarkedRingCount.lintegral_markedCount_eq_tsum,
    MarkedRingMean.lintegral_markedCount_eq_time L v b (T : Real) T.property]

instance finite_measure (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal) :
    IsFiniteMeasure (measure L v b T) where
  measure_univ_lt_top := by
    rw [measure_univ_eq]
    exact ENNReal.ofReal_lt_top

/-- Integrating against the actual point measure is summing the actual
marked arrivals; the nonnegative integrals retain possible infinity. -/
theorem lintegral_eq_tsum (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → ENNReal) (hf : Measurable f) :
    (∫⁻ q, f q ∂measure L v b T) = ∑' k : Nat,
      ∫⁻ z in window L v b T k, f (point L v k z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  rw [measure,lintegral_sum_measure]
  apply tsum_congr
  intro k
  exact lintegral_map hf (point_measurable L v k)

theorem lintegral_eq_pathwise_sum (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → ENNReal) (hf : Measurable f) :
    (∫⁻ q, f q ∂measure L v b T) =
      ∫⁻ z, ∑' k : Nat, (window L v b T k).indicator
        (fun z => f (point L v k z)) z
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  rw [lintegral_eq_tsum L v b T f hf]
  simp_rw [← lintegral_indicator (window_measurable L v b T _)]
  exact (lintegral_tsum (fun k =>
    ((hf.comp (point_measurable L v k)).indicator (window_measurable L v b T k)).aemeasurable)).symm
end MathResearchAnalysis.MarkedClockPointMeasure
