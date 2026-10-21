module
public import MathResearchAnalysis.ClockGapOccupation
public import MathResearchAnalysis.TruncatedExponential
public import MathResearchAnalysis.MarkedRingCount
public import Mathlib.MeasureTheory.Integral.Prod
set_option autoImplicit false
/-! Exact means of the actual ring counts. Each exponential gap contributes
its elapsed occupation length, whose mean equals its arrival probability.
The actual gap/rest product law and the pathwise occupation partition prove
the unit physical-time rate. No Poisson law or compensation formula is assumed. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.ClockRingMean
open MeasureTheory ProbabilityTheory Set
open DropletClockLaw (Sample Vertex)
variable {V : Type*}

/-- A preceding time beyond the horizon contributes neither occupation nor an arrival. -/
theorem prior_cap_lintegral (p t : Real) :
    (∫⁻ d : Real, ENNReal.ofReal (TruncatedExponential.cap (max 0 (t-p)) d)
      ∂expMeasure 1) = expMeasure 1 {d : Real | p + max d 0 ≤ t} := by
  by_cases hp : p ≤ t
  · have hset : {d : Real | p + max d 0 ≤ t} = Iic (t-p) := by
      ext d
      constructor
      · intro hd
        change p + max d 0 ≤ t at hd
        have hmax : d ≤ max d 0 := le_max_left _ _
        change d ≤ t-p
        linarith
      · intro hd
        have hmax : max d 0 ≤ t-p := max_le hd (sub_nonneg.mpr hp)
        change p + max d 0 ≤ t
        linarith
    rw [max_eq_right (sub_nonneg.mpr hp), hset]
    exact TruncatedExponential.cap_lintegral_eq_probability (sub_nonneg.mpr hp)
  · have hset : {d : Real | p + max d 0 ≤ t} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro d hd
      change p + max d 0 ≤ t at hd
      have hmax : 0 ≤ max d 0 := le_max_right _ _
      exact hp (by linarith)
    simp only [max_eq_left (by linarith : t-p ≤ 0),
      TruncatedExponential.cap_zero, ENNReal.ofReal_zero, lintegral_zero,
      hset, measure_empty]

/-- The identity holds under the genuine deleted-gap product decomposition.
The cutoff depends on all remaining coordinates, not on an assumed history law. -/
theorem gap_exposure_lintegral_eq_arrival_measure (v : V) (k : Nat) (t : Real) :
    (∫⁻ ω : ExponentialClocks.Sample V,
      ENNReal.ofReal (ClockGapOccupation.exposure v k t ω)
      ∂ExponentialClocks.clockMeasure V) =
      ExponentialClocks.clockMeasure V
        {ω | ArrivalFiltration.chronologicalArrival v k ω ≤ t} := by
  let H := RandomThresholdSurvival.RestSample V v k
  let ν : Measure H := (ExponentialClocks.clockMeasure V).map
    (RandomThresholdSurvival.restCoordinates v k)
  let F : H × Real → ENNReal := fun q => ENNReal.ofReal
    (TruncatedExponential.cap (max 0 (t - ClockGapReset.prior v k q.1)) q.2)
  let A : Set (H × Real) := {q | ClockGapReset.prior v k q.1 + max q.2 0 ≤ t}
  have hF : Measurable F :=
    ((measurable_snd.max measurable_const).min
      (measurable_const.max (measurable_const.sub
        ((ClockGapReset.prior_measurable v k).comp measurable_fst)))).ennreal_ofReal
  have hA : MeasurableSet A := measurableSet_le
    (((ClockGapReset.prior_measurable v k).comp measurable_fst).add
      (measurable_snd.max measurable_const)) measurable_const
  have hprod := (RandomThresholdSurvival.gap_independent_rest v k).symm.hasLaw_prod
    (hasLaw_map (RandomThresholdSurvival.restCoordinates_measurable v k).aemeasurable)
    (ExponentialClocks.gap_hasLaw v k)
  have hevent : {ω : ExponentialClocks.Sample V |
      (RandomThresholdSurvival.restCoordinates v k ω, ExponentialClocks.gap v k ω) ∈ A} =
      {ω | ArrivalFiltration.chronologicalArrival v k ω ≤ t} := by
    ext ω
    change ClockGapReset.prior v k (RandomThresholdSurvival.restCoordinates v k ω) +
      max (ExponentialClocks.gap v k ω) 0 ≤ t ↔
      ArrivalFiltration.chronologicalArrival v k ω ≤ t
    rw [ClockGapReset.prior_rest_eq_before, ClockCandidateIntervals.arrival_eq_before_add]
  calc
    _ = ∫⁻ ω : ExponentialClocks.Sample V,
        F (RandomThresholdSurvival.restCoordinates v k ω, ExponentialClocks.gap v k ω)
        ∂ExponentialClocks.clockMeasure V := by
      apply lintegral_congr
      intro ω
      simp only [F, TruncatedExponential.cap, ClockGapOccupation.exposure,
        ClockGapReset.prior_rest_eq_before]
    _ = ∫⁻ q, F q ∂ν.prod (expMeasure 1) := hprod.lintegral_comp hF.aemeasurable
    _ = ∫⁻ h : H, ∫⁻ d : Real, F (h,d) ∂expMeasure 1 ∂ν :=
      lintegral_prod _ hF.aemeasurable
    _ = ∫⁻ h : H, expMeasure 1 {d : Real | ClockGapReset.prior v k h + max d 0 ≤ t} ∂ν := by
      apply lintegral_congr
      intro h
      exact prior_cap_lintegral (ClockGapReset.prior v k h) t
    _ = ν.prod (expMeasure 1) A := (Measure.prod_apply hA).symm
    _ = ExponentialClocks.clockMeasure V
        {ω | (RandomThresholdSurvival.restCoordinates v k ω, ExponentialClocks.gap v k ω) ∈ A} :=
      (hprod.measure_eq (p := fun q => q ∈ A) hA).symm
    _ = _ := congrArg (ExponentialClocks.clockMeasure V) hevent

/-- Every finite nonnegative horizon has exactly its length as expected ring count.
The count remains ENNReal-valued, including infinity on exceptional samples. -/
theorem lintegral_count_eq_time (L : Nat) (v : Vertex L) (t : Real) (ht : 0 ≤ t) :
    (∫⁻ z : Sample L, MarkedRingCount.count L v t z
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) = ENNReal.ofReal t := by
  rw [MarkedRingCount.lintegral_count_eq_clock_tsum]
  calc
    _ = ∑' k : Nat, ∫⁻ ω : ExponentialClocks.Sample (Vertex L),
        ENNReal.ofReal (ClockGapOccupation.exposure v k t ω)
        ∂ExponentialClocks.clockMeasure (Vertex L) := by
      apply tsum_congr
      intro k
      exact (gap_exposure_lintegral_eq_arrival_measure v k t).symm
    _ = ∫⁻ ω : ExponentialClocks.Sample (Vertex L),
        ∑' k : Nat, ENNReal.ofReal (ClockGapOccupation.exposure v k t ω)
        ∂ExponentialClocks.clockMeasure (Vertex L) :=
      (lintegral_tsum (fun k =>
        (ClockGapOccupation.exposure_measurable v k t).ennreal_ofReal.aemeasurable)).symm
    _ = ∫⁻ _ω : ExponentialClocks.Sample (Vertex L), ENNReal.ofReal t
        ∂ExponentialClocks.clockMeasure (Vertex L) := by
      apply lintegral_congr_ae
      filter_upwards [ClockGapOccupation.tsum_exposure_ae (V := Vertex L)] with ω hω
      exact hω v t ht
    _ = ENNReal.ofReal t := by rw [lintegral_const, measure_univ, mul_one]

/-- The real integral agrees after the already proved almost-sure finite count. -/
theorem integral_count_eq_time (L : Nat) (v : Vertex L) (t : Real) (ht : 0 ≤ t) :
    (∫ z : Sample L, (MarkedRingCount.count L v t z).toReal
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) = t := by
  rw [integral_toReal (MarkedRingCount.count_measurable L v t).aemeasurable
    ((MarkedRingCount.count_finite_ae L).mono (fun z hz => (hz v t).lt_top)),
    lintegral_count_eq_time L v t ht, ENNReal.toReal_ofReal ht]

end MathResearchAnalysis.ClockRingMean

