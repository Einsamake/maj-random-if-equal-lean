module
public import MathResearchAnalysis.ClockGapOccupation
public import MathResearchAnalysis.MarkedRingIntegrability
set_option autoImplicit false
/-! Actual counts in a physical interval (s,t], retaining infinity on all samples.
Elapsed occupations are differenced only as real bounded gap lengths; count
real representatives are differenced only after actual a.e. finiteness is proved.
No conditional count mean or compensation formula is an input. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.ClockIntervalCount
open MeasureTheory Filter
open DropletClockLaw (Sample Event Vertex)
variable {V : Type*}

def count (L : Nat) (v : Vertex L) (s t : Real) (z : Sample L) : ENNReal :=
  ∑' k : Nat, if s < ClockEventWord.eventTime z.1 (v,k) ∧
    ClockEventWord.eventTime z.1 (v,k) ≤ t then 1 else 0

theorem count_measurable (L : Nat) (v : Vertex L) (s t : Real) :
    Measurable (count L v s t) := by
  apply Measurable.tsum
  intro k
  exact Measurable.ite
    ((measurableSet_lt measurable_const (MarkedClockFiltration.arrival_measurable L (v,k))).inter
      (measurableSet_le (MarkedClockFiltration.arrival_measurable L (v,k)) measurable_const))
    measurable_const measurable_const

theorem count_history_measurable (L : Nat) (v : Vertex L) (s t : Real) (hst : s ≤ t) :
    @Measurable (Sample L) ENNReal (MarkedClockFiltration.history L t) inferInstance
      (count L v s t) := by
  let : MeasurableSpace (Sample L) := MarkedClockFiltration.history L t
  apply Measurable.tsum
  intro k
  have hs : MeasurableSet {z : Sample L | s < ClockEventWord.eventTime z.1 (v,k)} := by
    simpa only [Set.compl_ofPred, not_le] using
      (MarkedClockFiltration.arrival_event_measurable L (v,k) (u := s) hst).compl
  exact Measurable.ite (hs.inter
    (MarkedClockFiltration.arrival_event_measurable L (v,k) (u := t) le_rfl))
    measurable_const measurable_const

theorem count_add (L : Nat) (v : Vertex L) (s t : Real) (hst : s ≤ t) (z : Sample L) :
    MarkedRingCount.count L v s z + count L v s t z = MarkedRingCount.count L v t z := by
  rw [MarkedRingCount.count, count, ← ENNReal.tsum_add, MarkedRingCount.count]
  apply tsum_congr
  intro k
  by_cases hs : ClockEventWord.eventTime z.1 (v,k) ≤ s
  · simp only [ite_eq_left hs, ite_eq_left (hs.trans hst),
      not_lt.mpr hs, false_and, ite_false, add_zero]
  · by_cases ht : ClockEventWord.eventTime z.1 (v,k) ≤ t
    · simp only [ite_eq_right hs, lt_of_not_ge hs, ht, and_self, ite_true, zero_add]
    · simp only [ite_eq_right hs, ht, and_false, ite_false, add_zero]

theorem count_le_total (L : Nat) (v : Vertex L) (s t : Real) (z : Sample L) :
    count L v s t z ≤ MarkedRingCount.count L v t z := by
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases h : s < ClockEventWord.eventTime z.1 (v,k) ∧ ClockEventWord.eventTime z.1 (v,k) ≤ t
  · simp only [ite_eq_left h, ite_eq_left h.2, le_refl]
  · simp only [ite_eq_right h]
    exact bot_le

theorem count_finite_ae (L : Nat) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      ∀ v : Vertex L, ∀ s t : Real, count L v s t z ≠ ⊤ := by
  filter_upwards [MarkedRingCount.count_finite_ae L] with z hz
  exact fun v s t => ne_top_of_le_ne_top (hz v t) (count_le_total L v s t z)

theorem count_lintegral_ne_top (L : Nat) (v : Vertex L) (s t : Real) :
    (∫⁻ z, count L v s t z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) ≠ ⊤ :=
  ne_top_of_le_ne_top (MarkedRingIntegrability.count_lintegral_ne_top L v t)
    (lintegral_mono (count_le_total L v s t))

theorem count_toReal_integrable (L : Nat) (v : Vertex L) (s t : Real) :
    Integrable (fun z => (count L v s t z).toReal)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  integrable_toReal_of_lintegral_ne_top (count_measurable L v s t).aemeasurable
    (count_lintegral_ne_top L v s t)

theorem count_toReal_eq_sub_ae (L : Nat) (v : Vertex L) (s t : Real) (hst : s ≤ t) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      (count L v s t z).toReal =
        (MarkedRingCount.count L v t z).toReal - (MarkedRingCount.count L v s z).toReal := by
  filter_upwards [MarkedRingCount.count_finite_ae L] with z hz
  have hf := ne_top_of_le_ne_top (hz v t) (count_le_total L v s t z)
  have h := congrArg ENNReal.toReal (count_add L v s t hst z)
  rw [ENNReal.toReal_add (hz v s) hf] at h
  linarith

theorem lintegral_count_eq_tsum (L : Nat) (v : Vertex L) (s t : Real)
    (μ : Measure (Sample L)) :
    (∫⁻ z, count L v s t z ∂μ) =
      ∑' k : Nat, μ {z : Sample L | s < ClockEventWord.eventTime z.1 (v,k) ∧
        ClockEventWord.eventTime z.1 (v,k) ≤ t} := by
  unfold count
  calc
    _ = ∑' k : Nat, ∫⁻ z : Sample L,
        (if s < ClockEventWord.eventTime z.1 (v,k) ∧ ClockEventWord.eventTime z.1 (v,k) ≤ t
          then (1 : ENNReal) else 0) ∂μ :=
      lintegral_tsum (fun k => (Measurable.ite
        ((measurableSet_lt measurable_const (MarkedClockFiltration.arrival_measurable L (v,k))).inter
          (measurableSet_le (MarkedClockFiltration.arrival_measurable L (v,k)) measurable_const))
        measurable_const measurable_const).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro k
      have hm : MeasurableSet {z : Sample L | s < ClockEventWord.eventTime z.1 (v,k) ∧
          ClockEventWord.eventTime z.1 (v,k) ≤ t} :=
        (measurableSet_lt measurable_const (MarkedClockFiltration.arrival_measurable L (v,k))).inter
          (measurableSet_le (MarkedClockFiltration.arrival_measurable L (v,k)) measurable_const)
      have heq : (fun z : Sample L => if s < ClockEventWord.eventTime z.1 (v,k) ∧
          ClockEventWord.eventTime z.1 (v,k) ≤ t then (1 : ENNReal) else 0) =
          {z : Sample L | s < ClockEventWord.eventTime z.1 (v,k) ∧
            ClockEventWord.eventTime z.1 (v,k) ≤ t}.indicator (fun _ => (1 : ENNReal)) := by
        funext z
        simp only [Set.indicator, Set.mem_ofPred_eq]
      rw [heq, lintegral_indicator_const hm, one_mul]

theorem lintegral_count_eq_tsum_restrict (L : Nat) (v : Vertex L) (s t : Real)
    (E : Set (Sample L)) :
    (∫⁻ z in E, count L v s t z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      ∑' k : Nat, ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
        (E ∩ {z : Sample L | s < ClockEventWord.eventTime z.1 (v,k) ∧
          ClockEventWord.eventTime z.1 (v,k) ≤ t}) := by
  rw [lintegral_count_eq_tsum]
  apply tsum_congr
  intro k
  have hm : MeasurableSet {z : Sample L | s < ClockEventWord.eventTime z.1 (v,k) ∧
      ClockEventWord.eventTime z.1 (v,k) ≤ t} :=
    (measurableSet_lt measurable_const (MarkedClockFiltration.arrival_measurable L (v,k))).inter
      (measurableSet_le (MarkedClockFiltration.arrival_measurable L (v,k)) measurable_const)
  rw [Measure.restrict_apply hm]
  exact congrArg (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) (Set.inter_comm _ _)

theorem exposure_mono (v : V) (k : Nat) (ω : ExponentialClocks.Sample V) :
    Monotone (fun t : Real => ClockGapOccupation.exposure v k t ω) := by
  intro s t hst
  exact min_le_min le_rfl (max_le_max le_rfl (sub_le_sub_right hst _))

theorem exposure_increment_nonnegative (v : V) (k : Nat) (s t : Real) (hst : s ≤ t)
    (ω : ExponentialClocks.Sample V) :
    0 ≤ ClockGapOccupation.exposure v k t ω - ClockGapOccupation.exposure v k s ω :=
  sub_nonneg.mpr (exposure_mono v k ω hst)

theorem exposure_increment_measurable (v : V) (k : Nat) (s t : Real) :
    Measurable (fun ω => ClockGapOccupation.exposure v k t ω - ClockGapOccupation.exposure v k s ω) :=
  (ClockGapOccupation.exposure_measurable v k t).sub (ClockGapOccupation.exposure_measurable v k s)

theorem exposure_increment_zero_of_arrived (v : V) (k : Nat) (s t : Real) (hst : s ≤ t)
    (ω : ExponentialClocks.Sample V) (ha : ArrivalFiltration.chronologicalArrival v k ω ≤ s) :
    ClockGapOccupation.exposure v k t ω - ClockGapOccupation.exposure v k s ω = 0 := by
  have hnext : ClockCandidateIntervals.before v (k+1) ω ≤ s := by
    simpa only [ClockCandidateIntervals.before_succ] using ha
  have hbefore : ClockCandidateIntervals.before v k ω ≤ s :=
    (ClockCandidateIntervals.before_monotone v ω (by omega : k ≤ k+1)).trans hnext
  simp only [ClockGapOccupation.exposure_eq_min_sub, min_eq_right (hnext.trans hst),
    min_eq_right (hbefore.trans hst), min_eq_right hnext, min_eq_right hbefore, sub_self]

theorem sum_exposure_increment (v : V) (n : Nat) (s t : Real) (hs : 0 ≤ s) (hst : s ≤ t)
    (ω : ExponentialClocks.Sample V) :
    ∑ k ∈ Finset.range n,
      (ClockGapOccupation.exposure v k t ω - ClockGapOccupation.exposure v k s ω) =
      min t (ClockCandidateIntervals.before v n ω) - min s (ClockCandidateIntervals.before v n ω) := by
  rw [Finset.sum_sub_distrib, ClockGapOccupation.sum_exposure v n t (hs.trans hst) ω,
    ClockGapOccupation.sum_exposure v n s hs ω]

theorem tsum_exposure_increment_of_before (v : V) (n : Nat) (s t : Real) (hs : 0 ≤ s) (hst : s ≤ t)
    (ω : ExponentialClocks.Sample V) (hn : t ≤ ClockCandidateIntervals.before v n ω) :
    ∑' k : Nat, ENNReal.ofReal
      (ClockGapOccupation.exposure v k t ω - ClockGapOccupation.exposure v k s ω) = ENNReal.ofReal (t-s) := by
  rw [tsum_eq_sum (s := Finset.range n) (fun k hk => ?_)]
  · rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => exposure_increment_nonnegative v k s t hst ω),
      sum_exposure_increment v n s t hs hst ω, min_eq_left hn, min_eq_left (hst.trans hn)]
  · have ht : t ≤ ClockCandidateIntervals.before v k ω :=
      hn.trans (ClockCandidateIntervals.before_monotone v ω (by simpa using hk))
    rw [ClockGapOccupation.exposure_zero_of_horizon_le_before v k t ω ht,
      ClockGapOccupation.exposure_zero_of_horizon_le_before v k s ω (hst.trans ht),
      sub_self, ENNReal.ofReal_zero]

theorem tsum_exposure_increment_ae [Countable V] :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ v s t, 0 ≤ s → s ≤ t →
      ∑' k : Nat, ENNReal.ofReal
        (ClockGapOccupation.exposure v k t ω - ClockGapOccupation.exposure v k s ω) = ENNReal.ofReal (t-s) := by
  filter_upwards [ArrivalFiltration.chronologicalArrival_unbounded_ae (V := V)] with ω hω
  intro v s t hs hst
  obtain ⟨n,hn⟩ := eventually_atTop.mp ((tendsto_atTop.mp (hω v)) t)
  exact tsum_exposure_increment_of_before v (n+1) s t hs hst ω (by
    simpa only [ClockCandidateIntervals.before_succ] using hn n le_rfl)
theorem tsum_exposure_increment_joint_ae (L : Nat) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      ∀ v : Vertex L, ∀ s t : Real, 0 ≤ s → s ≤ t →
        ∑' k : Nat, ENNReal.ofReal
          (ClockGapOccupation.exposure v k t z.1 - ClockGapOccupation.exposure v k s z.1) =
          ENNReal.ofReal (t-s) :=
  (Measure.quasiMeasurePreserving_fst (μ := ExponentialClocks.clockMeasure (Vertex L))
    (ν := FairMarks.markMeasure (Event L))).ae (tsum_exposure_increment_ae (V := Vertex L))
end MathResearchAnalysis.ClockIntervalCount
