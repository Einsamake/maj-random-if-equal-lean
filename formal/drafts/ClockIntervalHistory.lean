module
public import MathResearchAnalysis.ClockRingMean
public import MathResearchAnalysis.FutureGapHistory
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
set_option autoImplicit false
/-! A fixed clock gap contributes equal expected elapsed occupation and
arrival count, even after multiplication by any event in the original past.
The proof resets only an unrevealed gap and uses its genuine product law. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.ClockIntervalHistory
open MeasureTheory ProbabilityTheory Set
variable {V : Type*}

def increment (p s t d : Real) : Real :=
  TruncatedExponential.cap (max 0 (t-p)) d -
    TruncatedExponential.cap (max 0 (s-p)) d

theorem cap_cutoff_mono (p d : Real) {s t : Real} (hst : s ≤ t) :
    TruncatedExponential.cap (max 0 (s-p)) d ≤
      TruncatedExponential.cap (max 0 (t-p)) d :=
  min_le_min_left _ (max_le_max le_rfl (sub_le_sub_right hst p))

theorem increment_nonneg (p d : Real) {s t : Real} (hst : s ≤ t) :
    0 ≤ increment p s t d := sub_nonneg.mpr (cap_cutoff_mono p d hst)

theorem increment_zero_of_arrival_le (p s t d : Real) (hst : s ≤ t)
    (hs : p + max d 0 ≤ s) : increment p s t d = 0 := by
  have hds : max d 0 ≤ max 0 (s-p) := (by linarith : max d 0 ≤ s-p).trans (le_max_right _ _)
  have hdt : max d 0 ≤ max 0 (t-p) := hds.trans (max_le_max le_rfl (sub_le_sub_right hst p))
  simp only [increment, TruncatedExponential.cap, min_eq_left hds, min_eq_left hdt, sub_self]

theorem increment_lintegral (p s t : Real) (hst : s ≤ t) :
    (∫⁻ d : Real, ENNReal.ofReal (increment p s t d) ∂expMeasure 1) =
      expMeasure 1 {d : Real | s < p + max d 0 ∧ p + max d 0 ≤ t} := by
  have hmeas : Measurable (fun d : Real => ENNReal.ofReal
      (TruncatedExponential.cap (max 0 (s-p)) d)) :=
    (TruncatedExponential.cap_measurable _).ennreal_ofReal
  have hfin : (∫⁻ d : Real, ENNReal.ofReal
      (TruncatedExponential.cap (max 0 (s-p)) d) ∂expMeasure 1) ≠ ⊤ := by
    rw [ClockRingMean.prior_cap_lintegral p s]
    exact measure_ne_top _ _
  simp_rw [increment, ENNReal.ofReal_sub _ (TruncatedExponential.cap_nonneg (le_max_left _ _) _)]
  rw [lintegral_sub hmeas hfin (ae_of_all _ (fun d =>
      ENNReal.ofReal_le_ofReal (cap_cutoff_mono p d hst))),
    ClockRingMean.prior_cap_lintegral p t, ClockRingMean.prior_cap_lintegral p s]
  have hsub : {d : Real | p + max d 0 ≤ s} ⊆ {d : Real | p + max d 0 ≤ t} :=
    fun _ hd => hd.trans hst
  rw [← measure_sdiff hsub
    (measurableSet_le (measurable_const.add (measurable_id.max measurable_const)) measurable_const).nullMeasurableSet
    (measure_ne_top _ _)]
  congr 1
  ext d
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_le, and_comm]

/-- A fixed actual gap has the same mean occupation increment and arrival
increment on every event measurable in the original common clock history. -/
theorem gap_increment_lintegral_on_history (v : V) (k : Nat) (s t : Real)
    (hst : s ≤ t) (E : Set (ExponentialClocks.Sample V))
    (hE : MeasurableSet[ArrivalFiltration.clockHistory V s] E) :
    (∫⁻ ω in E, ENNReal.ofReal (ClockGapOccupation.exposure v k t ω -
      ClockGapOccupation.exposure v k s ω) ∂ExponentialClocks.clockMeasure V) =
      ExponentialClocks.clockMeasure V (E ∩ {ω |
        s < ArrivalFiltration.chronologicalArrival v k ω ∧
          ArrivalFiltration.chronologicalArrival v k ω ≤ t}) := by
  classical
  let H := RandomThresholdSurvival.RestSample V v k
  let ν : Measure H := (ExponentialClocks.clockMeasure V).map
    (RandomThresholdSurvival.restCoordinates v k)
  have hEa : MeasurableSet E := (ArrivalFiltration.clockHistory V).le s E hE
  let B : Set H := (ClockGapReset.reset v k s) ⁻¹' E
  have hB : MeasurableSet B := hEa.preimage (ClockGapReset.reset_measurable v k s)
  let F : H × Real → ENNReal := fun q => if q.1 ∈ B then
    ENNReal.ofReal (increment (ClockGapReset.prior v k q.1) s t q.2) else 0
  let C : Set (H × Real) := {q | q.1 ∈ B ∧
    s < ClockGapReset.prior v k q.1 + max q.2 0 ∧
      ClockGapReset.prior v k q.1 + max q.2 0 ≤ t}
  have hp : Measurable (fun q : H × Real => ClockGapReset.prior v k q.1) :=
    (ClockGapReset.prior_measurable v k).comp measurable_fst
  have hinc : Measurable (fun q : H × Real =>
      ENNReal.ofReal (increment (ClockGapReset.prior v k q.1) s t q.2)) :=
    (((measurable_snd.max measurable_const).min
      (measurable_const.max (measurable_const.sub hp))).sub
      ((measurable_snd.max measurable_const).min
        (measurable_const.max (measurable_const.sub hp)))).ennreal_ofReal
  have hF : Measurable F := Measurable.ite (hB.preimage measurable_fst) hinc measurable_const
  have hC : MeasurableSet C := (hB.preimage measurable_fst).inter
    ((measurableSet_lt measurable_const (hp.add (measurable_snd.max measurable_const))).inter
      (measurableSet_le (hp.add (measurable_snd.max measurable_const)) measurable_const))
  have hprod := (RandomThresholdSurvival.gap_independent_rest v k).symm.hasLaw_prod
    (hasLaw_map (RandomThresholdSurvival.restCoordinates_measurable v k).aemeasurable)
    (ExponentialClocks.gap_hasLaw v k)
  have hleft (ω : ExponentialClocks.Sample V) :
      E.indicator (fun ω => ENNReal.ofReal (ClockGapOccupation.exposure v k t ω -
        ClockGapOccupation.exposure v k s ω)) ω =
      F (RandomThresholdSurvival.restCoordinates v k ω, ExponentialClocks.gap v k ω) := by
    have hi : ClockGapOccupation.exposure v k t ω - ClockGapOccupation.exposure v k s ω =
        increment (ClockGapReset.prior v k (RandomThresholdSurvival.restCoordinates v k ω))
          s t (ExponentialClocks.gap v k ω) := by
      simp only [increment, TruncatedExponential.cap, ClockGapOccupation.exposure,
        ClockGapReset.prior_rest_eq_before]
    by_cases hf : s < ArrivalFiltration.chronologicalArrival v k ω
    · have he : ω ∈ E ↔ RandomThresholdSurvival.restCoordinates v k ω ∈ B :=
        FutureGapHistory.reset_history_event_iff v k s ω hf E hE
      by_cases hω : ω ∈ E
      · simp only [Set.indicator_of_mem hω, F, ite_eq_left (he.mp hω), hi]
      · have hb : RandomThresholdSurvival.restCoordinates v k ω ∉ B :=
          fun h => hω (he.mpr h)
        simp only [Set.indicator_of_notMem hω, F, ite_eq_right hb]
    · have hi0 : increment
          (ClockGapReset.prior v k (RandomThresholdSurvival.restCoordinates v k ω))
          s t (ExponentialClocks.gap v k ω) = 0 := by
        apply increment_zero_of_arrival_le _ _ _ _ hst
        simpa only [ClockGapReset.prior_rest_eq_before,
          ← ClockCandidateIntervals.arrival_eq_before_add] using le_of_not_gt hf
      simp only [Set.indicator, F, hi, hi0, ENNReal.ofReal_zero, ite_self]
  have hevent : {ω : ExponentialClocks.Sample V |
      (RandomThresholdSurvival.restCoordinates v k ω, ExponentialClocks.gap v k ω) ∈ C} =
      E ∩ {ω | s < ArrivalFiltration.chronologicalArrival v k ω ∧
        ArrivalFiltration.chronologicalArrival v k ω ≤ t} := by
    ext ω
    change (RandomThresholdSurvival.restCoordinates v k ω ∈ B ∧
      s < ClockGapReset.prior v k (RandomThresholdSurvival.restCoordinates v k ω) +
        max (ExponentialClocks.gap v k ω) 0 ∧
      ClockGapReset.prior v k (RandomThresholdSurvival.restCoordinates v k ω) +
        max (ExponentialClocks.gap v k ω) 0 ≤ t) ↔ _
    rw [ClockGapReset.prior_rest_eq_before, ← ClockCandidateIntervals.arrival_eq_before_add]
    by_cases hf : s < ArrivalFiltration.chronologicalArrival v k ω
    · have he : ω ∈ E ↔ RandomThresholdSurvival.restCoordinates v k ω ∈ B :=
        FutureGapHistory.reset_history_event_iff v k s ω hf E hE
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, he, hf, true_and]
    · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hf, false_and, and_false]
  rw [← lintegral_indicator hEa]
  calc
    _ = ∫⁻ ω : ExponentialClocks.Sample V,
        F (RandomThresholdSurvival.restCoordinates v k ω, ExponentialClocks.gap v k ω)
        ∂ExponentialClocks.clockMeasure V := lintegral_congr hleft
    _ = ∫⁻ q, F q ∂ν.prod (expMeasure 1) := hprod.lintegral_comp hF.aemeasurable
    _ = ∫⁻ h : H, ∫⁻ d : Real, F (h,d) ∂expMeasure 1 ∂ν :=
      lintegral_prod _ hF.aemeasurable
    _ = ∫⁻ h : H, expMeasure 1 (Prod.mk h ⁻¹' C) ∂ν := by
      apply lintegral_congr
      intro h
      by_cases hb : h ∈ B
      · simp only [F, ite_eq_left hb]
        rw [increment_lintegral _ _ _ hst]
        congr 1
        ext d
        simp only [Set.mem_preimage, C, Set.mem_ofPred_eq, hb, true_and]
      · simp only [F, ite_eq_right hb, lintegral_zero]
        have hempty : Prod.mk h ⁻¹' C = ∅ := by
          ext d
          simp only [Set.mem_preimage, C, Set.mem_ofPred_eq, hb, false_and,
            Set.mem_empty_iff_false]
        rw [hempty, measure_empty]
    _ = ν.prod (expMeasure 1) C := (Measure.prod_apply hC).symm
    _ = ExponentialClocks.clockMeasure V
        {ω | (RandomThresholdSurvival.restCoordinates v k ω, ExponentialClocks.gap v k ω) ∈ C} :=
      (hprod.measure_eq (p := fun q => q ∈ C) hC).symm
    _ = _ := congrArg (ExponentialClocks.clockMeasure V) hevent

end MathResearchAnalysis.ClockIntervalHistory
