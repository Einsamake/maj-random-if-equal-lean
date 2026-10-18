module

public import MathResearchAnalysis.ClockDeterministicResidual
public import MathResearchAnalysis.ClockWaitingLimit
public import MathResearchAnalysis.SurvivalLaw

set_option autoImplicit false

/-!
# Actual residual survival at countably-valued stopping times

The stopping time is decomposed into its finite real values. On each slice,
the stopped-history event is measurable at that deterministic time, so the
actual clock survival theorem applies. Almost-sure finiteness allows these
disjoint slices to cover the probability space up to a null event. The law
and independence follow from the resulting joint survival probabilities.
-/

public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace MathResearchAnalysis.CountableClockSurvival

variable {V : Type*}

/-- The finite real values actually attained by an extended readiness time. -/
@[expose] def FiniteValues (R : ExponentialClocks.Sample V → WithTop ℝ) :=
  {r : ℝ // (r : WithTop ℝ) ∈ Set.range R}

theorem finiteValues_countable (R : ExponentialClocks.Sample V → WithTop ℝ)
    (hcount : (Set.range R).Countable) : Countable (FiniteValues R) :=
  (hcount.preimage (show Function.Injective (fun r : ℝ => (r : WithTop ℝ)) from
    WithTop.coe_injective)).to_subtype

theorem finiteValue_nonnegative (R : ExponentialClocks.Sample V → WithTop ℝ)
    (hpos : ∀ ω, 0 ≤ R ω) (r : FiniteValues R) : 0 ≤ r.val := by
  obtain ⟨ω, hω⟩ := r.property
  have hp := hpos ω
  rw [hω] at hp
  exact WithTop.coe_le_coe.mp hp

/-- A stopped-history event restricted to one readiness value belongs to its ordinary history. -/
theorem history_slice_measurable (R : ExponentialClocks.Sample V → WithTop ℝ)
    (hR : IsStoppingTime (ArrivalFiltration.clockHistory V) R)
    (hcount : (Set.range R).Countable) (r : ℝ)
    (E : Set (ExponentialClocks.Sample V)) (hE : MeasurableSet[hR.measurableSpace] E) :
    MeasurableSet[ArrivalFiltration.clockHistory V r] (E ∩ {ω | R ω = (r : WithTop ℝ)}) :=
  (hR.measurableSet_inter_eq_iff E r).mp
    (hE.inter (hR.measurableSet_eq_of_countable_range' hcount r))

theorem clock_waiting_measurable (v : V) (R : ExponentialClocks.Sample V → WithTop ℝ)
    (hR : IsStoppingTime (ArrivalFiltration.clockHistory V) R) :
    Measurable (ClockWaitingLimit.waiting (ArrivalFiltration.chronologicalArrival v) R) := by
  have hC := ExtendedNextRing.after_isStoppingTime (ArrivalFiltration.clockHistory V)
    (ArrivalFiltration.chronologicalArrival v) R
    (ArrivalFiltration.chronologicalArrival_monotone v) hR
    (ArrivalFiltration.clock_arrival_isStoppingTime v)
  have hCm : Measurable (ExtendedNextRing.after (ArrivalFiltration.chronologicalArrival v) R) :=
    hC.measurable.mono hC.measurableSpace_le le_rfl
  have hRm : Measurable R := hR.measurable.mono hR.measurableSpace_le le_rfl
  exact ((hCm.untopD 0).sub (hRm.untopD 0)).max measurable_const

theorem after_eq_on_slice (v : V) (R : ExponentialClocks.Sample V → WithTop ℝ)
    (ω : ExponentialClocks.Sample V) (r : ℝ) (hω : R ω = (r : WithTop ℝ)) :
    ExtendedNextRing.after (ArrivalFiltration.chronologicalArrival v) R ω =
      NextRing.extendedNextRing (ArrivalFiltration.chronologicalArrival v) (fun _ => r) ω := by
  rw [← ExtendedNextRing.after_eq_extendedNextRing]
  unfold ExtendedNextRing.after
  rw [hω]

theorem waiting_survival_iff_on_slice (v : V)
    (R : ExponentialClocks.Sample V → WithTop ℝ) (ω : ExponentialClocks.Sample V)
    (r t : ℝ) (hω : R ω = (r : WithTop ℝ))
    (hN : NextRing.extendedNextRing (ArrivalFiltration.chronologicalArrival v) (fun _ => r) ω ≠ ⊤) :
    (t < ClockWaitingLimit.waiting (ArrivalFiltration.chronologicalArrival v) R ω) ↔
      ((r + t : ℝ) : WithTop ℝ) <
        NextRing.extendedNextRing (ArrivalFiltration.chronologicalArrival v) (fun _ => r) ω := by
  have hC := after_eq_on_slice v R ω r hω
  have hRf : R ω ≠ ⊤ := by rw [hω]; exact WithTop.coe_ne_top
  have hCf : ExtendedNextRing.after (ArrivalFiltration.chronologicalArrival v) R ω ≠ ⊤ :=
    hC.trans_ne hN
  rw [ClockWaitingLimit.waiting_eq_sub _ R ω hRf hCf, hC, hω,
    ClockWaitingLimit.representative_lt_iff WithTop.coe_ne_top hN]
  simp only [WithTop.untopD_coe]
  constructor <;> intro h <;> linarith

/-- The disjoint finite-value slices cover every event modulo infinite readiness paths. -/
theorem slice_measure_tsum (R : ExponentialClocks.Sample V → WithTop ℝ)
    (hR : IsStoppingTime (ArrivalFiltration.clockHistory V) R)
    (hcount : (Set.range R).Countable)
    (hfinite : ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, R ω ≠ ⊤)
    (E : Set (ExponentialClocks.Sample V)) (hE : MeasurableSet E) :
    (∑' r : FiniteValues R, ExponentialClocks.clockMeasure V
      (E ∩ {ω | R ω = (r.val : WithTop ℝ)})) = ExponentialClocks.clockMeasure V E := by
  let : Countable (FiniteValues R) := finiteValues_countable R hcount
  have hcover : (⋃ r : FiniteValues R, E ∩ {ω | R ω = (r.val : WithTop ℝ)})
      =ᵐ[ExponentialClocks.clockMeasure V] E := by
    filter_upwards [hfinite] with ω hω
    apply propext
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨r, hEω, _⟩
      exact hEω
    · intro hEω
      have hrep : (((R ω).untopD 0 : ℝ) : WithTop ℝ) = R ω := by
        lift R ω to ℝ using hω with x hx
        simp
      exact ⟨⟨(R ω).untopD 0, ⟨ω, hrep.symm⟩⟩, hEω, hrep.symm⟩
  calc
    _ = ExponentialClocks.clockMeasure V
        (⋃ r : FiniteValues R, E ∩ {ω | R ω = (r.val : WithTop ℝ)}) := by
      symm
      apply measure_iUnion
      · intro r s hrs
        apply Set.disjoint_left.mpr
        intro ω hωr hωs
        apply hrs
        apply Subtype.ext
        exact WithTop.coe_injective (hωr.2.symm.trans hωs.2)
      · intro r
        exact hE.inter ((ArrivalFiltration.clockHistory V).le r.val _
          (hR.measurableSet_eq_of_countable_range hcount r.val))
    _ = _ := measure_congr hcover

/-- Actual deterministic survival on one slice of a countably-valued stopping time. -/
theorem slice_joint_survival [Countable V] (v : V)
    (R : ExponentialClocks.Sample V → WithTop ℝ)
    (hR : IsStoppingTime (ArrivalFiltration.clockHistory V) R)
    (hcount : (Set.range R).Countable) (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (E : Set (ExponentialClocks.Sample V)) (hE : MeasurableSet[hR.measurableSpace] E) :
    ExponentialClocks.clockMeasure V
      ((E ∩ {ω | R ω = (r : WithTop ℝ)}) ∩
        {ω | t < ClockWaitingLimit.waiting (ArrivalFiltration.chronologicalArrival v) R ω}) =
      ENNReal.ofReal (Real.exp (-t)) * ExponentialClocks.clockMeasure V
        (E ∩ {ω | R ω = (r : WithTop ℝ)}) := by
  have hevent : ((E ∩ {ω | R ω = (r : WithTop ℝ)}) ∩
      {ω | t < ClockWaitingLimit.waiting (ArrivalFiltration.chronologicalArrival v) R ω})
      =ᵐ[ExponentialClocks.clockMeasure V]
      ((E ∩ {ω | R ω = (r : WithTop ℝ)}) ∩
        {ω | ((r + t : ℝ) : WithTop ℝ) <
          NextRing.extendedNextRing (ArrivalFiltration.chronologicalArrival v) (fun _ => r) ω}) := by
    filter_upwards [ArrivalFiltration.clock_next_finite_ae v (fun _ => r)] with ω hN
    apply propext
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    by_cases hω : R ω = (r : WithTop ℝ)
    · simp only [hω, and_true,
        waiting_survival_iff_on_slice v R ω r t hω hN]
    · simp only [hω, and_false, false_and]
  rw [measure_congr hevent]
  exact ClockDeterministicResidual.clock_next_joint_survival v r t hr ht
    (E ∩ {ω | R ω = (r : WithTop ℝ)}) (history_slice_measurable R hR hcount r E hE)

/-- The true waiting variable has exponential joint survival with its stopped history.
The only hypotheses on readiness are stopping, countable range, nonnegativity and a.e. finiteness. -/
theorem countable_clock_jointSurvival [Countable V] (v : V)
    (R : ExponentialClocks.Sample V → WithTop ℝ)
    (hR : IsStoppingTime (ArrivalFiltration.clockHistory V) R)
    (hcount : (Set.range R).Countable) (hpos : ∀ ω, 0 ≤ R ω)
    (hfinite : ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, R ω ≠ ⊤) :
    SurvivalLaw.JointSurvival (ClockWaitingLimit.waiting (ArrivalFiltration.chronologicalArrival v) R)
      hR.measurableSpace (ExponentialClocks.clockMeasure V) := by
  let : Countable (FiniteValues R) := finiteValues_countable R hcount
  intro t ht E hE
  have hEambient : MeasurableSet E := hR.measurableSpace_le E hE
  have hsurvmeas : MeasurableSet
      {ω | t < ClockWaitingLimit.waiting (ArrivalFiltration.chronologicalArrival v) R ω} :=
    measurableSet_lt measurable_const (clock_waiting_measurable v R hR)
  calc
    _ = ∑' r : FiniteValues R, ExponentialClocks.clockMeasure V
        ((E ∩ {ω | R ω = (r.val : WithTop ℝ)}) ∩
          {ω | t < ClockWaitingLimit.waiting (ArrivalFiltration.chronologicalArrival v) R ω}) := by
      have h := slice_measure_tsum R hR hcount hfinite
        (E ∩ {ω | t < ClockWaitingLimit.waiting (ArrivalFiltration.chronologicalArrival v) R ω})
        (hEambient.inter hsurvmeas)
      simpa only [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using h.symm
    _ = ∑' r : FiniteValues R, ENNReal.ofReal (Real.exp (-t)) *
        ExponentialClocks.clockMeasure V (E ∩ {ω | R ω = (r.val : WithTop ℝ)}) := by
      apply tsum_congr
      intro r
      exact slice_joint_survival v R hR hcount r.val t (finiteValue_nonnegative R hpos r) ht E hE
    _ = _ := by
      rw [ENNReal.tsum_mul_left, slice_measure_tsum R hR hcount hfinite E hEambient]

theorem countable_clock_hasLaw [Countable V] (v : V)
    (R : ExponentialClocks.Sample V → WithTop ℝ)
    (hR : IsStoppingTime (ArrivalFiltration.clockHistory V) R)
    (hcount : (Set.range R).Countable) (hpos : ∀ ω, 0 ≤ R ω)
    (hfinite : ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, R ω ≠ ⊤) :
    HasLaw (ClockWaitingLimit.waiting (ArrivalFiltration.chronologicalArrival v) R)
      (expMeasure 1) (ExponentialClocks.clockMeasure V) :=
  SurvivalLaw.hasLaw_of_jointSurvival (clock_waiting_measurable v R hR)
    (fun _ => le_max_right _ _) hR.measurableSpace_le
    (countable_clock_jointSurvival v R hR hcount hpos hfinite)

theorem countable_clock_indep [Countable V] (v : V)
    (R : ExponentialClocks.Sample V → WithTop ℝ)
    (hR : IsStoppingTime (ArrivalFiltration.clockHistory V) R)
    (hcount : (Set.range R).Countable) (hpos : ∀ ω, 0 ≤ R ω)
    (hfinite : ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, R ω ≠ ⊤) :
    Indep ((borel ℝ).comap (ClockWaitingLimit.waiting (ArrivalFiltration.chronologicalArrival v) R))
      hR.measurableSpace (ExponentialClocks.clockMeasure V) :=
  SurvivalLaw.indep_of_jointSurvival (clock_waiting_measurable v R hR)
    (fun _ => le_max_right _ _) hR.measurableSpace_le
    (countable_clock_jointSurvival v R hR hcount hpos hfinite)

end MathResearchAnalysis.CountableClockSurvival
