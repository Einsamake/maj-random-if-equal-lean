module

public import MathResearchAnalysis.ClockGapReset

set_option autoImplicit false

/-!
# Almost sure absence of simultaneous clock events

The conclusion is obtained from the actual product of exponential gaps.
For events at different sites, delete one terminal gap, express equality
as that gap hitting a measurable random threshold, and integrate the zero
singleton masses of the true exponential density. Same-site events are
strictly ordered by positive gaps. No Poisson-process assertion is assumed.
-/

public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace MathResearchAnalysis.ClockNoTies

theorem exponential_singleton_measure (x : ℝ) : expMeasure 1 {x} = 0 := by
  change (volume.withDensity (gammaPDF 1 1)) {x} = 0
  simp

variable {Ω H : Type*} {mΩ : MeasurableSpace Ω} {mH : MeasurableSpace H}
  {μ : Measure Ω} {D : Ω → ℝ} {rest : Ω → H}

/-- An independent random threshold can have arbitrary sign. -/
theorem independent_threshold_eq_zero [IsProbabilityMeasure μ]
    (hD : HasLaw D (expMeasure 1) μ) (hrest : Measurable rest)
    (hindep : IndepFun D rest μ) (threshold : H → ℝ)
    (hthreshold : Measurable threshold) :
    μ {ω | D ω = threshold (rest ω)} = 0 := by
  have hprod := hindep.symm.hasLaw_prod (hasLaw_map hrest.aemeasurable) hD
  have hevent : MeasurableSet {p : H × ℝ | p.2 = threshold p.1} :=
    measurableSet_eq_fun measurable_snd (hthreshold.comp measurable_fst)
  rw [hprod.measure_eq (p := fun p : H × ℝ => p.2 = threshold p.1) hevent,
    Measure.prod_apply hevent]
  have hs : ∀ h : H,
      Prod.mk h ⁻¹' {p : H × ℝ | p.2 = threshold p.1} = {threshold h} := by
    intro h
    ext x
    simp
  simp only [hs, exponential_singleton_measure, lintegral_zero]

variable {V : Type*}

/-- The raw partial sum preceding a chosen gap uses only the other coordinates. -/
@[expose] def rawPrior (v : V) (k : Nat)
    (h : RandomThresholdSurvival.RestSample V v k) : ℝ :=
  ∑ j ∈ Finset.range k, ClockGapReset.reconstruct v k 0 h (v, j)

theorem rawPrior_measurable (v : V) (k : Nat) : Measurable (rawPrior v k) := by
  unfold rawPrior
  exact Finset.measurable_sum _ (fun j _ =>
    (measurable_pi_apply (v, j)).comp
      (ClockGapReset.reconstruct_measurable v k (fun _ => 0) measurable_const))

theorem rawPrior_rest_eq (v : V) (k : Nat) (ω : ExponentialClocks.Sample V) :
    rawPrior v k (RandomThresholdSurvival.restCoordinates v k ω) =
      ∑ j ∈ Finset.range k, ExponentialClocks.gap v j ω := by
  apply Finset.sum_congr rfl
  intro j hj
  have hne : (v, j) ≠ (v, k) := by
    intro heq
    exact (Nat.ne_of_lt (Finset.mem_range.mp hj)) (congrArg Prod.snd heq)
  rw [ClockGapReset.reconstruct_other v k 0 _ (v, j) hne]
  rfl

theorem arrival_eq_rawPrior_add_gap (v : V) (k : Nat)
    (ω : ExponentialClocks.Sample V) :
    ExponentialClocks.arrival v k ω =
      rawPrior v k (RandomThresholdSurvival.restCoordinates v k ω) +
        ExponentialClocks.gap v k ω := by
  rw [rawPrior_rest_eq]
  exact Finset.sum_range_succ _ k

theorem other_arrival_reconstruct (v w : V) (k j : Nat) (hvw : v ≠ w)
    (ω : ExponentialClocks.Sample V) :
    ExponentialClocks.arrival w j
        (ClockGapReset.reconstruct v k 0 (RandomThresholdSurvival.restCoordinates v k ω)) =
      ExponentialClocks.arrival w j ω := by
  apply Finset.sum_congr rfl
  intro a _
  have hne : (w, a) ≠ (v, k) := by
    intro heq
    exact hvw (congrArg Prod.fst heq).symm
  exact ClockGapReset.reconstruct_other v k 0 _ (w, a) hne

/-- Equality of two different sites' arrivals has zero probability. -/
theorem cross_site_arrival_eq_zero (v w : V) (k j : Nat) (hvw : v ≠ w) :
    ExponentialClocks.clockMeasure V
      {ω | ExponentialClocks.arrival v k ω = ExponentialClocks.arrival w j ω} = 0 := by
  let threshold : RandomThresholdSurvival.RestSample V v k → ℝ := fun h =>
    ExponentialClocks.arrival w j (ClockGapReset.reconstruct v k 0 h) - rawPrior v k h
  have ht : Measurable threshold :=
    ((ExponentialClocks.arrival_measurable w j).comp
      (ClockGapReset.reconstruct_measurable v k (fun _ => 0) measurable_const)).sub
        (rawPrior_measurable v k)
  have hzero := independent_threshold_eq_zero (ExponentialClocks.gap_hasLaw v k)
    (RandomThresholdSurvival.restCoordinates_measurable v k)
    (RandomThresholdSurvival.gap_independent_rest v k) threshold ht
  have heq : {ω | ExponentialClocks.arrival v k ω = ExponentialClocks.arrival w j ω} =
      {ω | ExponentialClocks.gap v k ω =
        threshold (RandomThresholdSurvival.restCoordinates v k ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, threshold, other_arrival_reconstruct v w k j hvw ω,
      arrival_eq_rawPrior_add_gap v k ω]
    constructor <;> intro h <;> linarith
  rw [heq]
  exact hzero

theorem cross_site_arrival_ne_ae (v w : V) (k j : Nat) (hvw : v ≠ w) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V,
      ExponentialClocks.arrival v k ω ≠ ExponentialClocks.arrival w j ω := by
  rw [ae_iff]
  simpa only [not_not] using cross_site_arrival_eq_zero v w k j hvw

/-- Simultaneous all-site absence of ties is a countable intersection. -/
theorem all_arrivals_injective_ae [Countable V] :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V,
      Function.Injective (fun p : V × Nat => ExponentialClocks.arrival p.1 p.2 ω) := by
  have hcross : ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ v w k j,
      v ≠ w → ExponentialClocks.arrival v k ω ≠ ExponentialClocks.arrival w j ω := by
    simp only [ae_all_iff]
    intro v w k j hvw
    exact cross_site_arrival_ne_ae v w k j hvw
  filter_upwards [hcross, ExponentialClocks.arrival_strictMono_ae (V := V)] with ω hc hm
  rintro ⟨v, k⟩ ⟨w, j⟩ heq
  by_cases hvw : v = w
  · subst w
    have hkj := (hm v).injective heq
    exact Prod.ext rfl hkj
  · exact (hc v w k j hvw heq).elim

/-- The total chronological representatives inherit genuine all-event injectivity almost surely. -/
theorem all_chronological_arrivals_injective_ae [Countable V] :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V,
      Function.Injective (fun p : V × Nat =>
        ArrivalFiltration.chronologicalArrival p.1 p.2 ω) := by
  filter_upwards [all_arrivals_injective_ae (V := V),
    ArrivalFiltration.chronologicalArrival_eq_raw_ae (V := V)] with ω hi heq
  intro p q hpq
  apply hi
  simpa only [heq] using hpq

end MathResearchAnalysis.ClockNoTies
