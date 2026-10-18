module

public import MathResearchAnalysis.ExponentialMemoryless
public import MathResearchAnalysis.ExponentialClocks

set_option autoImplicit false

/-!
# Survival across an independent random threshold

This proves factorization for a nonnegative random threshold measurable
from coordinates independent of the current exponential gap. The actual
clock instance permits dependence on every other coordinate, including all
other sites. It does not assert that arbitrary clock-history readiness has
this independence or this functional representation.
-/

public noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace MathResearchAnalysis.RandomThresholdSurvival

variable {Ω H : Type*} {mΩ : MeasurableSpace Ω} {mH : MeasurableSpace H}
  {μ : Measure Ω} {D : Ω → ℝ} {past : Ω → H}

/-- The true survival probability is the product-law integral over the random threshold. -/
theorem joint_survival_formula [IsProbabilityMeasure μ]
    (hD : HasLaw D (expMeasure 1) μ) (hpast : Measurable past)
    (hindep : IndepFun D past μ) (threshold : H → ℝ)
    (hthreshold : Measurable threshold) (hnonneg : ∀ h, 0 ≤ threshold h)
    (B : Set H) (hB : MeasurableSet B) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | past ω ∈ B ∧ threshold (past ω) + t < D ω} =
      ∫⁻ h, B.indicator (fun h => ENNReal.ofReal (exp (-(threshold h + t)))) h
        ∂μ.map past := by
  have hprod := hindep.symm.hasLaw_prod (hasLaw_map hpast.aemeasurable) hD
  have hevent : MeasurableSet
      {p : H × ℝ | p.1 ∈ B ∧ threshold p.1 + t < p.2} :=
    (hB.preimage measurable_fst).inter
      (measurableSet_lt ((hthreshold.comp measurable_fst).add_const t) measurable_snd)
  rw [hprod.measure_eq (p := fun p : H × ℝ => p.1 ∈ B ∧ threshold p.1 + t < p.2) hevent,
    Measure.prod_apply hevent]
  apply lintegral_congr
  intro h
  by_cases hh : h ∈ B
  · have hs : Prod.mk h ⁻¹' {p : H × ℝ | p.1 ∈ B ∧ threshold p.1 + t < p.2} =
        Ioi (threshold h + t) := by ext x; simp [hh]
    rw [hs, ExponentialMemoryless.tail_measure (add_nonneg (hnonneg h) ht)]
    exact (Set.indicator_of_mem hh
      (fun h : H => ENNReal.ofReal (exp (-(threshold h + t))))).symm
  · have hs : Prod.mk h ⁻¹' {p : H × ℝ | p.1 ∈ B ∧ threshold p.1 + t < p.2} =
        ∅ := by ext x; simp [hh]
    rw [hs, measure_empty, Set.indicator_of_notMem hh]

/-- Memoryless survival remains valid for thresholds depending on an independent history.
No division by a possibly zero conditioning-event mass is used. -/
theorem independent_random_threshold_factorization [IsProbabilityMeasure μ]
    (hD : HasLaw D (expMeasure 1) μ) (hpast : Measurable past)
    (hindep : IndepFun D past μ) (threshold : H → ℝ)
    (hthreshold : Measurable threshold) (hnonneg : ∀ h, 0 ≤ threshold h)
    (B : Set H) (hB : MeasurableSet B) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | past ω ∈ B ∧ threshold (past ω) + t < D ω} =
      ENNReal.ofReal (exp (-t)) *
        μ {ω | past ω ∈ B ∧ threshold (past ω) < D ω} := by
  rw [joint_survival_formula hD hpast hindep threshold hthreshold hnonneg B hB ht]
  have hbase := joint_survival_formula hD hpast hindep threshold hthreshold hnonneg B hB
    (le_refl (0 : ℝ))
  simp only [add_zero] at hbase
  rw [hbase]
  calc
    _ = ∫⁻ h, ENNReal.ofReal (exp (-t)) *
        B.indicator (fun h => ENNReal.ofReal (exp (-threshold h))) h ∂μ.map past := by
      apply lintegral_congr
      intro h
      by_cases hh : h ∈ B
      · simp only [Set.indicator_of_mem hh, neg_add_rev, exp_add,
          ENNReal.ofReal_mul (exp_pos _).le]
      · simp only [Set.indicator_of_notMem hh, mul_zero]
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- All coordinates except a chosen exponential gap, with their full product sigma-algebra. -/
abbrev RestSample (V : Type*) (v : V) (k : Nat) :=
  {i : V × Nat // i ≠ (v, k)} → ℝ

@[expose] def restCoordinates {V : Type*} (v : V) (k : Nat)
    (ω : ExponentialClocks.Sample V) : RestSample V v k := fun i => ω i

theorem restCoordinates_measurable {V : Type*} (v : V) (k : Nat) :
    Measurable (restCoordinates v k) :=
  Measurable.of_eval (fun i => measurable_pi_apply (i : V × Nat))

/-- Independence of the chosen gap from all remaining coordinates is proved from the true model. -/
theorem gap_independent_rest {V : Type*} (v : V) (k : Nat) :
    IndepFun (ExponentialClocks.gap v k) (restCoordinates v k)
      (ExponentialClocks.clockMeasure V) := by
  let S : Set (V × Nat) := {(v, k)}
  let T : Set (V × Nat) := {i | i ≠ (v, k)}
  have hd : Disjoint S T := by
    apply Set.disjoint_left.mpr
    intro i hi hj
    exact hj (Set.mem_singleton_iff.mp hi)
  have hi := (ExponentialClocks.gaps_independent (V := V)).indepFun_set S T hd
    (fun i => measurable_pi_apply i)
  have hextract : Measurable (fun f : S → ℝ => f ⟨(v, k), Set.mem_singleton _⟩) :=
    measurable_pi_apply _
  exact hi.comp hextract measurable_id

/-- A real exponential clock gap satisfies the random-threshold factorization with no law
or independence premise; the threshold may use every coordinate except that gap. -/
theorem actual_gap_survival_factorization {V : Type*} (v : V) (k : Nat)
    (threshold : RestSample V v k → ℝ) (hthreshold : Measurable threshold)
    (hnonneg : ∀ h, 0 ≤ threshold h) (B : Set (RestSample V v k))
    (hB : MeasurableSet B) {t : ℝ} (ht : 0 ≤ t) :
    ExponentialClocks.clockMeasure V
      {ω | restCoordinates v k ω ∈ B ∧
        threshold (restCoordinates v k ω) + t < ExponentialClocks.gap v k ω} =
      ENNReal.ofReal (exp (-t)) * ExponentialClocks.clockMeasure V
        {ω | restCoordinates v k ω ∈ B ∧
          threshold (restCoordinates v k ω) < ExponentialClocks.gap v k ω} :=
  independent_random_threshold_factorization (ExponentialClocks.gap_hasLaw v k)
    (restCoordinates_measurable v k) (gap_independent_rest v k)
    threshold hthreshold hnonneg B hB ht

end MathResearchAnalysis.RandomThresholdSurvival
