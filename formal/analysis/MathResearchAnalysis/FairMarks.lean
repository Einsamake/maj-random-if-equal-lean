module

public import MathResearchAnalysis.ExponentialClocks
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false

/-!
# Actual independent fair marks and clock-only selection

The mark measure is an actual infinite product of fair Bernoulli measures.
Selections are functions of a separate clock sample, not of mark outcomes.
The finite selected-vector factorization is proved by product integration;
injectivity is a structural requirement preventing reuse of an event mark.
This module does not assert a censoring theorem or a CA absorption bound.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace MathResearchAnalysis.FairMarks

def fair : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance fair_probability : IsProbabilityMeasure fair := by
  constructor
  norm_num [fair]
  change ((2 : ℝ≥0) : ℝ≥0∞)⁻¹ + ((2 : ℝ≥0) : ℝ≥0∞)⁻¹ = (1 : ℝ≥0∞)
  rw [← ENNReal.coe_inv, ← ENNReal.coe_add]
  exact_mod_cast (by norm_num : (2 : ℝ≥0)⁻¹ + (2 : ℝ≥0)⁻¹ = 1)
  all_goals norm_num

theorem fair_singleton (b : Bool) : fair {b} = (2 : ℝ≥0∞)⁻¹ := by
  cases b <;> norm_num [fair]

abbrev Sample (I : Type*) := I → Bool

def markMeasure (I : Type*) : Measure (Sample I) :=
  Measure.infinitePi (fun _ : I => fair)

instance markMeasure_probability (I : Type*) : IsProbabilityMeasure (markMeasure I) := by
  unfold markMeasure
  infer_instance

def vectorMeasure (r : Nat) : Measure (Fin r → Bool) := markMeasure (Fin r)

instance vectorMeasure_probability (r : Nat) : IsProbabilityMeasure (vectorMeasure r) := by
  unfold vectorMeasure
  infer_instance

variable {I : Type*}

theorem mark_hasLaw (i : I) :
    HasLaw (fun η : Sample I => η i) fair (markMeasure I) where
  aemeasurable := (measurable_pi_apply i).aemeasurable
  map_eq := Measure.infinitePi_map_eval _ i

theorem marks_independent :
    iIndepFun (fun i : I => fun η : Sample I => η i) (markMeasure I) := by
  exact iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)

def fixedSelection {r : Nat} (j : Fin r → I) (η : Sample I) : Fin r → Bool :=
  fun k => η (j k)

theorem fixedSelection_measurable {r : Nat} (j : Fin r → I) :
    Measurable (fixedSelection j) := measurable_pi_iff.mpr fun k => measurable_pi_apply (j k)

theorem fixedSelection_hasLaw {r : Nat} (j : Fin r → I) (hj : Function.Injective j) :
    HasLaw (fixedSelection j) (vectorMeasure r) (markMeasure I) where
  aemeasurable := (fixedSelection_measurable j).aemeasurable
  map_eq := Measure.map_infinitePi_infinitePi_of_inj hj

variable {Ω : Type*} [MeasurableSpace Ω]
  [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I]

def selected {r : Nat} (j : Ω → Fin r → I) (z : Ω × Sample I) : Fin r → Bool :=
  fixedSelection (j z.1) z.2

theorem evaluation_measurable :
    Measurable (fun z : I × Sample I => z.2 z.1) := by
  exact measurable_from_prod_countable_right fun i => measurable_pi_apply i

theorem selected_measurable {r : Nat} (j : Ω → Fin r → I) (hj : Measurable j) :
    Measurable (selected j) := by
  apply measurable_pi_iff.mpr
  intro k
  exact evaluation_measurable.comp
    (((measurable_pi_apply k).comp (hj.comp measurable_fst)).prodMk measurable_snd)

/-- Joint event factorization on any clock event where selected identities are distinct.
The hypothesis is event-identity injectivity, not a probability-law conclusion. -/
theorem selected_joint_measure {r : Nat} (μ : Measure Ω)
    (j : Ω → Fin r → I) (hj : Measurable j) (E : Set Ω) (hE : MeasurableSet E)
    (hinj : ∀ᵐ ω ∂μ, ω ∈ E → Function.Injective (j ω))
    (B : Set (Fin r → Bool)) (hB : MeasurableSet B) :
    (μ.prod (markMeasure I)) {z | z.1 ∈ E ∧ selected j z ∈ B} =
      μ E * vectorMeasure r B := by
  have hset : MeasurableSet {z : Ω × Sample I | z.1 ∈ E ∧ selected j z ∈ B} :=
    (measurable_fst hE).inter ((selected_measurable j hj) hB)
  rw [Measure.prod_apply hset]
  calc
    _ = ∫⁻ ω, E.indicator (fun _ => vectorMeasure r B) ω ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hinj] with ω hω
      by_cases hmem : ω ∈ E
      · have hlaw := (fixedSelection_hasLaw (j ω) (hω hmem)).measure_eq
          (p := fun x => x ∈ B) hB
        have hslice : Prod.mk ω ⁻¹' {z | z.1 ∈ E ∧ selected j z ∈ B} =
            {η | fixedSelection (j ω) η ∈ B} := by
          ext η
          simp [selected, hmem]
        rw [hslice, Set.indicator_of_mem hmem]
        simpa only [Set.ofPred_mem_eq] using hlaw
      · simp [hmem, Set.indicator_of_notMem]
    _ = μ E * vectorMeasure r B := by
      rw [lintegral_indicator hE]
      simp [mul_comm]

theorem selected_hasLaw {r : Nat} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (j : Ω → Fin r → I) (hj : Measurable j)
    (hinj : ∀ᵐ ω ∂μ, Function.Injective (j ω)) :
    HasLaw (selected j) (vectorMeasure r) (μ.prod (markMeasure I)) where
  aemeasurable := (selected_measurable j hj).aemeasurable
  map_eq := by
    ext B hB
    rw [Measure.map_apply (selected_measurable j hj) hB]
    have h := selected_joint_measure μ j hj Set.univ MeasurableSet.univ
      (hinj.mono fun _ h _ => h) B hB
    rw [show selected j ⁻¹' B = {z | selected j z ∈ B} by ext z; simp]
    simpa only [Set.mem_univ, true_and, measure_univ, one_mul] using h

theorem selected_indep_clock {r : Nat} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (j : Ω → Fin r → I) (hj : Measurable j)
    (hinj : ∀ᵐ ω ∂μ, Function.Injective (j ω)) :
    IndepFun (fun z : Ω × Sample I => z.1) (selected j) (μ.prod (markMeasure I)) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro E B hE hB
  have h := selected_joint_measure μ j hj E hE (hinj.mono fun _ h _ => h) B hB
  have hclock : (μ.prod (markMeasure I)) ((fun z : Ω × Sample I => z.1) ⁻¹' E) = μ E := by
    rw [show (fun z : Ω × Sample I => z.1) ⁻¹' E = E ×ˢ Set.univ by ext z; simp]
    rw [Measure.prod_prod]
    simp
  have hmark : (μ.prod (markMeasure I)) (selected j ⁻¹' B) = vectorMeasure r B := by
    have hlaw := (selected_hasLaw μ j hj hinj).measure_eq (p := fun x => x ∈ B) hB
    rw [show selected j ⁻¹' B = {z | selected j z ∈ B} by ext z; simp]
    simpa only [Set.ofPred_mem_eq] using hlaw
  rw [hclock, hmark,
    show (fun z : Ω × Sample I => z.1) ⁻¹' E ∩ selected j ⁻¹' B =
      {z | z.1 ∈ E ∧ selected j z ∈ B} by ext z; simp]
  exact h

end MathResearchAnalysis.FairMarks
