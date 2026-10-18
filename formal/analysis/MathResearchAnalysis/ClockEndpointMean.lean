module

public import MathResearchAnalysis.FiniteWordKernel

set_option autoImplicit false

/-!
# Actual identity-mark integration and clock endpoint averaging

Distinct identities in a fixed chronological word have the genuine finite
fair product law. Fubini then identifies the actual clock/mark endpoint mean
with its clock-wise cold-word mean, without a bound on random word length.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace MathResearchAnalysis.ClockEndpointMean

abbrev Event (n : Nat) := SquareSpin.Event n
abbrev Config (n : Nat) := SquareSpin.Config n
abbrev ClockSample (n : Nat) := ExponentialClocks.Sample (SquareTasks.Vertex n)

/-- Finite configuration-valued observables give integrable real tests. -/
theorem finite_test_integrable {n : Nat} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → Config n) (hf : Measurable f)
    (φ : Config n → ℝ) : Integrable (fun ω => φ (f ω)) μ := by
  exact (Integrable.of_finite : Integrable φ (Measure.map f μ)).comp_aemeasurable
    hf.aemeasurable

theorem marked_execute_measurable {n : Nat} (events : List (Event n))
    (initial : Config n) :
    Measurable (fun η : FairMarks.Sample (Event n) =>
      MarkedEventTrace.execute η events initial) := by
  simpa only [List.reverse_reverse] using
    ClockExecutionLaw.fixedRun_measurable events.reverse initial

/-- A fixed chronological identity word is integrated against actual infinite marks. -/
theorem integral_marked_execute_eq_coldWord {n : Nat} (events : List (Event n))
    (unique : events.Nodup) (φ : Config n → ℝ) (initial : Config n) :
    (∫ η, φ (MarkedEventTrace.execute η events initial)
      ∂FairMarks.markMeasure (Event n)) =
      ZeroTemperature.coldWord (events.map Prod.fst) φ initial := by
  have hlaw : HasLaw (ClockExecutionLaw.fixedVector events.reverse)
      (FairMarks.vectorMeasure events.reverse.length) (FairMarks.markMeasure (Event n)) :=
    FairMarks.fixedSelection_hasLaw events.reverse.get
      (List.nodup_reverse.mpr unique).injective_get
  have hm : AEStronglyMeasurable
      (fun ξ => φ (ClockExecutionLaw.freshRun events.reverse ξ initial))
      (FairMarks.vectorMeasure events.reverse.length) :=
    (measurable_of_countable _).aestronglyMeasurable
  calc
    _ = ∫ η, (fun ξ => φ (ClockExecutionLaw.freshRun events.reverse ξ initial))
        (ClockExecutionLaw.fixedVector events.reverse η)
        ∂FairMarks.markMeasure (Event n) := by
      apply integral_congr_ae
      exact ae_of_all _ fun η => by
        dsimp only
        rw [ClockExecutionLaw.freshRun_fixedVector, List.reverse_reverse]
    _ = ∫ ξ, φ (ClockExecutionLaw.freshRun events.reverse ξ initial)
        ∂FairMarks.vectorMeasure events.reverse.length := hlaw.integral_comp hm
    _ = _ := by
      rw [FiniteWordKernel.integral_freshRun_eq_coldWord events.reverse
        (List.nodup_reverse.mpr unique), List.reverse_reverse]

def wordMean (n : Nat) (t : ℝ) (φ : Config n → ℝ) (initial : Config n)
    (ω : ClockSample n) : ℝ :=
  ZeroTemperature.coldWord ((ClockEventWord.word ω t).reverse.map Prod.fst) φ initial

theorem wordMean_measurable (n : Nat) (t : ℝ) (φ : Config n → ℝ)
    (initial : Config n) : Measurable (wordMean n t φ initial) :=
  (measurable_of_countable (fun events : List (Event n) =>
    ZeroTemperature.coldWord (events.reverse.map Prod.fst) φ initial)).comp
      (ClockEventWord.word_measurable t)

theorem integral_endpoint_eq_integral_wordMean (n : Nat) (t : ℝ)
    (φ : Config n → ℝ) (initial : Config n) :
    (∫ z, φ (ClockExecutionLaw.endpoint n t initial z) ∂ClockWordMarks.measure n) =
      ∫ ω, wordMean n t φ initial ω
        ∂ExponentialClocks.clockMeasure (SquareTasks.Vertex n) := by
  have hi := finite_test_integrable (ClockWordMarks.measure n)
    (ClockExecutionLaw.endpoint n t initial)
    (ClockExecutionLaw.endpoint_measurable n t initial) φ
  change (∫ z, φ (ClockExecutionLaw.endpoint n t initial z)
      ∂(ExponentialClocks.clockMeasure (SquareTasks.Vertex n)).prod
        (FairMarks.markMeasure (Event n))) = _
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun ω =>
    integral_marked_execute_eq_coldWord (ClockEventWord.word ω t).reverse
      (List.nodup_reverse.mpr (ClockEventWord.word_nodup ω t)) φ initial

theorem wordMean_integrable (n : Nat) (t : ℝ) (φ : Config n → ℝ)
    (initial : Config n) :
    Integrable (wordMean n t φ initial)
      (ExponentialClocks.clockMeasure (SquareTasks.Vertex n)) := by
  have hi := finite_test_integrable (ClockWordMarks.measure n)
    (ClockExecutionLaw.endpoint n t initial)
    (ClockExecutionLaw.endpoint_measurable n t initial) φ
  have heq : (fun ω => ∫ η, φ (ClockExecutionLaw.endpoint n t initial (ω, η))
      ∂FairMarks.markMeasure (Event n)) = wordMean n t φ initial := by
    funext ω
    exact integral_marked_execute_eq_coldWord (ClockEventWord.word ω t).reverse
      (List.nodup_reverse.mpr (ClockEventWord.word_nodup ω t)) φ initial
  exact heq ▸ hi.integral_prod_left

end MathResearchAnalysis.ClockEndpointMean
