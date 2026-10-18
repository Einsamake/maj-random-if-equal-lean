module

public import MathResearchAnalysis.ExtendedBlockTail
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

set_option autoImplicit false

/-!
# Extended expectations of recovery times

The expectation of an `ℕ∞`-valued recovery time is its nonnegative extended
Lebesgue integral. The coercion to `ℝ≥0∞` preserves infinity. None of the
transport or monotonicity results assumes almost-sure finite recovery.

These are generic measure-theoretic interfaces. Equality of laws transports
an expectation; it does not establish a model-specific recovery bound.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace MathResearchAnalysis.ExtendedRecoveryExpectation

universe u v

variable {Ω : Type u} {Ξ : Type v} [MeasurableSpace Ω] [MeasurableSpace Ξ]

/-- Extended expectation, retaining infinite recovery times as infinity. -/
def expectation (μ : Measure Ω) (T : Ω → ℕ∞) : ℝ≥0∞ :=
  ∫⁻ ω, (T ω).toENNReal ∂μ

theorem measurable_toENNReal : Measurable ENat.toENNReal :=
  measurable_of_countable ENat.toENNReal

theorem measurable_integrand (T : Ω → ℕ∞) (hT : Measurable T) :
    Measurable (fun ω => (T ω).toENNReal) :=
  measurable_toENNReal.comp hT

/-- A recovery time's expectation depends only on its actual pushforward law. -/
theorem expectation_eq_lintegral_map (μ : Measure Ω) (T : Ω → ℕ∞)
    (hT : Measurable T) :
    expectation μ T = ∫⁻ t : ℕ∞, t.toENNReal ∂(μ.map T) := by
  exact (lintegral_map measurable_toENNReal hT).symm

theorem expectation_eq_of_map_eq (μ : Measure Ω) (ν : Measure Ξ)
    (T : Ω → ℕ∞) (S : Ξ → ℕ∞) (hT : Measurable T) (hS : Measurable S)
    (hLaw : μ.map T = ν.map S) : expectation μ T = expectation ν S := by
  rw [expectation_eq_lintegral_map μ T hT,
    expectation_eq_lintegral_map ν S hS, hLaw]

theorem expectation_mono (μ : Measure Ω) (T S : Ω → ℕ∞)
    (h : ∀ ω, T ω ≤ S ω) : expectation μ T ≤ expectation μ S := by
  exact lintegral_mono (fun ω => ENat.toENNReal_mono (h ω))

/-- Change of sample space along a measurable map, proved by `lintegral_map`. -/
theorem expectation_precompose (μ : Measure Ω) (f : Ω → Ξ) (hf : Measurable f)
    (T : Ξ → ℕ∞) (hT : Measurable T) :
    expectation μ (T ∘ f) = expectation (μ.map f) T := by
  exact (lintegral_map (measurable_integrand T hT) hf).symm

theorem expectation_const (μ : Measure Ω) (t : ℕ∞) :
    expectation μ (fun _ => t) = t.toENNReal * μ Set.univ := by
  exact lintegral_const t.toENNReal

theorem expectation_zero (μ : Measure Ω) :
    expectation μ (fun _ => 0) = 0 := by
  simp [expectation_const]

end MathResearchAnalysis.ExtendedRecoveryExpectation
