module

public import MathResearchAnalysis.ExtendedRecoveryExpectation

set_option autoImplicit false

/-!
# Lower bounds for genuine extended recovery expectations

A lower bound for one measurable survival event gives a lower bound for
its extended expectation. Infinite recovery times remain infinite throughout;
no integrability or almost-sure finiteness is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace MathResearchAnalysis.ExtendedTailLower

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- A single survival event pays its time threshold in the extended integral. -/
theorem tail_mul_le_expectation (μ : Measure Ω) (T : Ω → ℕ∞)
    (hT : Measurable T) (k : Nat) :
    (k : ℝ≥0∞) * μ {ω | (k : ℕ∞) < T ω} ≤
      ExtendedRecoveryExpectation.expectation μ T := by
  have hm : MeasurableSet {ω | (k : ℕ∞) < T ω} :=
    by simpa only [Nat.one_mul] using ExtendedBlockTail.measurableSet_blockTail T hT k 1
  calc
    (k : ℝ≥0∞) * μ {ω | (k : ℕ∞) < T ω} =
        ∫⁻ ω, {ω | (k : ℕ∞) < T ω}.indicator (fun _ => (k : ℝ≥0∞)) ω ∂μ :=
      (lintegral_indicator_const hm _).symm
    _ ≤ ExtendedRecoveryExpectation.expectation μ T := by
      apply lintegral_mono
      intro ω
      by_cases hω : (k : ℕ∞) < T ω
      · have he := Set.indicator_of_mem hω (fun _ => (k : ℝ≥0∞))
        exact he.le.trans (ENat.toENNReal_mono hω.le)
      · have he := Set.indicator_of_notMem hω (fun _ => (k : ℝ≥0∞))
        exact he.le.trans bot_le

/-- This implication needs only finite event mass, not a finite recovery mean. -/
theorem expectation_ge_quarter (μ : Measure Ω) [IsFiniteMeasure μ]
    (T : Ω → ℕ∞) (hT : Measurable T) (k : Nat)
    (hprob : (1/4 : Real) ≤ μ.real {ω | (k : ℕ∞) < T ω}) :
    ENNReal.ofReal ((k : Real)/4) ≤ ExtendedRecoveryExpectation.expectation μ T := by
  have hp : ENNReal.ofReal (1/4 : Real) ≤ μ {ω | (k : ℕ∞) < T ω} := by
    exact (ENNReal.ofReal_le_ofReal hprob).trans (le_of_eq (ofReal_measureReal (measure_ne_top μ _)))
  calc
    ENNReal.ofReal ((k : Real)/4) = (k : ℝ≥0∞) * ENNReal.ofReal (1/4 : Real) := by
      rw [div_eq_mul_inv, ENNReal.ofReal_mul (Nat.cast_nonneg k), ENNReal.ofReal_natCast]
      norm_num
    _ ≤ (k : ℝ≥0∞) * μ {ω | (k : ℕ∞) < T ω} := mul_le_mul_right hp _
    _ ≤ ExtendedRecoveryExpectation.expectation μ T := tail_mul_le_expectation μ T hT k

/-- A real quantitative threshold transports into the extended expectation. -/
theorem expectation_ge_of_quarter_tail (μ : Measure Ω) [IsFiniteMeasure μ]
    (T : Ω → ℕ∞) (hT : Measurable T) (k : Nat)
    (hprob : (1/4 : Real) ≤ μ.real {ω | (k : ℕ∞) < T ω})
    (a : Real) (ha : a ≤ (k : Real)/4) :
    ENNReal.ofReal a ≤ ExtendedRecoveryExpectation.expectation μ T :=
  (ENNReal.ofReal_le_ofReal ha).trans (expectation_ge_quarter μ T hT k hprob)

end MathResearchAnalysis.ExtendedTailLower

