module

public import MathResearchAnalysis.BlockTail
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Geometric block tails for a possibly infinite recovery time

`T : Ω → ℕ∞` may take the value `∞`.  The only stochastic input is the
geometric block-tail bound; neither almost-sure finiteness nor integrability
is assumed.  Tonelli first proves the finite extended expectation, and that
result then implies that the infinite-value event has measure zero.

The block-tail hypothesis remains an explicit input.  This file does not
construct a recovery time, prove a restart argument, or instantiate a CA.
-/

public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace MathResearchAnalysis.ExtendedBlockTail

universe u

/-- Block domination includes the infinite value: infinitely many positive
    block weights have extended sum `∞`. -/
theorem value_le_block_tsum (t : ℕ∞) (b : ℕ) (hb : 1 ≤ b) :
    (t : ℝ≥0∞) ≤ ∑' j : ℕ, if ((j * b : ℕ) : ℕ∞) < t then (b : ℝ≥0∞) else 0 := by
  cases t using ENat.recTopCoe with
  | top =>
    have hb0 : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
    simp only [ENat.toENNReal_top, ENat.natCast_lt_top, ite_true,
      ENNReal.tsum_const_eq_top_of_ne_zero hb0, le_refl]
  | coe t =>
    simpa only [ENat.toENNReal_coe, ENat.natCast_lt_natCast]
      using BlockTail.value_le_block_tsum t b hb

def blockWeight {Ω : Type u} (T : Ω → ℕ∞) (b j : ℕ) : Ω → ℝ≥0∞ :=
  fun ω => if ((j * b : ℕ) : ℕ∞) < T ω then (b : ℝ≥0∞) else 0

theorem blockWeight_indicator {Ω : Type u} (T : Ω → ℕ∞) (b j : ℕ) :
    blockWeight T b j =
      {ω | ((j * b : ℕ) : ℕ∞) < T ω}.indicator (fun _ => (b : ℝ≥0∞)) := by
  funext ω
  simp [blockWeight, Set.indicator]

theorem measurableSet_blockTail {Ω : Type u} [MeasurableSpace Ω]
    (T : Ω → ℕ∞) (hT : Measurable T) (b j : ℕ) :
    MeasurableSet {ω | ((j * b : ℕ) : ℕ∞) < T ω} :=
  hT ((Set.to_countable {t : ℕ∞ | ((j * b : ℕ) : ℕ∞) < t}).measurableSet)

theorem measurable_blockWeight {Ω : Type u} [MeasurableSpace Ω]
    (T : Ω → ℕ∞) (hT : Measurable T) (b j : ℕ) :
    Measurable (blockWeight T b j) := by
  rw [blockWeight_indicator]
  exact measurable_const.indicator (measurableSet_blockTail T hT b j)

theorem measurable_ENNRealCast {Ω : Type u} [MeasurableSpace Ω]
    (T : Ω → ℕ∞) (hT : Measurable T) :
    Measurable (fun ω => (T ω : ℝ≥0∞)) :=
  (measurable_of_countable (fun t : ℕ∞ => (t : ℝ≥0∞))).comp hT

theorem lintegral_blockWeight {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℕ∞) (hT : Measurable T) (b j : ℕ) :
    (∫⁻ ω, blockWeight T b j ω ∂μ) =
      (b : ℝ≥0∞) * μ {ω | ((j * b : ℕ) : ℕ∞) < T ω} := by
  rw [blockWeight_indicator]
  exact lintegral_indicator_const (measurableSet_blockTail T hT b j) _

/-- A finite bound on the genuine extended expectation, without any prior
    finiteness assumption on `T`. The measure need not be normalized. -/
theorem lintegral_le_two_blocks {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℕ∞) (hT : Measurable T) (b : ℕ) (hb : 1 ≤ b)
    (hTail : ∀ j : ℕ, μ {ω | ((j * b : ℕ) : ℕ∞) < T ω} ≤ (1 / 2 : ℝ≥0∞) ^ j) :
    (∫⁻ ω, (T ω : ℝ≥0∞) ∂μ) ≤ 2 * (b : ℝ≥0∞) := by
  calc
    (∫⁻ ω, (T ω : ℝ≥0∞) ∂μ) ≤
        ∫⁻ ω, ∑' j : ℕ, blockWeight T b j ω ∂μ :=
      lintegral_mono (fun ω => value_le_block_tsum (T ω) b hb)
    _ = ∑' j : ℕ, ∫⁻ ω, blockWeight T b j ω ∂μ :=
      lintegral_tsum (fun j => (measurable_blockWeight T hT b j).aemeasurable)
    _ = ∑' j : ℕ, (b : ℝ≥0∞) * μ {ω | ((j * b : ℕ) : ℕ∞) < T ω} := by
      congr 1
      funext j
      exact lintegral_blockWeight μ T hT b j
    _ ≤ ∑' j : ℕ, (b : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ^ j :=
      ENNReal.tsum_le_tsum (fun j => mul_le_mul_right (hTail j) (b : ℝ≥0∞))
    _ = (b : ℝ≥0∞) * 2 := by
      rw [ENNReal.tsum_mul_left]
      congr 1
      simpa only [one_div] using ENNReal.tsum_geometric_two
    _ = 2 * (b : ℝ≥0∞) := mul_comm _ _

theorem lintegral_lt_top {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℕ∞) (hT : Measurable T) (b : ℕ) (hb : 1 ≤ b)
    (hTail : ∀ j : ℕ, μ {ω | ((j * b : ℕ) : ℕ∞) < T ω} ≤ (1 / 2 : ℝ≥0∞) ^ j) :
    (∫⁻ ω, (T ω : ℝ≥0∞) ∂μ) < ∞ := by
  exact (lintegral_le_two_blocks μ T hT b hb hTail).trans_lt (by finiteness)

/-- Almost-sure finiteness is a conclusion of the extended expectation
    bound, rather than a property encoded by a natural-number codomain. -/
theorem ae_lt_top {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℕ∞) (hT : Measurable T) (b : ℕ) (hb : 1 ≤ b)
    (hTail : ∀ j : ℕ, μ {ω | ((j * b : ℕ) : ℕ∞) < T ω} ≤ (1 / 2 : ℝ≥0∞) ^ j) :
    ∀ᵐ ω ∂μ, T ω < ⊤ := by
  have h := MeasureTheory.ae_lt_top (measurable_ENNRealCast T hT)
    (lintegral_lt_top μ T hT b hb hTail).ne
  filter_upwards [h] with ω hω
  exact ENat.toENNReal_lt_top.mp hω

/-- The unrecovered, infinite-time event has measure zero. -/
theorem measure_eq_top_zero {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℕ∞) (hT : Measurable T) (b : ℕ) (hb : 1 ≤ b)
    (hTail : ∀ j : ℕ, μ {ω | ((j * b : ℕ) : ℕ∞) < T ω} ≤ (1 / 2 : ℝ≥0∞) ^ j) :
    μ {ω | T ω = ⊤} = 0 := by
  have h := ae_lt_top μ T hT b hb hTail
  simpa only [ae_iff, not_lt, top_le_iff] using h

theorem measurable_toNat {Ω : Type u} [MeasurableSpace Ω]
    (T : Ω → ℕ∞) (hT : Measurable T) :
    Measurable (fun ω => (T ω).toNat) :=
  (measurable_of_countable ENat.toNat).comp hT

/-- The finite representative sends `∞` to zero. Its tail is smaller
    pointwise, so it inherits the same geometric bound. -/
theorem measure_toNat_tail_le {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℕ∞) (b j : ℕ) :
    μ {ω | j * b < (T ω).toNat} ≤ μ {ω | ((j * b : ℕ) : ℕ∞) < T ω} := by
  apply measure_mono
  intro ω hω
  exact (ENat.natCast_lt_natCast.mpr hω).trans_le (ENat.natCast_toNat_le_self _)

/-- After finiteness has been proved, the finite representative agrees
    with the original recovery time almost everywhere. -/
theorem ae_natCast_toNat_eq {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℕ∞) (hT : Measurable T) (b : ℕ) (hb : 1 ≤ b)
    (hTail : ∀ j : ℕ, μ {ω | ((j * b : ℕ) : ℕ∞) < T ω} ≤ (1 / 2 : ℝ≥0∞) ^ j) :
    ∀ᵐ ω ∂μ, ((T ω).toNat : ℕ∞) = T ω := by
  filter_upwards [ae_lt_top μ T hT b hb hTail] with ω hω
  exact ENat.natCast_toNat hω.ne

theorem lintegral_toNat_eq {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℕ∞) (hT : Measurable T) (b : ℕ) (hb : 1 ≤ b)
    (hTail : ∀ j : ℕ, μ {ω | ((j * b : ℕ) : ℕ∞) < T ω} ≤ (1 / 2 : ℝ≥0∞) ^ j) :
    (∫⁻ ω, ((T ω).toNat : ℝ≥0∞) ∂μ) = (∫⁻ ω, (T ω : ℝ≥0∞) ∂μ) := by
  apply lintegral_congr_ae
  filter_upwards [ae_natCast_toNat_eq μ T hT b hb hTail] with ω hω
  simpa only [ENat.toENNReal_coe] using congrArg ENat.toENNReal hω

/-- An integrable real representative for the recovery time whose
    almost-sure finiteness was proved above. -/
theorem integrable_realToNat {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℕ∞) (hT : Measurable T) (b : ℕ) (hb : 1 ≤ b)
    (hTail : ∀ j : ℕ, μ {ω | ((j * b : ℕ) : ℕ∞) < T ω} ≤ (1 / 2 : ℝ≥0∞) ^ j) :
    Integrable (fun ω => ((T ω).toNat : ℝ)) μ := by
  exact BlockTail.integrable_realCast μ (fun ω => (T ω).toNat)
    (measurable_toNat T hT) b hb
    (fun j => (measure_toNat_tail_le μ T b j).trans (hTail j))

theorem integral_realToNat_le_two_blocks {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℕ∞) (hT : Measurable T) (b : ℕ) (hb : 1 ≤ b)
    (hTail : ∀ j : ℕ, μ {ω | ((j * b : ℕ) : ℕ∞) < T ω} ≤ (1 / 2 : ℝ≥0∞) ^ j) :
    (∫ ω, ((T ω).toNat : ℝ) ∂μ) ≤ 2 * (b : ℝ) := by
  exact BlockTail.integral_le_two_blocks μ (fun ω => (T ω).toNat)
    (measurable_toNat T hT) b hb
    (fun j => (measure_toNat_tail_le μ T b j).trans (hTail j))

end MathResearchAnalysis.ExtendedBlockTail
