module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A geometric block-tail bound implies a finite expectation bound

The block-tail probabilities are explicit hypotheses.  This file does not
derive them from Markov restarts, a cellular automaton, or a clock process.
The initial expectation is an extended nonnegative Lebesgue integral; its
finiteness is proved from the tail bound, not assumed.
-/

public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace MathResearchAnalysis.BlockTail

universe u

/-- A finite arithmetic bound with no probabilistic input. -/
theorem truncation_le_blocks (t b n : ℕ) :
    min t (n * b) ≤ ∑ j ∈ Finset.range n, if j * b < t then b else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.succ_mul]
    by_cases h : n * b < t
    · rw [ite_eq_left h]
      omega
    · rw [ite_eq_right h]
      omega

/-- Every value is dominated by its count of surviving blocks times `b`. -/
theorem value_le_block_tsum (t b : ℕ) (hb : 1 ≤ b) :
    (t : ℝ≥0∞) ≤ ∑' j : ℕ, if j * b < t then (b : ℝ≥0∞) else 0 := by
  have ht : t ≤ t * b := by simpa using Nat.mul_le_mul_left t hb
  have hfinite := truncation_le_blocks t b t
  rw [Nat.min_eq_left ht] at hfinite
  have hcast : (t : ℝ≥0∞) ≤
      ∑ j ∈ Finset.range t, if j * b < t then (b : ℝ≥0∞) else 0 := by
    exact_mod_cast hfinite
  exact hcast.trans (ENNReal.sum_le_tsum (Finset.range t))

def blockWeight {Ω : Type u} (T : Ω → ℕ) (b j : ℕ) : Ω → ℝ≥0∞ :=
  fun ω => if j * b < T ω then (b : ℝ≥0∞) else 0

theorem blockWeight_indicator {Ω : Type u} (T : Ω → ℕ) (b j : ℕ) :
    blockWeight T b j =
      {ω | j * b < T ω}.indicator (fun _ => (b : ℝ≥0∞)) := by
  funext ω
  simp [blockWeight, Set.indicator]

theorem measurable_blockWeight {Ω : Type u} [MeasurableSpace Ω]
    (T : Ω → ℕ) (hT : Measurable T) (b j : ℕ) :
    Measurable (blockWeight T b j) := by
  rw [blockWeight_indicator]
  exact measurable_const.indicator (measurableSet_lt measurable_const hT)

theorem lintegral_blockWeight {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℕ) (hT : Measurable T) (b j : ℕ) :
    (∫⁻ ω, blockWeight T b j ω ∂μ) = (b : ℝ≥0∞) * μ {ω | j * b < T ω} := by
  rw [blockWeight_indicator]
  exact lintegral_indicator_const (measurableSet_lt measurable_const hT) _

/-- The genuine nonnegative expectation bound. No integrability hypothesis
    is needed, and the statement even holds for measures not normalized to 1. -/
theorem lintegral_le_two_blocks {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℕ) (hT : Measurable T) (b : ℕ) (hb : 1 ≤ b)
    (hTail : ∀ j : ℕ, μ {ω | j * b < T ω} ≤ (1 / 2 : ℝ≥0∞) ^ j) :
    (∫⁻ ω, (T ω : ℝ≥0∞) ∂μ) ≤ 2 * (b : ℝ≥0∞) := by
  calc
    (∫⁻ ω, (T ω : ℝ≥0∞) ∂μ) ≤
        ∫⁻ ω, ∑' j : ℕ, blockWeight T b j ω ∂μ :=
      lintegral_mono (fun ω => value_le_block_tsum (T ω) b hb)
    _ = ∑' j : ℕ, ∫⁻ ω, blockWeight T b j ω ∂μ :=
      lintegral_tsum (fun j => (measurable_blockWeight T hT b j).aemeasurable)
    _ = ∑' j : ℕ, (b : ℝ≥0∞) * μ {ω | j * b < T ω} := by
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
    (μ : Measure Ω) (T : Ω → ℕ) (hT : Measurable T) (b : ℕ) (hb : 1 ≤ b)
    (hTail : ∀ j : ℕ, μ {ω | j * b < T ω} ≤ (1 / 2 : ℝ≥0∞) ^ j) :
    (∫⁻ ω, (T ω : ℝ≥0∞) ∂μ) < ∞ := by
  exact (lintegral_le_two_blocks μ T hT b hb hTail).trans_lt (by finiteness)

/-- Integrability of the real-valued version follows from the proved finite
    nonnegative expectation. It is not an additional assumption. -/
theorem integrable_realCast {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℕ) (hT : Measurable T) (b : ℕ) (hb : 1 ≤ b)
    (hTail : ∀ j : ℕ, μ {ω | j * b < T ω} ≤ (1 / 2 : ℝ≥0∞) ^ j) :
    Integrable (fun ω => (T ω : ℝ)) μ := by
  have hMeas : Measurable (fun ω => (T ω : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hT
  refine ⟨hMeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => Nat.cast_nonneg (T ω))]
  simpa only [ENNReal.ofReal_natCast] using lintegral_lt_top μ T hT b hb hTail

/-- Ordinary real Bochner expectation satisfies the same bound, after its
    integrability has been derived from the geometric block-tail hypothesis. -/
theorem integral_le_two_blocks {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℕ) (hT : Measurable T) (b : ℕ) (hb : 1 ≤ b)
    (hTail : ∀ j : ℕ, μ {ω | j * b < T ω} ≤ (1 / 2 : ℝ≥0∞) ^ j) :
    (∫ ω, (T ω : ℝ) ∂μ) ≤ 2 * (b : ℝ) := by
  have hIntegrable := integrable_realCast μ T hT b hb hTail
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω => Nat.cast_nonneg (T ω))
    hIntegrable.aestronglyMeasurable]
  simp only [ENNReal.ofReal_natCast]
  have hBound := ENNReal.toReal_mono (by finiteness)
    (lintegral_le_two_blocks μ T hT b hb hTail)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast] using hBound

end MathResearchAnalysis.BlockTail
