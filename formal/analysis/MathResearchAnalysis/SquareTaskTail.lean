module

public import MathResearchAnalysis.SquareTasks
public import MathResearchAnalysis.TaskPathTail
public import MathResearchAnalysis.ExponentialMoment

set_option autoImplicit false

/-!
# The concrete square task tail

All graph, coloring, path closure, successor coverage and degree inputs are
proved by `SquareTasks`. Single-step waiting conditions still require the
stochastic clock model; no Poisson strong Markov theorem is asserted here.
-/

public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.SquareTaskTail

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem square_prefix_half_tail (n : Nat) (c : Bool) (k : Nat)
    (delay : Nat → SquareTasks.Vertex n → Ω → ℝ)
    (filtration : List (SquareTasks.Vertex n) → Filtration Nat mΩ)
    (nonnegative : ∀ ω j v, 0 ≤ delay j v ω) (threshold : ℝ)
    (hknown : ∀ p ∈ (SquareTasks.system n).terminalPaths (SquareTasks.tasks n c k) k,
      ∀ i < k + 1, StronglyMeasurable[filtration p (i + 1)] (TaskPathTail.pathWait delay p i))
    (hwaitInt : ∀ p ∈ (SquareTasks.system n).terminalPaths (SquareTasks.tasks n c k) k,
      ∀ i < k + 1, Integrable
        (fun ω => Real.exp ((1 / 2 : ℝ) * TaskPathTail.pathWait delay p i ω)) μ)
    (hconditional : ∀ p ∈ (SquareTasks.system n).terminalPaths (SquareTasks.tasks n c k) k,
      ∀ i < k + 1, μ[(fun ω => Real.exp ((1 / 2 : ℝ) * TaskPathTail.pathWait delay p i ω)) |
        filtration p i] =ᵐ[μ] fun _ => 2) :
    MeasurableSet {ω | threshold < (SquareTasks.system n).prefixMaximum
        (SquareTasks.tasks n c) (SquareTasks.tasks_nonempty n c) (fun i v => delay i v ω) k} ∧
      μ.real {ω | threshold < (SquareTasks.system n).prefixMaximum
        (SquareTasks.tasks n c) (SquareTasks.tasks_nonempty n c) (fun i v => delay i v ω) k} ≤
        (n + 2 : ℝ) ^ 2 * (4 : ℝ) ^ k * (2 : ℝ) ^ (k + 1) * Real.exp (-threshold / 2) := by
  have h := TaskPathTail.prefix_degree_half_tail (SquareTasks.system n)
    (SquareTasks.tasks n c) (SquareTasks.tasks_nonempty n c) delay filtration nonnegative
    (SquareTasks.successor_coverage n c) 4 k (SquareTasks.predecessor_degree n) threshold
    hknown hwaitInt hconditional
  refine ⟨h.1, h.2.trans ?_⟩
  have hc : ((SquareTasks.tasks n c k).card : ℝ) ≤ (n + 2 : ℝ) ^ 2 := by
    exact_mod_cast SquareTasks.tasks_card_le n c k
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)) (Real.exp_pos _).le

theorem four_two_coefficient_le_eight (k : Nat) :
    (4 : ℝ) ^ k * (2 : ℝ) ^ (k + 1) ≤ (8 : ℝ) ^ (k + 1) := by
  calc
    (4 : ℝ) ^ k * (2 : ℝ) ^ (k + 1) = ((4 : ℝ) * 2) ^ k * 2 := by
      rw [mul_pow, pow_succ]
      ring
    _ = (8 : ℝ) ^ k * 2 := by norm_num
    _ ≤ (8 : ℝ) ^ k * 8 := mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
    _ = (8 : ℝ) ^ (k + 1) := (pow_succ _ _).symm

/-- Concrete geometry and actual exponential laws give the stated square tail.
Independence from each readiness history is still a model obligation; it is
not inferred from independence of the underlying clock interarrival coordinates. -/
theorem square_prefix_eight_tail_of_law_indep (n : Nat) (c : Bool) (k : Nat)
    (delay : Nat → SquareTasks.Vertex n → Ω → ℝ)
    (filtration : List (SquareTasks.Vertex n) → Filtration Nat mΩ)
    (nonnegative : ∀ ω j v, 0 ≤ delay j v ω) (threshold : ℝ)
    (hknown : ∀ p ∈ (SquareTasks.system n).terminalPaths (SquareTasks.tasks n c k) k,
      ∀ i < k + 1, StronglyMeasurable[filtration p (i + 1)] (TaskPathTail.pathWait delay p i))
    (hlaw : ∀ p ∈ (SquareTasks.system n).terminalPaths (SquareTasks.tasks n c k) k,
      ∀ i < k + 1, ProbabilityTheory.HasLaw (TaskPathTail.pathWait delay p i)
        (ProbabilityTheory.expMeasure 1) μ)
    (hindep : ∀ p ∈ (SquareTasks.system n).terminalPaths (SquareTasks.tasks n c k) k,
      ∀ i < k + 1, ProbabilityTheory.Indep
        ((borel ℝ).comap (TaskPathTail.pathWait delay p i)) (filtration p i) μ) :
    MeasurableSet {ω | threshold < (SquareTasks.system n).prefixMaximum
        (SquareTasks.tasks n c) (SquareTasks.tasks_nonempty n c) (fun i v => delay i v ω) k} ∧
      μ.real {ω | threshold < (SquareTasks.system n).prefixMaximum
        (SquareTasks.tasks n c) (SquareTasks.tasks_nonempty n c) (fun i v => delay i v ω) k} ≤
        (n + 2 : ℝ) ^ 2 * (8 : ℝ) ^ (k + 1) * Real.exp (-threshold / 2) := by
  have h := square_prefix_half_tail n c k delay filtration nonnegative threshold hknown
    (fun p hp i hi => ExponentialMoment.integrable_of_hasLaw
      (by norm_num : (1 / 2 : ℝ) < 1) (hlaw p hp i hi))
    (fun p hp i hi => ExponentialMoment.condExp_half_of_hasLaw_indep (hlaw p hp i hi)
      (((hknown p hp i hi).mono ((filtration p).le (i + 1))).measurable)
      ((filtration p).le i) (hindep p hp i hi))
  refine ⟨h.1, h.2.trans ?_⟩
  have hc := four_two_coefficient_le_eight k
  have hm : 0 ≤ (n + 2 : ℝ) ^ 2 := by positivity
  have hprod := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hm)
    (Real.exp_pos (-threshold / 2)).le
  simpa only [mul_assoc] using hprod

end MathResearchAnalysis.SquareTaskTail
