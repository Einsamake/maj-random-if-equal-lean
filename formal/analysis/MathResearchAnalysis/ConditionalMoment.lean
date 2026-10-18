module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false

/-!
# Fixed-path conditional exponential moments

This file proves the tower/pull-out argument itself.  The conditional moment
of an individual waiting time and the integrability of finite exponential
prefixes are explicit hypotheses.  No Poisson process, strong Markov theorem,
censoring theorem, or Ising extinction estimate is asserted here.

`ℱ : Filtration Nat mΩ` is an explicit increasing family of sub-σ-algebras.
In particular, the proof does not infer a conditioning σ-algebra from a name
such as "the past", nor replace a conditional expectation by independence.
-/

public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.ConditionalMoment

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Total-expectation and pull-out step for a measurable previous factor. -/
theorem integral_mul_of_condExp_const [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (f g : Ω → ℝ) (constant : ℝ)
    (hf : StronglyMeasurable[m] f)
    (hfg : Integrable (fun ω => f ω * g ω) μ) (hg : Integrable g μ)
    (hconditional : μ[g | m] =ᵐ[μ] fun _ => constant) :
    (∫ ω, f ω * g ω ∂μ) = (∫ ω, f ω ∂μ) * constant := by
  have hpull : μ[f * g | m] =ᵐ[μ] f * μ[g | m] :=
    condExp_mul_of_stronglyMeasurable_left hf hfg hg
  have heq : μ[f * g | m] =ᵐ[μ] fun ω => f ω * constant := by
    filter_upwards [hpull, hconditional] with ω hp hc
    simpa only [Pi.mul_apply, hc] using hp
  calc
    (∫ ω, f ω * g ω ∂μ) = ∫ ω, (μ[f * g | m]) ω ∂μ :=
      (integral_condExp hm).symm
    _ = ∫ ω, f ω * constant ∂μ := integral_congr_ae heq
    _ = (∫ ω, f ω ∂μ) * constant := by rw [integral_mul_const]

/-- Sum of the first `n` waits along a fixed, preselected logical path. -/
@[expose] def prefixSum (wait : Nat → Ω → ℝ) : Nat → Ω → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun ω => prefixSum wait n ω + wait n ω

/-- Exponential of a finite path-prefix sum. -/
@[expose] def pathExp (θ : ℝ) (wait : Nat → Ω → ℝ) (n : Nat) : Ω → ℝ :=
  fun ω => Real.exp (θ * prefixSum wait n ω)

theorem pathExp_succ (θ : ℝ) (wait : Nat → Ω → ℝ) (n : Nat) :
    pathExp θ wait (n + 1) =
      pathExp θ wait n * (fun ω => Real.exp (θ * wait n ω)) := by
  funext ω
  simp only [pathExp, prefixSum, mul_add, Real.exp_add, Pi.mul_apply]

/--
Individual waits known by the next filtration level make every previous
prefix measurable when the next waiting time is conditioned.
-/
theorem prefixSum_stronglyMeasurable (ℱ : Filtration Nat mΩ)
    (wait : Nat → Ω → ℝ) (length : Nat)
    (hknown : ∀ i < length, StronglyMeasurable[ℱ (i + 1)] (wait i)) :
    ∀ n ≤ length, StronglyMeasurable[ℱ n] (prefixSum wait n) := by
  intro n
  induction n with
  | zero => intro _; exact stronglyMeasurable_const
  | succ n ih =>
      intro hn
      have hprevious : n ≤ length := (Nat.le_succ n).trans hn
      have hp := (ih hprevious).mono (ℱ.mono (Nat.le_succ n))
      exact hp.add (hknown n (Nat.lt_of_succ_le hn))

theorem pathExp_stronglyMeasurable (ℱ : Filtration Nat mΩ)
    (θ : ℝ) (wait : Nat → Ω → ℝ) (length : Nat)
    (hknown : ∀ i < length, StronglyMeasurable[ℱ (i + 1)] (wait i))
    {n : Nat} (hn : n ≤ length) :
    StronglyMeasurable[ℱ n] (pathExp θ wait n) := by
  have hp := prefixSum_stronglyMeasurable ℱ wait length hknown n hn
  exact Real.continuous_exp.comp_stronglyMeasurable
    (stronglyMeasurable_const.mul hp)

/--
Finite-path tower induction, without assuming independence of all waits.

`hprefixInt` supplies only integrability, never the desired integral value.
In a Poisson application its proof is a remaining analytic obligation, in
addition to the strong-Markov proof of `hconditional`.
-/
theorem fixed_path_exponential_moment [IsProbabilityMeasure μ]
    (ℱ : Filtration Nat mΩ) (θ constant : ℝ)
    (wait : Nat → Ω → ℝ) (length : Nat)
    (hknown : ∀ i < length, StronglyMeasurable[ℱ (i + 1)] (wait i))
    (hwaitInt : ∀ i < length, Integrable (fun ω => Real.exp (θ * wait i ω)) μ)
    (hprefixInt : ∀ n ≤ length, Integrable (pathExp θ wait n) μ)
    (hconditional : ∀ i < length,
      μ[(fun ω => Real.exp (θ * wait i ω)) | ℱ i] =ᵐ[μ] fun _ => constant) :
    (∫ ω, Real.exp (θ * prefixSum wait length ω) ∂μ) = constant ^ length := by
  suffices h : ∀ n ≤ length, (∫ ω, pathExp θ wait n ω ∂μ) = constant ^ n by
    exact h length le_rfl
  intro n
  induction n with
  | zero => intro _; simp [pathExp, prefixSum]
  | succ n ih =>
      intro hn
      have hlt : n < length := Nat.lt_of_succ_le hn
      have hle : n ≤ length := (Nat.le_succ n).trans hn
      have hpmeas := pathExp_stronglyMeasurable ℱ θ wait length hknown hle
      have hprod : Integrable
          (fun ω => pathExp θ wait n ω * Real.exp (θ * wait n ω)) μ := by
        simpa only [pathExp_succ, Pi.mul_def] using hprefixInt (n + 1) hn
      rw [pathExp_succ, Pi.mul_def]
      rw [integral_mul_of_condExp_const (ℱ.le n) (pathExp θ wait n)
        (fun ω => Real.exp (θ * wait n ω)) constant hpmeas hprod
        (hwaitInt n hlt) (hconditional n hlt)]
      rw [ih hle, pow_succ]

/-- The rate-one exponential conditional-moment value used in formula (11). -/
theorem fixed_path_rate_one_moment [IsProbabilityMeasure μ]
    (ℱ : Filtration Nat mΩ) (θ : ℝ) (wait : Nat → Ω → ℝ) (length : Nat)
    (hknown : ∀ i < length, StronglyMeasurable[ℱ (i + 1)] (wait i))
    (hwaitInt : ∀ i < length, Integrable (fun ω => Real.exp (θ * wait i ω)) μ)
    (hprefixInt : ∀ n ≤ length, Integrable (pathExp θ wait n) μ)
    (hconditional : ∀ i < length,
      μ[(fun ω => Real.exp (θ * wait i ω)) | ℱ i] =ᵐ[μ]
        fun _ => (1 - θ)⁻¹) :
    (∫ ω, Real.exp (θ * prefixSum wait length ω) ∂μ) = ((1 - θ)⁻¹) ^ length :=
  fixed_path_exponential_moment ℱ θ ((1 - θ)⁻¹) wait length
    hknown hwaitInt hprefixInt hconditional

end MathResearchAnalysis.ConditionalMoment
