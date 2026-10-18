module

public import MathResearchAnalysis.SquareAttractivity
public import MathResearchAnalysis.SquarePWDrop
public import MathResearchAnalysis.FiniteWordKernel
public import Mathlib.Topology.Order.OrderClosed

set_option autoImplicit false

/-!
# Censoring actual finite square heat-bath words from the top configuration

The actual Gibbs density is propagated through forward mass updates. A deleted
update increases stochastic order, which the remaining attractive updates
preserve. The fixed finite-word limit then yields the genuine fair-mark
execution-integral inequality. No censoring, density or probability law is an
input of the final interfaces.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace MathResearchAnalysis.SquarePWCensoring

open SquarePWMeasure

theorem density_step_monotone {n : Nat} (β : ℝ) (hβ : 0 ≤ β) (v : Site n)
    (ρ : Config n → ℝ) (hd : Monotone (density β ρ)) :
    Monotone (density β (step β v ρ)) := by
  have heq : density β (step β v ρ) = ZeroTemperature.warmStep β v (density β ρ) := by
    funext f
    exact density_step β v ρ f
  rw [heq]
  exact SquareAttractivity.warmStep_monotone β hβ v hd

/-- Density monotonicity suffices; no probability normalization is required here. -/
theorem censoring_from_density {n : Nat} (β : ℝ) (hβ : 0 ≤ β)
    {short full : List (Site n)} (sub : short.Sublist full)
    (ρ : Config n → ℝ) (hd : Monotone (density β ρ))
    (φ : Config n → ℝ) (hφ : Monotone φ) :
    expect (runMass β full ρ) φ ≤ expect (runMass β short ρ) φ := by
  induction sub generalizing ρ with
  | slnil => exact le_rfl
  | @cons short full v sub ih =>
    change expect (runMass β full (step β v ρ)) φ ≤ expect (runMass β short ρ) φ
    calc
      _ ≤ expect (runMass β short (step β v ρ)) φ :=
        ih (step β v ρ) (density_step_monotone β hβ v ρ hd)
      _ = expect (step β v ρ) (ZeroTemperature.warmWord β short φ) :=
        expect_runMass β short (step β v ρ) φ
      _ ≤ expect ρ (ZeroTemperature.warmWord β short φ) :=
        SquarePWDrop.expect_step_le_expect β v ρ hd _
          (SquareAttractivity.warmWord_monotone β hβ short hφ)
      _ = expect (runMass β short ρ) φ := (expect_runMass β short ρ φ).symm
  | @cons_cons short full v sub ih =>
    exact ih (step β v ρ) (density_step_monotone β hβ v ρ hd)

/-- Actual finite-temperature Peres--Winkler stochastic order from the top state. -/
theorem warmWord_censoring {n : Nat} (β : ℝ) (hβ : 0 ≤ β)
    {short full : List (Site n)} (sub : short.Sublist full)
    (φ : Config n → ℝ) (hφ : Monotone φ) :
    ZeroTemperature.warmWord β full φ (topConfig n) ≤
      ZeroTemperature.warmWord β short φ (topConfig n) := by
  have h := censoring_from_density β hβ sub (topMass n)
    (topMass_density_monotone n β) φ hφ
  rw [expect_runMass, expect_topMass, expect_runMass, expect_topMass] at h
  exact h

/-- Fixed finite-word zero-temperature transfer, with no law or density inputs. -/
theorem actualMajorityWordMean_censoring {n : Nat}
    {short full : List (Site n)} (sub : short.Sublist full)
    (φ : Config n → ℝ) (hφ : Monotone φ) :
    ZeroTemperature.actualMajorityWordMean full φ (topConfig n) ≤
      ZeroTemperature.actualMajorityWordMean short φ (topConfig n) := by
  apply le_of_tendsto_of_tendsto
    (ZeroTemperature.finite_word_limit_actual_majority full φ (topConfig n))
    (ZeroTemperature.finite_word_limit_actual_majority short φ (topConfig n))
  exact (eventually_ge_atTop (0 : ℝ)).mono fun β hβ => warmWord_censoring β hβ sub φ hφ

/-- Chronological event identities may repeat sites, but never reuse an identity. -/
theorem chronological_fair_execution_censoring {n : Nat}
    {short full : List (SquareSpin.Event n)} (sub : short.Sublist full)
    (unique : full.Nodup) (φ : Config n → ℝ) (hφ : Monotone φ) :
    (∫ ξ, φ (ClockExecutionLaw.freshRun full.reverse ξ (topConfig n))
      ∂FairMarks.vectorMeasure full.reverse.length) ≤
    (∫ ξ, φ (ClockExecutionLaw.freshRun short.reverse ξ (topConfig n))
      ∂FairMarks.vectorMeasure short.reverse.length) := by
  rw [FiniteWordKernel.chronological_fair_execution_mean full unique,
    FiniteWordKernel.chronological_fair_execution_mean short (unique.sublist sub)]
  exact actualMajorityWordMean_censoring (sub.map Prod.fst) φ hφ

/-- The same comparison directly in the actual finite execution measures. -/
theorem freshExecutionLaw_censoring {n : Nat}
    {short full : List (SquareSpin.Event n)} (sub : short.Sublist full)
    (unique : full.Nodup) (φ : Config n → ℝ) (hφ : Monotone φ) :
    (∫ f, φ f ∂ClockExecutionLaw.freshExecutionLaw full.reverse (topConfig n)) ≤
    (∫ f, φ f ∂ClockExecutionLaw.freshExecutionLaw short.reverse (topConfig n)) := by
  rw [FiniteWordKernel.freshExecutionLaw_integral full.reverse (List.nodup_reverse.mpr unique),
    FiniteWordKernel.freshExecutionLaw_integral short.reverse
      (List.nodup_reverse.mpr (unique.sublist sub))]
  simpa only [List.reverse_reverse] using
    actualMajorityWordMean_censoring (sub.map Prod.fst) φ hφ

end MathResearchAnalysis.SquarePWCensoring
