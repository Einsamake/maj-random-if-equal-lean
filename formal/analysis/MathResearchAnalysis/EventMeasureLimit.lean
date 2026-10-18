module

public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

set_option autoImplicit false

/-!
# Convergence of finite-measure events from almost-sure eventual membership

The bound is the constant one. Exceptional sample paths are kept in the
events and then handled by almost-sure convergence, rather than removed by
definition or replaced with a preassigned finite random variable.
-/

public noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace MathResearchAnalysis.EventMeasureLimit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

theorem event_measure_tendsto (events : Nat → Set Ω) (target : Set Ω)
    (hmeas : ∀ n, MeasurableSet (events n)) (htarget : MeasurableSet target)
    (hevent : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, (ω ∈ events n ↔ ω ∈ target)) :
    Tendsto (fun n => μ (events n)) atTop (𝓝 (μ target)) := by
  let F : Nat → Ω → ℝ≥0∞ := fun n => (events n).indicator (fun _ => 1)
  let f : Ω → ℝ≥0∞ := target.indicator (fun _ => 1)
  have hF : ∀ n, Measurable (F n) := fun n => measurable_const.indicator (hmeas n)
  have hbound : ∀ n, F n ≤ᵐ[μ] fun _ => (1 : ℝ≥0∞) := by
    intro n
    apply Filter.Eventually.of_forall
    intro ω
    by_cases hω : ω ∈ events n <;> simp [F, hω]
  have hfinite : (∫⁻ ω, (1 : ℝ≥0∞) ∂μ) ≠ ⊤ := by simp
  have hlimit : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 (f ω)) := by
    filter_upwards [hevent] with ω hω
    have heq : (fun n => F n ω) =ᶠ[atTop] fun _ => f ω := by
      filter_upwards [hω] with n hn
      by_cases ht : ω ∈ target <;> simp [F, f, hn, ht]
    exact (tendsto_congr' heq).mpr tendsto_const_nhds
  have h := tendsto_lintegral_of_dominated_convergence (fun _ => (1 : ℝ≥0∞))
    hF hbound hfinite hlimit
  simpa only [F, f, lintegral_indicator_const (hmeas _),
    lintegral_indicator_const htarget, one_mul] using h

end MathResearchAnalysis.EventMeasureLimit
