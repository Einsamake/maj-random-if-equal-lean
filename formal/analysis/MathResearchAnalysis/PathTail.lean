module

public import MathResearchAnalysis.NonnegativeMoment
public import MathResearchAnalysis.FiniteTail

set_option autoImplicit false

/-!
# From single-step conditional moments to a finite maximum tail

Each path is fixed before sampling. Paths may share waits and need not be
independent. Prefix integrability and prefix moment values are derived, not
inputs. The single-step conditional expectation is still an explicit input.
-/

public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.PathTail

variable {Ω Index : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable [IsProbabilityMeasure μ]

/-- A finite family of fixed paths, each with its own readiness filtration. -/
theorem fixed_paths_maximum_tail
    (paths : Finset Index) (hne : paths.Nonempty)
    (filtration : Index → Filtration Nat mΩ)
    (wait : Index → Nat → Ω → ℝ) (length : Nat) (θ constant : ℝ)
    (hθ : 0 < θ) (threshold : ℝ)
    (hknown : ∀ p ∈ paths, ∀ i < length,
      StronglyMeasurable[filtration p (i + 1)] (wait p i))
    (hwaitInt : ∀ p ∈ paths, ∀ i < length,
      Integrable (fun ω => Real.exp (θ * wait p i ω)) μ)
    (hconditional : ∀ p ∈ paths, ∀ i < length,
      μ[(fun ω => Real.exp (θ * wait p i ω)) | filtration p i] =ᵐ[μ]
        fun _ => constant) :
    MeasurableSet {ω | threshold < FiniteTail.finiteMaximum paths hne
        (fun p => ConditionalMoment.prefixSum (wait p) length) ω} ∧
      μ.real {ω | threshold < FiniteTail.finiteMaximum paths hne
        (fun p => ConditionalMoment.prefixSum (wait p) length) ω} ≤
          (paths.card : ℝ) * constant ^ length * Real.exp (-θ * threshold) := by
  apply FiniteTail.finite_maximum_exponential_tail paths hne
    (fun p => ConditionalMoment.prefixSum (wait p) length) hθ threshold
  · intro p hp
    exact ((ConditionalMoment.prefixSum_stronglyMeasurable (filtration p)
      (wait p) length (hknown p hp) length le_rfl).mono
        ((filtration p).le length)).measurable
  · intro p hp
    exact NonnegativeMoment.fixed_path_exponential_integrable
      (filtration p) θ constant (wait p) length (hknown p hp)
        (hwaitInt p hp) (hconditional p hp)
  · intro p hp
    exact (NonnegativeMoment.fixed_path_exponential_moment
      (filtration p) θ constant (wait p) length (hknown p hp)
        (hwaitInt p hp) (hconditional p hp)).le

/-- Formula (12)'s per-path factor at theta = 1/2, before graph counting. -/
theorem fixed_paths_half_tail
    (paths : Finset Index) (hne : paths.Nonempty)
    (filtration : Index → Filtration Nat mΩ)
    (wait : Index → Nat → Ω → ℝ) (length : Nat) (threshold : ℝ)
    (hknown : ∀ p ∈ paths, ∀ i < length,
      StronglyMeasurable[filtration p (i + 1)] (wait p i))
    (hwaitInt : ∀ p ∈ paths, ∀ i < length,
      Integrable (fun ω => Real.exp ((1 / 2 : ℝ) * wait p i ω)) μ)
    (hconditional : ∀ p ∈ paths, ∀ i < length,
      μ[(fun ω => Real.exp ((1 / 2 : ℝ) * wait p i ω)) | filtration p i] =ᵐ[μ]
        fun _ => 2) :
    MeasurableSet {ω | threshold < FiniteTail.finiteMaximum paths hne
        (fun p => ConditionalMoment.prefixSum (wait p) length) ω} ∧
      μ.real {ω | threshold < FiniteTail.finiteMaximum paths hne
        (fun p => ConditionalMoment.prefixSum (wait p) length) ω} ≤
          (paths.card : ℝ) * (2 : ℝ) ^ length * Real.exp (-threshold / 2) := by
  have h := fixed_paths_maximum_tail paths hne filtration wait length (1 / 2) 2
    (by norm_num) threshold hknown hwaitInt hconditional
  have hexp : -(1 / 2 : ℝ) * threshold = -threshold / 2 := by ring
  simpa only [hexp] using h

end MathResearchAnalysis.PathTail
