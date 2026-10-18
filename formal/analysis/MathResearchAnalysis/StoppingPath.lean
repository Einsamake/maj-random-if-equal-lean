module

public import Mathlib.Probability.Process.Stopping
public import MathResearchAnalysis.NonnegativeMoment

set_option autoImplicit false

/-!
# Fixed-path readiness sigma-algebras

This constructs the discrete filtration of actual stopping-time sigma-algebras
along a fixed path. The real-valued times, their stopping-time properties, and
the readiness/completion order are explicit inputs. It does not construct
Poisson clocks, establish finite ringing times, or prove strong Markov.
-/

public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.StoppingPath

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A real-valued stopping time is measurable at its own stopping sigma-algebra. -/
theorem real_time_measurable (clocks : Filtration ℝ mΩ) (time : Ω → ℝ)
    (hstop : IsStoppingTime clocks (fun ω => (time ω : WithTop ℝ))) :
    Measurable[hstop.measurableSpace] time := by
  refine measurable_of_Iic fun t => ?_
  simpa only [Set.preimage, Set.mem_Iic, WithTop.coe_le_coe] using
    hstop.measurableSet_le' t

/-- The stopping sigma-algebras at ordered readiness times form a filtration. -/
def readinessFiltration (clocks : Filtration ℝ mΩ) (ready : Nat → Ω → ℝ)
    (hready : ∀ i, IsStoppingTime clocks (fun ω => (ready i ω : WithTop ℝ)))
    (horder : ∀ i ω, ready i ω ≤ ready (i + 1) ω) : Filtration Nat mΩ where
  seq i := (hready i).measurableSpace
  mono' := monotone_nat_of_le_succ fun i =>
    (hready i).measurableSpace_mono (hready (i + 1))
      (fun ω => WithTop.coe_le_coe.mpr (horder i ω))
  le' i := (hready i).measurableSpace_le

theorem readiness_order (ready complete : Nat → Ω → ℝ)
    (hbefore : ∀ i ω, ready i ω ≤ complete i ω)
    (hnext : ∀ i ω, complete i ω ≤ ready (i + 1) ω) :
    ∀ i ω, ready i ω ≤ ready (i + 1) ω :=
  fun i ω => (hbefore i ω).trans (hnext i ω)

/-- The waiting difference is known by the next readiness stopping sigma-algebra. -/
theorem delay_known (clocks : Filtration ℝ mΩ) (ready complete : Nat → Ω → ℝ)
    (hready : ∀ i, IsStoppingTime clocks (fun ω => (ready i ω : WithTop ℝ)))
    (hcomplete : ∀ i, IsStoppingTime clocks (fun ω => (complete i ω : WithTop ℝ)))
    (hbefore : ∀ i ω, ready i ω ≤ complete i ω)
    (hnext : ∀ i ω, complete i ω ≤ ready (i + 1) ω) (i : Nat) :
    StronglyMeasurable[
      readinessFiltration clocks ready hready (readiness_order ready complete hbefore hnext)
        (i + 1)] (fun ω => complete i ω - ready i ω) := by
  have hc : Measurable[(hready (i + 1)).measurableSpace] (complete i) :=
    (real_time_measurable clocks (complete i) (hcomplete i)).mono
    ((hcomplete i).measurableSpace_mono (hready (i + 1))
      (fun ω => WithTop.coe_le_coe.mpr (hnext i ω))) le_rfl
  have hr : Measurable[(hready (i + 1)).measurableSpace] (ready i) :=
    (real_time_measurable clocks (ready i) (hready i)).mono
    ((hready i).measurableSpace_mono (hready (i + 1))
      (fun ω => WithTop.coe_le_coe.mpr
        ((hbefore i ω).trans (hnext i ω)))) le_rfl
  exact (hc.sub hr).stronglyMeasurable

/-- Actual stopping-time measurability supplies the fixed-path known-past input.
The conditional waiting moment is an input, not a strong-Markov conclusion. -/
theorem stopped_path_moment {μ : Measure Ω} [IsProbabilityMeasure μ]
    (clocks : Filtration ℝ mΩ) (ready complete : Nat → Ω → ℝ)
    (hready : ∀ i, IsStoppingTime clocks (fun ω => (ready i ω : WithTop ℝ)))
    (hcomplete : ∀ i, IsStoppingTime clocks (fun ω => (complete i ω : WithTop ℝ)))
    (hbefore : ∀ i ω, ready i ω ≤ complete i ω)
    (hnext : ∀ i ω, complete i ω ≤ ready (i + 1) ω)
    (θ constant : ℝ) (length : Nat)
    (hwaitInt : ∀ i < length,
      Integrable (fun ω => Real.exp (θ * (complete i ω - ready i ω))) μ)
    (hconditional : ∀ i < length,
      μ[(fun ω => Real.exp (θ * (complete i ω - ready i ω))) |
        (hready i).measurableSpace] =ᵐ[μ] fun _ => constant) :
    Integrable (ConditionalMoment.pathExp θ
        (fun i ω => complete i ω - ready i ω) length) μ ∧
      (∫ ω, Real.exp (θ * ConditionalMoment.prefixSum
        (fun i ω => complete i ω - ready i ω) length ω) ∂μ) = constant ^ length := by
  let ℱ := readinessFiltration clocks ready hready
    (readiness_order ready complete hbefore hnext)
  have hknown : ∀ i < length, StronglyMeasurable[ℱ (i + 1)]
      (fun ω => complete i ω - ready i ω) := by
    intro i _
    exact delay_known clocks ready complete hready hcomplete hbefore hnext i
  exact ⟨NonnegativeMoment.fixed_path_exponential_integrable ℱ θ constant _ length
    hknown hwaitInt hconditional,
    NonnegativeMoment.fixed_path_exponential_moment ℱ θ constant _ length
      hknown hwaitInt hconditional⟩

end MathResearchAnalysis.StoppingPath
