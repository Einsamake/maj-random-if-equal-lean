module

public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
public import MathResearchAnalysis.NonnegativeMoment

set_option autoImplicit false

/-!
# Known-past waits at extended stopping times

Stopping times are allowed to be infinite. Taking a real representative is
used only for measurable random variables, never to assert that the resulting
real representative is itself a stopping time. Conditional laws are still inputs.
-/

public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.ExtendedStoppingPath

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem representative_measurable (clocks : Filtration ℝ mΩ)
    (time : Ω → WithTop ℝ) (hstop : IsStoppingTime clocks time) :
    Measurable[hstop.measurableSpace] (fun ω => (time ω).untopD 0) :=
  hstop.measurable.untopD 0

@[expose] def readinessFiltration (clocks : Filtration ℝ mΩ)
    (ready : Nat → Ω → WithTop ℝ) (hready : ∀ i, IsStoppingTime clocks (ready i))
    (horder : ∀ i ω, ready i ω ≤ ready (i + 1) ω) : Filtration Nat mΩ where
  seq i := (hready i).measurableSpace
  mono' := monotone_nat_of_le_succ fun i =>
    (hready i).measurableSpace_mono (hready (i + 1)) (horder i)
  le' i := (hready i).measurableSpace_le

@[expose] def waiting (ready complete : Nat → Ω → WithTop ℝ) (i : Nat) (ω : Ω) : ℝ :=
  max ((complete i ω).untopD 0 - (ready i ω).untopD 0) 0

theorem waiting_nonnegative (ready complete : Nat → Ω → WithTop ℝ) (i : Nat) (ω : Ω) :
    0 ≤ waiting ready complete i ω := le_max_right _ _

theorem readiness_order (ready complete : Nat → Ω → WithTop ℝ)
    (hbefore : ∀ i ω, ready i ω ≤ complete i ω)
    (hnext : ∀ i ω, complete i ω ≤ ready (i + 1) ω) :
    ∀ i ω, ready i ω ≤ ready (i + 1) ω :=
  fun i ω => (hbefore i ω).trans (hnext i ω)

theorem waiting_known (clocks : Filtration ℝ mΩ)
    (ready complete : Nat → Ω → WithTop ℝ)
    (hready : ∀ i, IsStoppingTime clocks (ready i))
    (hcomplete : ∀ i, IsStoppingTime clocks (complete i))
    (hbefore : ∀ i ω, ready i ω ≤ complete i ω)
    (hnext : ∀ i ω, complete i ω ≤ ready (i + 1) ω) (i : Nat) :
    StronglyMeasurable[
      readinessFiltration clocks ready hready (readiness_order ready complete hbefore hnext)
        (i + 1)] (waiting ready complete i) := by
  have hc : Measurable[(hready (i + 1)).measurableSpace]
      (fun ω => (complete i ω).untopD 0) :=
    (representative_measurable clocks (complete i) (hcomplete i)).mono
      ((hcomplete i).measurableSpace_mono (hready (i + 1)) (hnext i)) le_rfl
  have hr : Measurable[(hready (i + 1)).measurableSpace]
      (fun ω => (ready i ω).untopD 0) :=
    (representative_measurable clocks (ready i) (hready i)).mono
      ((hready i).measurableSpace_mono (hready (i + 1))
        (readiness_order ready complete hbefore hnext i)) le_rfl
  exact ((hc.sub hr).max measurable_const).stronglyMeasurable

theorem extended_path_moment {μ : Measure Ω} [IsProbabilityMeasure μ]
    (clocks : Filtration ℝ mΩ) (ready complete : Nat → Ω → WithTop ℝ)
    (hready : ∀ i, IsStoppingTime clocks (ready i))
    (hcomplete : ∀ i, IsStoppingTime clocks (complete i))
    (hbefore : ∀ i ω, ready i ω ≤ complete i ω)
    (hnext : ∀ i ω, complete i ω ≤ ready (i + 1) ω)
    (θ constant : ℝ) (length : Nat)
    (hwaitInt : ∀ i < length, Integrable (fun ω => Real.exp
      (θ * waiting ready complete i ω)) μ)
    (hconditional : ∀ i < length, μ[(fun ω => Real.exp
      (θ * waiting ready complete i ω)) | (hready i).measurableSpace] =ᵐ[μ]
        fun _ => constant) :
    Integrable (ConditionalMoment.pathExp θ (waiting ready complete) length) μ ∧
      (∫ ω, Real.exp (θ * ConditionalMoment.prefixSum
        (waiting ready complete) length ω) ∂μ) = constant ^ length := by
  let ℱ := readinessFiltration clocks ready hready
    (readiness_order ready complete hbefore hnext)
  have hknown : ∀ i < length, StronglyMeasurable[ℱ (i + 1)]
      (waiting ready complete i) := fun i _ =>
    waiting_known clocks ready complete hready hcomplete hbefore hnext i
  exact ⟨NonnegativeMoment.fixed_path_exponential_integrable ℱ θ constant _ length
      hknown hwaitInt hconditional,
    NonnegativeMoment.fixed_path_exponential_moment ℱ θ constant _ length
      hknown hwaitInt hconditional⟩

end MathResearchAnalysis.ExtendedStoppingPath
