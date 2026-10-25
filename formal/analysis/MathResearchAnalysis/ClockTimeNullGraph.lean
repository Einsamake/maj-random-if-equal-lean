module

public import MathResearchAnalysis.PredictableClockReference
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

set_option autoImplicit false

/-!
# Countable event-time graphs are null for actual Lebesgue time

A measurable countable family of real times defines a measurable graph in
(time,sample). Every sample section is countable, including exceptional clock
samples. Genuine product-measure almost-everywhere avoidance is proved before
it is used. No state measurability, clock non-atomic arrival law, independence
or stopping-time conclusion is assumed.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.ClockTimeNullGraph

open MeasureTheory Set

universe u v
variable {E : Type u} {Ω : Type v} [Countable E] [MeasurableSpace Ω]

/-- The actual graph of a countable real event-time family. -/
def graph (τ : E → Ω → Real) : Set (Real × Ω) :=
  {p | ∃ e : E, p.1 = τ e p.2}

theorem graph_measurable (τ : E → Ω → Real) (hτ : ∀ e, Measurable (τ e)) :
    MeasurableSet (graph τ) := by
  have heq : graph τ = ⋃ e : E, {p : Real × Ω | p.1 = τ e p.2} := by
    ext p
    simp only [graph,Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [heq]
  exact MeasurableSet.iUnion (fun e => measurableSet_eq_fun measurable_fst
    ((hτ e).comp measurable_snd))

omit [MeasurableSpace Ω] in
/-- Every path has a countable null exceptional time set. -/
theorem sample_section_ae_avoid (τ : E → Ω → Real) (ν : Measure Real)
    [NullSingletonClass ν] (z : Ω) :
    ∀ᵐ t ∂ν, (t,z) ∉ graph τ := by
  have h := (Set.countable_range (fun e : E => τ e z)).ae_notMem ν
  filter_upwards [h] with t ht
  rintro ⟨e,he⟩
  exact ht ⟨e,he.symm⟩

theorem sample_time_ae_avoid (τ : E → Ω → Real) (μ : Measure Ω) (ν : Measure Real)
    [NullSingletonClass ν] :
    ∀ᵐ z ∂μ, ∀ᵐ t ∂ν, (t,z) ∉ graph τ :=
  Filter.Eventually.of_forall (sample_section_ae_avoid τ ν)

/-- The measurable graph justifies swapping the AE order. -/
theorem time_sample_ae_avoid (τ : E → Ω → Real) (hτ : ∀ e, Measurable (τ e))
    (μ : Measure Ω) (ν : Measure Real) [SFinite μ] [SFinite ν] [NullSingletonClass ν] :
    ∀ᵐ t ∂ν, ∀ᵐ z ∂μ, (t,z) ∉ graph τ := by
  exact (Measure.ae_ae_comm (μ := ν) (ν := μ)
    (graph_measurable τ hτ).compl).mpr (sample_time_ae_avoid τ μ ν)

theorem product_ae_avoid (τ : E → Ω → Real) (hτ : ∀ e, Measurable (τ e))
    (μ : Measure Ω) (ν : Measure Real) [SFinite μ] [SFinite ν] [NullSingletonClass ν] :
    ∀ᵐ p ∂ν.prod μ, p ∉ graph τ := by
  exact (Measure.ae_prod_iff_ae_ae (graph_measurable τ hτ).compl).mpr
    (time_sample_ae_avoid τ hτ μ ν)

theorem graph_product_null (τ : E → Ω → Real) (hτ : ∀ e, Measurable (τ e))
    (μ : Measure Ω) (ν : Measure Real) [SFinite μ] [SFinite ν] [NullSingletonClass ν] :
    (ν.prod μ) (graph τ) = 0 := by
  simpa only [ae_iff,Set.mem_ofPred_eq,not_not,Set.ofPred_mem_eq] using product_ae_avoid τ hτ μ ν

/-- Both product orientations are genuinely covered. -/
theorem swapped_product_ae_avoid (τ : E → Ω → Real) (hτ : ∀ e, Measurable (τ e))
    (μ : Measure Ω) (ν : Measure Real) [SFinite μ] [SFinite ν] [NullSingletonClass ν] :
    ∀ᵐ p ∂μ.prod ν, (p.2,p.1) ∉ graph τ := by
  exact (Measure.ae_prod_iff_ae_ae
    ((graph_measurable τ hτ).compl.preimage measurable_swap)).mpr
    (sample_time_ae_avoid τ μ ν)

/-- The original clock graph; the finite-square parameter n is arbitrary. -/
def clockGraph (n : Nat) : Set (Real × ClockWordMarks.Sample n) :=
  graph (fun (e : SquareSpin.Event n) (z : ClockWordMarks.Sample n) =>
    ClockEventWord.eventTime z.1 e)

theorem clockGraph_measurable (n : Nat) : MeasurableSet (clockGraph n) :=
  graph_measurable _ (fun e => (ClockEventWord.eventTime_measurable e).comp measurable_fst)

/-- This does not permit evaluation at a random ringing time. -/
theorem clock_time_sample_ae_no_event (n : Nat) :
    ∀ᵐ t : Real ∂volume, ∀ᵐ z ∂ClockWordMarks.measure n,
      ∀ e : SquareSpin.Event n, ClockEventWord.eventTime z.1 e ≠ t := by
  have h := time_sample_ae_avoid
    (fun (e : SquareSpin.Event n) (z : ClockWordMarks.Sample n) => ClockEventWord.eventTime z.1 e)
    (fun e => (ClockEventWord.eventTime_measurable e).comp measurable_fst)
    (ClockWordMarks.measure n) volume
  filter_upwards [h] with t ht
  filter_upwards [ht] with z hz
  intro e he
  exact hz ⟨e,he.symm⟩

theorem clock_product_ae_no_event (n : Nat) (ν : Measure Real)
    [SFinite ν] [NullSingletonClass ν] :
    ∀ᵐ p ∂ν.prod (ClockWordMarks.measure n),
      ∀ e : SquareSpin.Event n, ClockEventWord.eventTime p.2.1 e ≠ p.1 := by
  have h := product_ae_avoid
    (fun (e : SquareSpin.Event n) (z : ClockWordMarks.Sample n) => ClockEventWord.eventTime z.1 e)
    (fun e => (ClockEventWord.eventTime_measurable e).comp measurable_fst)
    (ClockWordMarks.measure n) ν
  filter_upwards [h] with p hp
  intro e he
  exact hp ⟨e,he.symm⟩

/-- True finite-horizon Lebesgue time times the original clock/mark law. -/
theorem clock_horizon_product_ae_no_event (n : Nat) (T : NNReal) :
    ∀ᵐ p ∂((volume : Measure Real).restrict (Ioc 0 (T : Real))).prod
      (ClockWordMarks.measure n),
      ∀ e : SquareSpin.Event n, ClockEventWord.eventTime p.2.1 e ≠ p.1 :=
  clock_product_ae_no_event n _

end MathResearchAnalysis.ClockTimeNullGraph

