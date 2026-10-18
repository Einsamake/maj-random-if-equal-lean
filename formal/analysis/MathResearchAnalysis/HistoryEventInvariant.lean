module

public import MathResearchAnalysis.ArrivalFiltration

set_option autoImplicit false

/-!
# Observation equivalence determines every common-history event

This is a pointwise statement for the actual generated sigma-algebra. It
does not replace the physical history by independent full coordinate data.
-/

public section

open MeasureTheory Set

namespace MathResearchAnalysis.HistoryEventInvariant

variable {Ω V : Type*} {mΩ : MeasurableSpace Ω}

theorem history_event_invariant (A : V → Nat → Ω → ℝ)
    (hA : ∀ v k, Measurable (A v k)) (r : ℝ) (E : Set Ω)
    (hE : MeasurableSet[ArrivalFiltration.history A hA r] E) (ω ω' : Ω)
    (hobs : ∀ v k u, u ≤ r → (A v k ω ≤ u ↔ A v k ω' ≤ u)) :
    ω ∈ E ↔ ω' ∈ E := by
  have hsame : ∀ s ∈ {s : Set Ω | ∃ v k u, u ≤ r ∧ s = {ω | A v k ω ≤ u}},
      ω ∈ s ↔ ω' ∈ s := by
    rintro _ ⟨v, k, u, hu, rfl⟩
    exact hobs v k u hu
  exact (MeasurableSpace.forall_generateFrom_mem_iff_mem_iff.mpr hsame) E hE

theorem history_event_equivalence_iff (A : V → Nat → Ω → ℝ)
    (hA : ∀ v k, Measurable (A v k)) (r : ℝ) (ω ω' : Ω) :
    (∀ E : Set Ω, MeasurableSet[ArrivalFiltration.history A hA r] E →
      (ω ∈ E ↔ ω' ∈ E)) ↔
      ∀ v k u, u ≤ r → (A v k ω ≤ u ↔ A v k ω' ≤ u) := by
  constructor
  · intro h v k u hu
    exact h _ (ArrivalFiltration.arrival_event_measurable A hA v k hu)
  · intro h E hE
    exact history_event_invariant A hA r E hE ω ω' h

theorem clock_event_invariant (r : ℝ) (E : Set (ExponentialClocks.Sample V))
    (hE : MeasurableSet[ArrivalFiltration.clockHistory V r] E)
    (ω ω' : ExponentialClocks.Sample V)
    (hobs : ∀ v k u, u ≤ r →
      (ArrivalFiltration.chronologicalArrival v k ω ≤ u ↔
        ArrivalFiltration.chronologicalArrival v k ω' ≤ u)) :
    ω ∈ E ↔ ω' ∈ E :=
  history_event_invariant ArrivalFiltration.chronologicalArrival
    ArrivalFiltration.chronologicalArrival_measurable r E hE ω ω' hobs

end MathResearchAnalysis.HistoryEventInvariant
