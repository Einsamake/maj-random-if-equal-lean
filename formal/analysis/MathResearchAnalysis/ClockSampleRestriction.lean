module

public import MathResearchAnalysis.ClockWordMarks

set_option autoImplicit false

/-!
# Restricting the actual clocks and identity marks to an injected smaller square

An event keeps its zero-based arrival index. Both coordinates of the actual
sample are projected by the same event injection. The product-measure law is
proved from the exponential and fair infinite products; it is not supplied as
a coupling assumption. Raw and chronological event times agree pointwise,
including exceptional samples. No update-word filtering is asserted here.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.ClockSampleRestriction

open MeasureTheory Set
open SquareTasks (Vertex)
open ClockWordMarks (Event Sample)

/-- The arrival index is retained literally when a site is embedded. -/
def eventι {n m : Nat} (ι : Vertex n → Vertex m) : Event n → Event m :=
  fun e => (ι e.1,e.2)

theorem eventι_injective {n m : Nat} {ι : Vertex n → Vertex m}
    (hι : Function.Injective ι) : Function.Injective (eventι ι) := by
  intro a b hab
  apply Prod.ext
  · exact hι (congrArg (fun e : Event m => e.1) hab)
  · exact congrArg (fun e : Event m => e.2) hab

/-- Every retained event uses its actual original exponential gap. -/
def projectClock {n m : Nat} (ι : Vertex n → Vertex m)
    (ω : ExponentialClocks.Sample (Vertex m)) : ExponentialClocks.Sample (Vertex n) :=
  fun e => ω (eventι ι e)

/-- Its independent fair mark is read at the same retained event identity. -/
def projectMarks {n m : Nat} (ι : Vertex n → Vertex m)
    (η : FairMarks.Sample (Event m)) : FairMarks.Sample (Event n) :=
  fun e => η (eventι ι e)

/-- Restrict the actual joint clock/mark sample without changing identities. -/
def projectSample {n m : Nat} (ι : Vertex n → Vertex m) : Sample m → Sample n :=
  Prod.map (projectClock ι) (projectMarks ι)

theorem projectClock_measurable {n m : Nat} (ι : Vertex n → Vertex m) :
    Measurable (projectClock ι) :=
  measurable_pi_iff.mpr (fun e => measurable_pi_apply (eventι ι e))

theorem projectMarks_measurable {n m : Nat} (ι : Vertex n → Vertex m) :
    Measurable (projectMarks ι) :=
  measurable_pi_iff.mpr (fun e => measurable_pi_apply (eventι ι e))

theorem projectSample_measurable {n m : Nat} (ι : Vertex n → Vertex m) :
    Measurable (projectSample ι) :=
  (projectClock_measurable ι).prodMap (projectMarks_measurable ι)

/-- The actual projected clock field has exactly the original smaller-square law. -/
theorem projectClock_map {n m : Nat} (ι : Vertex n → Vertex m) (hι : Function.Injective ι) :
    (ExponentialClocks.clockMeasure (Vertex m)).map (projectClock ι) =
      ExponentialClocks.clockMeasure (Vertex n) := by
  exact Measure.map_infinitePi_infinitePi_of_inj (eventι_injective hι)

/-- All retained fair marks jointly have their original infinite product law. -/
theorem projectMarks_map {n m : Nat} (ι : Vertex n → Vertex m) (hι : Function.Injective ι) :
    (FairMarks.markMeasure (Event m)).map (projectMarks ι) = FairMarks.markMeasure (Event n) := by
  exact Measure.map_infinitePi_infinitePi_of_inj (eventι_injective hι)

/-- In particular clocks and retained marks keep their genuine joint product law. -/
theorem projectSample_map {n m : Nat} (ι : Vertex n → Vertex m) (hι : Function.Injective ι) :
    (ClockWordMarks.measure m).map (projectSample ι) = ClockWordMarks.measure n := by
  unfold ClockWordMarks.measure projectSample
  rw [←Measure.map_prod_map _ _ (projectClock_measurable ι) (projectMarks_measurable ι),
    projectClock_map ι hι,projectMarks_map ι hι]

@[simp] theorem projected_gap {n m : Nat} (ι : Vertex n → Vertex m)
    (ω : ExponentialClocks.Sample (Vertex m)) (v : Vertex n) (k : Nat) :
    ExponentialClocks.gap v k (projectClock ι ω) = ExponentialClocks.gap (ι v) k ω := rfl

/-- No almost-sure substitution is needed for the raw partial sums. -/
@[simp] theorem projected_arrival {n m : Nat} (ι : Vertex n → Vertex m)
    (ω : ExponentialClocks.Sample (Vertex m)) (v : Vertex n) (k : Nat) :
    ExponentialClocks.arrival v k (projectClock ι ω) = ExponentialClocks.arrival (ι v) k ω := rfl

/-- The clipping operation also commutes pointwise with retained coordinates. -/
@[simp] theorem projected_chronologicalArrival {n m : Nat} (ι : Vertex n → Vertex m)
    (ω : ExponentialClocks.Sample (Vertex m)) (v : Vertex n) (k : Nat) :
    ArrivalFiltration.chronologicalArrival v k (projectClock ι ω) =
      ArrivalFiltration.chronologicalArrival (ι v) k ω := rfl

@[simp] theorem projected_eventTime {n m : Nat} (ι : Vertex n → Vertex m)
    (ω : ExponentialClocks.Sample (Vertex m)) (e : Event n) :
    ClockEventWord.eventTime (projectClock ι ω) e = ClockEventWord.eventTime ω (eventι ι e) := rfl

@[simp] theorem projected_mark {n m : Nat} (ι : Vertex n → Vertex m)
    (η : FairMarks.Sample (Event m)) (e : Event n) :
    projectMarks ι η e = η (eventι ι e) := rfl

/-- Bounded event identities are the literal inverse image under the event injection. -/
theorem projected_eventSet {n m : Nat} (ι : Vertex n → Vertex m)
    (ω : ExponentialClocks.Sample (Vertex m)) (t : Real) :
    ClockEventWord.eventSet (projectClock ι ω) t = (eventι ι) ⁻¹' ClockEventWord.eventSet ω t := rfl

/-- Finiteness and absence of ties pass to the retained clocks on every good sample. -/
theorem projected_good {n m : Nat} (ι : Vertex n → Vertex m) (hι : Function.Injective ι)
    (ω : ExponentialClocks.Sample (Vertex m)) (t : Real) (h : ClockEventWord.Good ω t) :
    ClockEventWord.Good (projectClock ι ω) t := by
  constructor
  · rw [projected_eventSet]
    exact Set.Finite.preimage (eventι_injective hι).injOn h.1
  · intro a b hab
    apply eventι_injective hι
    exact h.2 hab

/-- A common original-law full-probability set works for all retained time bounds. -/
theorem projected_good_ae {n m : Nat} (ι : Vertex n → Vertex m) (hι : Function.Injective ι) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (Vertex m),
      ∀ t : Real, ClockEventWord.Good (projectClock ι ω) t := by
  filter_upwards [ClockEventWord.good_ae (V := Vertex m)] with ω hω
  exact fun t => projected_good ι hι ω t (hω t)

end MathResearchAnalysis.ClockSampleRestriction
