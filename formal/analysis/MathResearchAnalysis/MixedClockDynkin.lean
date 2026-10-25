module

public import MathResearchAnalysis.MachineClockGenerator
public import MathResearchAnalysis.MixedSquareClockLaw
public import MathResearchAnalysis.MixedExclusionGenerator

set_option autoImplicit false

/-!
# Genuine mixed-clock Dynkin with the actual exclusion generator

The finite-machine theorem is instantiated on the original mixed update and
identity-mark law. The generator identification uses the actual current
staircase shape, valid for every sample and time from a monotone initial state.
No moment equation, transition law or compensation identity is a premise.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.MixedClockDynkin

open MeasureTheory Set
open DropletClockLaw (Sample Vertex Config)
open MixedExclusionGenerator (Slot slotState pathEdges)

/-- The actual mixed cell update as a finite marked-clock machine. -/
def step (L : Nat) : Vertex L → Bool → Config L → Config L :=
  fun v b f => MixedSquareModel.cellUpdate f v b

/-- The generic machine and actual mixed endpoint are definitionally identical,
including the guarded total word and original event identity marks. -/
theorem endpoint_eq_mixed (L : Nat) (initial : Config L) (t : Real) (z : Sample L) :
    FiniteObservedClockState.endpoint L (step L) initial t z =
      MixedSquareClockLaw.endpoint (ClippedSquareCoordinates.parameter L) t initial z := rfl

theorem generator_eq_exclusion (L : Nat) (f : Config L) (hf : Monotone f)
    (F : (Slot (ClippedSquareCoordinates.parameter L) → Bool) → Real) :
    MachineClockGenerator.generator L (step L) (fun g => F (slotState g)) f =
      FiniteExclusionGenerator.generator (pathEdges (ClippedSquareCoordinates.parameter L)) F (slotState f) := by
  exact MixedExclusionGenerator.actual_generator_eq_exclusion hf F

/-- Only the actual current endpoint is used here, after its proved shape
invariance. No claim that a guarded endpoint is past-adapted is substituted. -/
theorem generator_at_endpoint (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (F : (Slot (ClippedSquareCoordinates.parameter L) → Bool) → Real)
    (t : Real) (z : Sample L) :
    MachineClockGenerator.generator L (step L) (fun g => F (slotState g))
      (FiniteObservedClockState.endpoint L (step L) initial t z) =
      FiniteExclusionGenerator.generator (pathEdges (ClippedSquareCoordinates.parameter L)) F
        (slotState (MixedSquareClockLaw.endpoint (ClippedSquareCoordinates.parameter L) t initial z)) := by
  rw [endpoint_eq_mixed]
  exact generator_eq_exclusion L _
    (MixedSquareClockLaw.endpoint_monotone_shape _ t initial hinit z) F

theorem observable_integrable (L : Nat) (initial : Config L)
    (F : (Slot (ClippedSquareCoordinates.parameter L) → Bool) → Real) (T : NNReal) :
    Integrable (fun z : Sample L => F (slotState
      (MixedSquareClockLaw.endpoint (ClippedSquareCoordinates.parameter L) (T : Real) initial z)))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  MachineClockDynkin.observable_integrable (fun g => F (slotState g)) L (step L) initial T

/-- Integrability is transported from the true finite-machine current-state
formula before any later moment equation exchanges are attempted. -/
theorem generator_time_mean_integrable (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (F : (Slot (ClippedSquareCoordinates.parameter L) → Bool) → Real) (T : NNReal) :
    Integrable (fun u : Real => ∫ z : Sample L,
      FiniteExclusionGenerator.generator (pathEdges (ClippedSquareCoordinates.parameter L)) F
        (slotState (MixedSquareClockLaw.endpoint (ClippedSquareCoordinates.parameter L) u initial z))
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L))
      ((volume : Measure Real).restrict (Ioc 0 (T : Real))) := by
  apply (MachineClockGenerator.current_generator_time_mean_integrable L (step L) initial
    (fun g => F (slotState g)) T).congr
  apply Filter.Eventually.of_forall
  intro u
  exact integral_congr_ae (Filter.Eventually.of_forall (fun z => generator_at_endpoint L initial hinit F u z))

/-- The actual mixed slot process satisfies Dynkin under the original clock
law and elapsed Lebesgue time, with rate one half per listed adjacent bond. -/
theorem expected_observable_dynkin (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (F : (Slot (ClippedSquareCoordinates.parameter L) → Bool) → Real) (T : NNReal) :
    (∫ z : Sample L, F (slotState
      (MixedSquareClockLaw.endpoint (ClippedSquareCoordinates.parameter L) (T : Real) initial z))
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      F (slotState initial) + ∫ u : Real in Ioc 0 (T : Real), ∫ z : Sample L,
        FiniteExclusionGenerator.generator (pathEdges (ClippedSquareCoordinates.parameter L)) F
          (slotState (MixedSquareClockLaw.endpoint (ClippedSquareCoordinates.parameter L) u initial z))
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  calc
    _ = F (slotState initial) + ∫ u : Real in Ioc 0 (T : Real), ∫ z : Sample L,
        MachineClockGenerator.generator L (step L) (fun g => F (slotState g))
          (FiniteObservedClockState.endpoint L (step L) initial u z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) :=
      MachineClockGenerator.expected_observable_dynkin_current L (step L) initial
        (fun g => F (slotState g)) T
    _ = _ := by
      congr 1
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      exact integral_congr_ae (Filter.Eventually.of_forall
        (fun z => generator_at_endpoint L initial hinit F u z))

end MathResearchAnalysis.MixedClockDynkin
