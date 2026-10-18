module

public import MathResearchAnalysis.InfiniteGridTranslation
public import MathResearchAnalysis.InfiniteGridRecoveryTime
public import MathResearchAnalysis.RecoveryTimeTransport

set_option autoImplicit false

/-!
# Translation invariance of the actual random grid and its extended recovery law

The entire mark field is shifted together with the initial configuration.
Its product law is invariant by coordinate injection. Checkerboard phases
change at odd spatial shifts; the recovery identities include infinite hits.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.InfiniteGridTranslationLaw

open InfiniteGridTranslation

abbrev Site := InfiniteGridModel.Site
abbrev Config := InfiniteGridModel.Config
abbrev Sample := InfiniteGridRandomDynamics.Sample
abbrev Event := InfiniteGridRandomDynamics.Event

def eventShift (a : Site) (e : Event) : Event := (shift a e.1, e.2)

theorem eventShift_injective (a : Site) : Function.Injective (eventShift a) := by
  intro e f h
  have hx := congrArg (fun q : Event => q.1.1) h
  have hy := congrArg (fun q : Event => q.1.2) h
  have ht := congrArg (fun q : Event => q.2) h
  apply Prod.ext
  · apply Prod.ext <;> simp only [eventShift, shift] at hx hy ⊢ <;> omega
  · exact ht

def translateSample (a : Site) : Sample → Sample := FairMarksTransport.pullback (eventShift a)

theorem translateSample_measurable (a : Site) : Measurable (translateSample a) :=
  FairMarksTransport.pullback_measurable (eventShift a)

theorem translateSample_map_measure (a : Site) :
    Measure.map (translateSample a) InfiniteGridRandomDynamics.measure =
      InfiniteGridRandomDynamics.measure :=
  FairMarksTransport.map_pullback (eventShift a) (eventShift_injective a)

theorem synchronous_translate (a : Site) (initial : Config) (t : Nat) (η : Sample) :
    InfiniteGridRandomDynamics.synchronous (translate a initial) t (translateSample a η) =
      translate a (InfiniteGridRandomDynamics.synchronous initial t η) :=
  InfiniteGridTranslation.synchronous_translate a (InfiniteGridRandomDynamics.marks η) initial t

theorem alternating_translate (a : Site) (initial : Config) (phase : Bool)
    (t : Nat) (η : Sample) :
    InfiniteGridRandomDynamics.alternating (translate a initial) (translatePhase a phase) t
        (translateSample a η) =
      translate a (InfiniteGridRandomDynamics.alternating initial phase t η) :=
  InfiniteGridTranslation.alternating_translate a (InfiniteGridRandomDynamics.marks η) initial phase t

theorem synchronous_recovery_eq (a : Site) (initial : Config) (η : Sample) :
    InfiniteGridRecoveryTime.synchronous (translate a initial) (translateSample a η) =
      InfiniteGridRecoveryTime.synchronous initial η := by
  apply RecoveryTimeTransport.time_eq_of_zero_iff
    (fun t ξ => InfiniteGridRandomDynamics.synchronous (translate a initial) t (translateSample a ξ))
    (InfiniteGridRandomDynamics.synchronous initial)
    InfiniteGridRecoveryTime.zeroConfig InfiniteGridRecoveryTime.zeroConfig η
  intro t
  rw [synchronous_translate]
  exact translate_eq_zero_iff a _

theorem alternating_recovery_eq (a : Site) (initial : Config) (phase : Bool) (η : Sample) :
    InfiniteGridRecoveryTime.alternating (translate a initial) (translatePhase a phase)
        (translateSample a η) = InfiniteGridRecoveryTime.alternating initial phase η := by
  apply RecoveryTimeTransport.time_eq_of_zero_iff
    (fun t ξ => InfiniteGridRandomDynamics.alternating (translate a initial) (translatePhase a phase) t
      (translateSample a ξ))
    (InfiniteGridRandomDynamics.alternating initial phase)
    InfiniteGridRecoveryTime.zeroConfig InfiniteGridRecoveryTime.zeroConfig η
  intro t
  rw [alternating_translate]
  exact translate_eq_zero_iff a _

theorem synchronous_recovery_map (a : Site) (initial : Config) :
    Measure.map (InfiniteGridRecoveryTime.synchronous (translate a initial))
        InfiniteGridRandomDynamics.measure =
      Measure.map (InfiniteGridRecoveryTime.synchronous initial) InfiniteGridRandomDynamics.measure := by
  conv_lhs => rw [← translateSample_map_measure a]
  rw [Measure.map_map (InfiniteGridRecoveryTime.synchronous_measurable _)
    (translateSample_measurable a)]
  congr 1
  exact funext (synchronous_recovery_eq a initial)

theorem alternating_recovery_map (a : Site) (initial : Config) (phase : Bool) :
    Measure.map (InfiniteGridRecoveryTime.alternating (translate a initial) (translatePhase a phase))
        InfiniteGridRandomDynamics.measure =
      Measure.map (InfiniteGridRecoveryTime.alternating initial phase) InfiniteGridRandomDynamics.measure := by
  conv_lhs => rw [← translateSample_map_measure a]
  rw [Measure.map_map (InfiniteGridRecoveryTime.alternating_measurable _ _)
    (translateSample_measurable a)]
  congr 1
  exact funext (alternating_recovery_eq a initial phase)

end MathResearchAnalysis.InfiniteGridTranslationLaw
