module

public import MathResearchAnalysis.InfiniteGridRecoveryTime
public import MathResearchAnalysis.RecoveryTimeTransport

set_option autoImplicit false

/-!
# Complement symmetry for the actual infinite-grid random dynamics

The spin complement also complements each tie mark. The whole independent
fair-mark product measure is invariant under this operation. Consequently,
first recovery to the all-one configuration has the same law as first
recovery to zero from the complemented initial configuration, including
samples with infinite recovery time.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.InfiniteGridComplement

abbrev Config := InfiniteGridModel.Config
abbrev Marks := InfiniteGridModel.Marks
abbrev Sample := InfiniteGridRandomDynamics.Sample

def complementConfig (state : Config) : Config := fun v => !(state v)

def complementMarks (marks : Marks) : Marks := fun t v => !(marks t v)

def complementSample {I : Type*} (η : FairMarks.Sample I) : FairMarks.Sample I :=
  fun i => !(η i)

theorem majority4_complement : ∀ a b c d tie : Bool,
    InfiniteGridModel.majority4 (!a) (!b) (!c) (!d) (!tie) =
      !(InfiniteGridModel.majority4 a b c d tie) := by
  decide

theorem update_complement (marks : Marks) (t : Nat) (v : InfiniteGridModel.Site)
    (state : Config) :
    InfiniteGridModel.update (complementMarks marks) t v (complementConfig state) =
      !(InfiniteGridModel.update marks t v state) :=
  majority4_complement _ _ _ _ _

theorem synchronous_complement (marks : Marks) (initial : Config) (t : Nat) :
    InfiniteGridModel.synchronous (complementMarks marks) (complementConfig initial) t =
      complementConfig (InfiniteGridModel.synchronous marks initial t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [InfiniteGridModel.synchronous_succ, InfiniteGridModel.synchronous_succ, ih]
    funext v
    exact update_complement marks (t + 1) v _

theorem alternating_complement (marks : Marks) (initial : Config) (phase : Bool) (t : Nat) :
    InfiniteGridModel.alternating (complementMarks marks) (complementConfig initial) phase t =
      complementConfig (InfiniteGridModel.alternating marks initial phase t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [InfiniteGridModel.alternating_succ, InfiniteGridModel.alternating_succ, ih]
    funext v
    by_cases h : InfiniteGridModel.colour v = BipartiteDynamics.activeColour phase (t + 1)
    · simp only [h, ite_true, complementConfig]
      exact update_complement marks (t + 1) v _
    · simp only [h, ite_false, complementConfig]

theorem fair_map_not : Measure.map Bool.not FairMarks.fair = FairMarks.fair := by
  have hn : Measurable Bool.not := measurable_of_countable _
  simp only [FairMarks.fair, Measure.map_add _ _ hn,
    Measure.map_smul _ hn.aemeasurable, Measure.map_dirac' hn,
    Bool.not_true, Bool.not_false]
  exact add_comm _ _

theorem complementSample_measurable (I : Type*) :
    Measurable (complementSample (I := I)) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_of_countable Bool.not).comp (measurable_pi_apply i)

theorem complementSample_map (I : Type*) :
    Measure.map (complementSample (I := I)) (FairMarks.markMeasure I) =
      FairMarks.markMeasure I := by
  change (Measure.infinitePi (fun _ : I => FairMarks.fair)).map
      (fun η i => !(η i)) = Measure.infinitePi (fun _ : I => FairMarks.fair)
  rw [Measure.infinitePi_map_pi (fun _ : I => FairMarks.fair)
    (fun _ => measurable_of_countable Bool.not)]
  simp only [fair_map_not]

theorem random_synchronous_complement (initial : Config) (t : Nat) (η : Sample) :
    InfiniteGridRandomDynamics.synchronous (complementConfig initial) t (complementSample η) =
      complementConfig (InfiniteGridRandomDynamics.synchronous initial t η) :=
  synchronous_complement (InfiniteGridRandomDynamics.marks η) initial t

theorem random_alternating_complement (initial : Config) (phase : Bool) (t : Nat)
    (η : Sample) :
    InfiniteGridRandomDynamics.alternating (complementConfig initial) phase t
        (complementSample η) =
      complementConfig (InfiniteGridRandomDynamics.alternating initial phase t η) :=
  alternating_complement (InfiniteGridRandomDynamics.marks η) initial phase t

def targetOneSynchronous (initial : Config) : Sample → ℕ∞ :=
  ExtendedRecoveryTime.time (InfiniteGridRandomDynamics.synchronous initial) (fun _ => true)

private theorem complement_eq_zero_iff (state : Config) :
    complementConfig state = InfiniteGridRecoveryTime.zeroConfig ↔ state = (fun _ => true) := by
  constructor
  · intro h
    funext v
    have hv := congrFun h v
    cases hs : state v <;> simp [complementConfig, hs] at hv ⊢
  · intro h
    rw [h]
    rfl

theorem targetOneSynchronous_eq_zero_complement (initial : Config) (η : Sample) :
    targetOneSynchronous initial η =
      InfiniteGridRecoveryTime.synchronous (complementConfig initial) (complementSample η) := by
  apply RecoveryTimeTransport.time_eq_of_zero_iff
    (InfiniteGridRandomDynamics.synchronous initial)
    (fun t ξ => InfiniteGridRandomDynamics.synchronous (complementConfig initial) t
      (complementSample ξ))
    (fun _ => true) InfiniteGridRecoveryTime.zeroConfig η
  intro t
  rw [random_synchronous_complement]
  exact (complement_eq_zero_iff _).symm

theorem targetOneSynchronous_map (initial : Config) :
    Measure.map (targetOneSynchronous initial) InfiniteGridRandomDynamics.measure =
      Measure.map (InfiniteGridRecoveryTime.synchronous (complementConfig initial))
        InfiniteGridRandomDynamics.measure := by
  have heq : targetOneSynchronous initial =
      InfiniteGridRecoveryTime.synchronous (complementConfig initial) ∘ complementSample :=
    funext (targetOneSynchronous_eq_zero_complement initial)
  rw [heq, ← Measure.map_map (InfiniteGridRecoveryTime.synchronous_measurable _)
    (complementSample_measurable _)]
  exact congrArg (Measure.map (InfiniteGridRecoveryTime.synchronous (complementConfig initial)))
    (complementSample_map InfiniteGridRandomDynamics.Event)

end MathResearchAnalysis.InfiniteGridComplement
