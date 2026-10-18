module

public import MathResearchAnalysis.InfiniteGridRandomDynamics
public import MathResearchAnalysis.ExtendedRecoveryTime

set_option autoImplicit false

/-!
# Extended recovery times of the actual infinite-lattice random dynamics

The first zero times are defined on the genuine infinite fair-mark field and
retain infinity on samples that never reach zero. Zero absorption follows from
the actual four-neighbour rule. All statements apply to arbitrary initial
configurations, without a finite-support or finite-recovery assumption.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.InfiniteGridRecoveryTime

abbrev Config := InfiniteGridModel.Config
abbrev Sample := InfiniteGridRandomDynamics.Sample
abbrev zeroConfig : Config := fun _ => false

theorem isZero_iff_eq_zero (state : Config) :
    BipartiteDynamics.IsZero state ↔ state = zeroConfig := by
  constructor
  · exact fun h => funext h
  · intro h v
    exact congrFun h v

def synchronous (initial : Config) : Sample → ℕ∞ :=
  ExtendedRecoveryTime.time (InfiniteGridRandomDynamics.synchronous initial) zeroConfig

def alternating (initial : Config) (phase : Bool) : Sample → ℕ∞ :=
  ExtendedRecoveryTime.time (InfiniteGridRandomDynamics.alternating initial phase) zeroConfig

theorem synchronous_absorbing (initial : Config) :
    ExtendedRecoveryTime.Absorbing (InfiniteGridRandomDynamics.synchronous initial)
      zeroConfig := by
  intro η s t hst hs
  exact (isZero_iff_eq_zero _).mp
    ((InfiniteGridModel.system (InfiniteGridRandomDynamics.marks η)).synchronous_zero_persists
      initial ((isZero_iff_eq_zero _).mpr hs) hst)

theorem alternating_absorbing (initial : Config) (phase : Bool) :
    ExtendedRecoveryTime.Absorbing (InfiniteGridRandomDynamics.alternating initial phase)
      zeroConfig := by
  intro η s t hst hs
  exact (isZero_iff_eq_zero _).mp
    ((InfiniteGridModel.system (InfiniteGridRandomDynamics.marks η)).alternating_zero_persists
      initial phase ((isZero_iff_eq_zero _).mpr hs) hst)

theorem synchronous_measurable (initial : Config) : Measurable (synchronous initial) :=
  ExtendedRecoveryTime.time_measurable _ _
    (InfiniteGridRandomDynamics.synchronous_measurable initial)

theorem alternating_measurable (initial : Config) (phase : Bool) :
    Measurable (alternating initial phase) :=
  ExtendedRecoveryTime.time_measurable _ _
    (InfiniteGridRandomDynamics.alternating_measurable initial phase)

theorem synchronous_le_nat_iff (initial : Config) (η : Sample) (t : Nat) :
    synchronous initial η ≤ (t : ℕ∞) ↔
      InfiniteGridRandomDynamics.synchronous initial t η = zeroConfig :=
  ExtendedRecoveryTime.time_le_nat_iff_of_absorbing _ _ (synchronous_absorbing initial) η t

theorem alternating_le_nat_iff (initial : Config) (phase : Bool) (η : Sample) (t : Nat) :
    alternating initial phase η ≤ (t : ℕ∞) ↔
      InfiniteGridRandomDynamics.alternating initial phase t η = zeroConfig :=
  ExtendedRecoveryTime.time_le_nat_iff_of_absorbing _ _
    (alternating_absorbing initial phase) η t

theorem synchronous_tail_iff (initial : Config) (η : Sample) (t : Nat) :
    (t : ℕ∞) < synchronous initial η ↔
      InfiniteGridRandomDynamics.synchronous initial t η ≠ zeroConfig :=
  ExtendedRecoveryTime.time_gt_nat_iff_of_absorbing _ _ (synchronous_absorbing initial) η t

theorem alternating_tail_iff (initial : Config) (phase : Bool) (η : Sample) (t : Nat) :
    (t : ℕ∞) < alternating initial phase η ↔
      InfiniteGridRandomDynamics.alternating initial phase t η ≠ zeroConfig :=
  ExtendedRecoveryTime.time_gt_nat_iff_of_absorbing _ _
    (alternating_absorbing initial phase) η t

theorem measurableSet_synchronous_tail (initial : Config) (t : Nat) :
    MeasurableSet {η | (t : ℕ∞) < synchronous initial η} := by
  have hset : {η | (t : ℕ∞) < synchronous initial η} =
      {η | synchronous initial η ≤ (t : ℕ∞)}ᶜ := by
    ext η
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
  rw [hset]
  exact (ExtendedRecoveryTime.measurableSet_time_le_nat _ _
    (InfiniteGridRandomDynamics.synchronous_measurable initial) t).compl

theorem measurableSet_alternating_tail (initial : Config) (phase : Bool) (t : Nat) :
    MeasurableSet {η | (t : ℕ∞) < alternating initial phase η} := by
  have hset : {η | (t : ℕ∞) < alternating initial phase η} =
      {η | alternating initial phase η ≤ (t : ℕ∞)}ᶜ := by
    ext η
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
  rw [hset]
  exact (ExtendedRecoveryTime.measurableSet_time_le_nat _ _
    (InfiniteGridRandomDynamics.alternating_measurable initial phase) t).compl

theorem synchronous_eq_top_iff (initial : Config) (η : Sample) :
    synchronous initial η = ⊤ ↔
      ∀ t, InfiniteGridRandomDynamics.synchronous initial t η ≠ zeroConfig :=
  ExtendedRecoveryTime.time_eq_top_iff _ _ η

theorem alternating_eq_top_iff (initial : Config) (phase : Bool) (η : Sample) :
    alternating initial phase η = ⊤ ↔
      ∀ t, InfiniteGridRandomDynamics.alternating initial phase t η ≠ zeroConfig :=
  ExtendedRecoveryTime.time_eq_top_iff _ _ η

end MathResearchAnalysis.InfiniteGridRecoveryTime
