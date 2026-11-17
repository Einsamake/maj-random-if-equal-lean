module
public import OriginalRecoveryResults
public import SharpRecoveryTail
public import RecoveryMoments
public import ImprovedOriginalLower
public import MathResearchAnalysis.MachineClockGenerator
set_option autoImplicit false

/-! Closed original-model statements for the six A/B tasks.  Initial states
range over both backgrounds at exact enclosing-square side N.  The measure
is the original infinite-grid fair-mark law and the hitting time retains top. -/
@[expose] public noncomputable section
namespace MathResearchRevision.OriginalConsequences
open MeasureTheory
open MathResearchAnalysis
open PerturbationSymmetry
open OriginalRecoveryResults

theorem quadratic_bounds (N : Nat) (hN : 500001 ≤ N) :
    ENNReal.ofReal ((N : Real)^2/576000000) ≤ OriginalRecoveryProfile.tau N ∧
      OriginalRecoveryProfile.tau N ≤ ENNReal.ofReal (664066*(N : Real)^2) :=
  MathResearchExploration.ImprovedOriginalLower.tau_quadratic_bounds N hN

theorem original_sharp_block_tail (N : Nat) (hN : 16≤N)
    (initial : InfiniteGridModel.Config) (hi : distance initial = (N : ℕ∞)) (j : Nat) :
    InfiniteGridRandomDynamics.measure
      {η | ((j*SyncUpperScale.block N : Nat) : ℕ∞)<HomogeneousRecoveryTime.synchronous initial η} ≤
        (ENNReal.ofReal (SharpRecoveryTail.failure N))^j := by
  obtain ⟨g,hg⟩ := exists_finite_tail N (by omega) initial hi
  rw [hg]
  exact SharpRecoveryTail.recovery_block_tail N (by omega) g j

theorem original_sharp_expectation (N : Nat) (hN : 16≤N)
    (initial : InfiniteGridModel.Config) (hi : distance initial = (N : ℕ∞)) :
    OriginalRecoveryProfile.expectedRecovery initial ≤
      ENNReal.ofReal ((SyncUpperScale.block N : Real)/(1-SharpRecoveryTail.failure N)) :=
  (OriginalRecoveryProfile.expectedRecovery_le_tau N initial hi).trans (SharpRecoveryTail.tau_le N hN)

theorem original_ae_finite (N : Nat) (hN : 16≤N)
    (initial : InfiniteGridModel.Config) (hi : distance initial = (N : ℕ∞)) :
    ∀ᵐ η ∂InfiniteGridRandomDynamics.measure,
      HomogeneousRecoveryTime.synchronous initial η < ⊤ :=
  ExtendedBlockTail.ae_lt_top InfiniteGridRandomDynamics.measure
    (HomogeneousRecoveryTime.synchronous initial)
    (HomogeneousRecoveryTime.synchronous_measurable initial) (SyncUpperScale.block N)
    (SyncUpperScale.block_positive N) (original_recovery_block_tail N hN initial hi)

theorem original_rpow_le (N : Nat) (hN : 16≤N)
    (initial : InfiniteGridModel.Config) (hi : distance initial = (N : ℕ∞))
    (r : Real) (hr : 0<r) :
    (∫⁻ η, (HomogeneousRecoveryTime.synchronous initial η : ENNReal)^r
      ∂InfiniteGridRandomDynamics.measure) ≤
      RecoveryMoments.momentConstant r*(N : ENNReal)^(2*r) := by
  obtain ⟨g,hg⟩ := exists_finite_observable_integrals N (by omega) initial hi
  rw [hg (fun t : ℕ∞ => (t : ENNReal)^r) (measurable_of_countable _)]
  exact RecoveryMoments.recovery_rpow_le N hN g r hr

theorem original_rpow_lt_top (N : Nat) (hN : 16≤N)
    (initial : InfiniteGridModel.Config) (hi : distance initial = (N : ℕ∞))
    (r : Real) (hr : 0<r) :
    (∫⁻ η, (HomogeneousRecoveryTime.synchronous initial η : ENNReal)^r
      ∂InfiniteGridRandomDynamics.measure) < ⊤ := by
  obtain ⟨g,hg⟩ := exists_finite_observable_integrals N (by omega) initial hi
  rw [hg (fun t : ℕ∞ => (t : ENNReal)^r) (measurable_of_countable _)]
  exact RecoveryMoments.recovery_rpow_lt_top N hN g r hr

theorem original_exponential_le (N : Nat) (hN : 16≤N)
    (initial : InfiniteGridModel.Config) (hi : distance initial = (N : ℕ∞))
    (lambda : Real) (hl : 0<lambda) :
    (∫⁻ η, RecoveryMoments.extendedExp lambda ((N : Real)^2)
      (HomogeneousRecoveryTime.synchronous initial η) ∂InfiniteGridRandomDynamics.measure) ≤
      RecoveryMoments.expConstant lambda := by
  obtain ⟨g,hg⟩ := exists_finite_observable_integrals N (by omega) initial hi
  rw [hg (RecoveryMoments.extendedExp lambda ((N : Real)^2)) (measurable_of_countable _)]
  exact RecoveryMoments.recovery_exponential_le N hN g lambda hl

theorem original_exponential_lt_top (N : Nat) (hN : 16≤N)
    (initial : InfiniteGridModel.Config) (hi : distance initial = (N : ℕ∞))
    (lambda : Real) (hl : 0<lambda) (hl' : 332033*lambda<Real.log 2) :
    (∫⁻ η, RecoveryMoments.extendedExp lambda ((N : Real)^2)
      (HomogeneousRecoveryTime.synchronous initial η) ∂InfiniteGridRandomDynamics.measure) < ⊤ :=
  (original_exponential_le N hN initial hi lambda hl).trans_lt
    (RecoveryMoments.expConstant_lt_top lambda hl')

theorem finite_machine_dynkin {A : Type*} [Fintype A] (L : Nat)
    (step : DropletClockLaw.Vertex L → Bool → A → A) (initial : A)
    (F : A → Real) (T : NNReal) :
    (∫ z : DropletClockLaw.Sample L,
      F (FiniteObservedClockState.endpoint L step initial (T : Real) z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    F initial + ∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : DropletClockLaw.Sample L,
      MachineClockGenerator.generator L step F (FiniteObservedClockState.endpoint L step initial u z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) :=
  MachineClockGenerator.expected_observable_dynkin_current L step initial F T

#print axioms quadratic_bounds
#print axioms original_sharp_block_tail
#print axioms original_sharp_expectation
#print axioms original_ae_finite
#print axioms original_rpow_le
#print axioms original_rpow_lt_top
#print axioms original_exponential_le
#print axioms original_exponential_lt_top
#print axioms finite_machine_dynkin
end MathResearchRevision.OriginalConsequences
