module

public import MathResearchAnalysis.OriginalQuadraticUpper
public import MathResearchAnalysis.MachineClockDynkin
public import Mathlib.Tactic

set_option autoImplicit false

/-! Explicit original-model law reduction and the full-square maximizer.
No finiteness of a recovery time or its extended expectation is assumed. -/

@[expose] public noncomputable section
open MeasureTheory
namespace MathResearchRevision.OriginalRecoveryResults
open MathResearchAnalysis
open PerturbationSymmetry

theorem finiteExpected_le_top (n : Nat) (g : SquareSpin.Config n) :
    OriginalRecoveryProfile.finiteExpected n g ≤
      OriginalRecoveryProfile.finiteExpected n (SquarePWMeasure.topConfig n) := by
  exact ExtendedRecoveryExpectation.expectation_mono _ _ _
    (SquareRecoveryTime.synchronous_le_top n g)

theorem tau_eq_full_square_finite (N : Nat) (hN : 2 ≤ N) :
    OriginalRecoveryProfile.tau N =
      OriginalRecoveryProfile.finiteExpected (N-2) (SquarePWMeasure.topConfig (N-2)) := by
  apply le_antisymm
  · rw [OriginalRecoveryProfile.tau_eq_normalizedTau N hN]
    apply iSup_le
    intro g
    apply iSup_le
    intro _
    exact finiteExpected_le_top (N-2) g
  · rw [← OriginalRecoveryProfile.expectedRecovery_finite_square]
    apply OriginalRecoveryProfile.expectedRecovery_le_tau
    rw [OriginalRecoveryProfile.distance_extend_top,
      PerturbationGeometry.original_side_sub_two N hN]

theorem tau_eq_full_square (N : Nat) (hN : 2 ≤ N) :
    OriginalRecoveryProfile.tau N =
      OriginalRecoveryProfile.expectedRecovery (squareConfig N) := by
  rw [tau_eq_full_square_finite N hN, ← OriginalRecoveryProfile.expectedRecovery_finite_square]
  congr 1
  funext z
  have he : N-2+2=N := by omega
  by_cases hz : InfiniteGridModel.Inside N z <;>
    simp [SquareGridEmbedding.extend, SquarePWMeasure.topConfig, squareConfig, he, hz]

theorem homogeneous_finite_square_map (n : Nat) (g : SquareSpin.Config n) :
    Measure.map (HomogeneousRecoveryTime.synchronous (SquareGridEmbedding.extend n g))
        InfiniteGridRandomDynamics.measure =
      Measure.map (SquareRecoveryTime.synchronous n g) (SquareRandomDynamics.measure n) := by
  have he : HomogeneousRecoveryTime.synchronous (SquareGridEmbedding.extend n g) =
      InfiniteGridRecoveryTime.synchronous (SquareGridEmbedding.extend n g) := by
    funext η
    exact HomogeneousRecoveryTime.synchronous_eq_zero_background (n+2) _
      (SquareGridEmbedding.extend_supported n g) η
  rw [he]
  exact SquareGridLaw.synchronous_recovery_map n g

/-- The entire first-hit law, rather than only its mean, has an exact finite representative. -/
theorem exists_finite_recovery_law (N : Nat) (hN : 2 ≤ N)
    (initial : InfiniteGridModel.Config) (hi : distance initial = (N : ℕ∞)) :
    ∃ g : SquareSpin.Config (N-2),
      Measure.map (HomogeneousRecoveryTime.synchronous initial) InfiniteGridRandomDynamics.measure =
        Measure.map (SquareRecoveryTime.synchronous (N-2) g) (SquareRandomDynamics.measure (N-2)) := by
  obtain ⟨a,b,g,he,_⟩ := PerturbationNormalization.exists_normal_form_exact N hN initial hi
  refine ⟨g, ?_⟩
  rw [he, HomogeneousRecoveryTime.synchronous_translate_map]
  cases b with
  | false => simpa only [Bool.false_eq_true, ite_false] using homogeneous_finite_square_map (N-2) g
  | true =>
    simp only [ite_true]
    rw [HomogeneousRecoveryTime.synchronous_complement_map]
    exact homogeneous_finite_square_map (N-2) g

theorem exists_finite_tail (N : Nat) (hN : 2 ≤ N)
    (initial : InfiniteGridModel.Config) (hi : distance initial = (N : ℕ∞)) :
    ∃ g : SquareSpin.Config (N-2), ∀ t : Nat,
      InfiniteGridRandomDynamics.measure {η | (t : ℕ∞) < HomogeneousRecoveryTime.synchronous initial η} =
        SquareRandomDynamics.measure (N-2) {η | (t : ℕ∞) < SquareRecoveryTime.synchronous (N-2) g η} := by
  obtain ⟨g,hg⟩ := exists_finite_recovery_law N hN initial hi
  refine ⟨g, fun t => ?_⟩
  have hset : MeasurableSet {x : ℕ∞ | (t : ℕ∞)<x} :=
    (Set.to_countable _).measurableSet
  have h := congrArg (fun μ : Measure ℕ∞ => μ {x | (t : ℕ∞)<x}) hg
  simpa only [Measure.map_apply (HomogeneousRecoveryTime.synchronous_measurable initial) hset,
    Measure.map_apply (SquareRecoveryTime.synchronous_measurable (N-2) g) hset,
    Set.preimage_ofPred_eq] using h

/-- Any nonnegative measurable function of the full extended recovery time
transports along this law equality, including powers and infinity-valued exponentials. -/
theorem exists_finite_observable_integrals (N : Nat) (hN : 2 ≤ N)
    (initial : InfiniteGridModel.Config) (hi : distance initial = (N : ℕ∞)) :
    ∃ g : SquareSpin.Config (N-2), ∀ Φ : ℕ∞ → ENNReal, Measurable Φ →
      (∫⁻ η, Φ (HomogeneousRecoveryTime.synchronous initial η)
        ∂InfiniteGridRandomDynamics.measure) =
      ∫⁻ η, Φ (SquareRecoveryTime.synchronous (N-2) g η)
        ∂SquareRandomDynamics.measure (N-2) := by
  obtain ⟨g,hg⟩ := exists_finite_recovery_law N hN initial hi
  refine ⟨g, fun Φ hΦ => ?_⟩
  rw [← lintegral_map hΦ (HomogeneousRecoveryTime.synchronous_measurable initial),
    ← lintegral_map hΦ (SquareRecoveryTime.synchronous_measurable (N-2) g), hg]

theorem original_recovery_block_tail (N : Nat) (hN : 16 ≤ N)
    (initial : InfiniteGridModel.Config) (hi : distance initial = (N : ℕ∞)) (j : Nat) :
    InfiniteGridRandomDynamics.measure
      {η | ((j*SyncUpperScale.block N : Nat) : ℕ∞) < HomogeneousRecoveryTime.synchronous initial η} ≤
        (1/2 : ENNReal)^j := by
  obtain ⟨g,hg⟩ := exists_finite_tail N (by omega) initial hi
  rw [hg]
  exact OriginalQuadraticUpper.recovery_block_tail N hN g j

end MathResearchRevision.OriginalRecoveryResults

#print axioms MathResearchRevision.OriginalRecoveryResults.finiteExpected_le_top
#print axioms MathResearchRevision.OriginalRecoveryResults.tau_eq_full_square_finite
#print axioms MathResearchRevision.OriginalRecoveryResults.tau_eq_full_square
#print axioms MathResearchRevision.OriginalRecoveryResults.homogeneous_finite_square_map
#print axioms MathResearchRevision.OriginalRecoveryResults.exists_finite_recovery_law
#print axioms MathResearchRevision.OriginalRecoveryResults.exists_finite_tail
#print axioms MathResearchRevision.OriginalRecoveryResults.exists_finite_observable_integrals
#print axioms MathResearchRevision.OriginalRecoveryResults.original_recovery_block_tail
