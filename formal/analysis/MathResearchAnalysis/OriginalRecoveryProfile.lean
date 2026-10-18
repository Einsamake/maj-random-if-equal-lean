module

public import MathResearchAnalysis.PerturbationNormalization
public import MathResearchAnalysis.HomogeneousRecoveryTime
public import MathResearchAnalysis.ExtendedRecoveryExpectation
public import MathResearchAnalysis.SquareGridLaw
public import MathResearchAnalysis.SmallDiameterRecovery
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

set_option autoImplicit false

/-!
# The original exact-diameter worst extended recovery expectation

The target is the two homogeneous configurations. Expectations retain
infinity. The original scale is the minimum translated half-open-square side,
and the optimization uses exact equality to that scale. For N ≥ 2 this
optimization is reduced to a genuine finite set of patterns of side N and
its maximum is attained. No quadratic bound or finite expectation is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace MathResearchAnalysis.OriginalRecoveryProfile

open PerturbationSymmetry

abbrev Config := InfiniteGridModel.Config

def expectedRecovery (initial : Config) : ℝ≥0∞ :=
  ExtendedRecoveryExpectation.expectation InfiniteGridRandomDynamics.measure
    (HomogeneousRecoveryTime.synchronous initial)

def tau (N : Nat) : ℝ≥0∞ :=
  ⨆ initial : Config, ⨆ (_ : distance initial = (N : ℕ∞)), expectedRecovery initial

def finiteExpected (n : Nat) (g : SquareSpin.Config n) : ℝ≥0∞ :=
  ExtendedRecoveryExpectation.expectation (SquareRandomDynamics.measure n)
    (SquareRecoveryTime.synchronous n g)

def normalizedTau (N : Nat) : ℝ≥0∞ :=
  ⨆ g : SquareSpin.Config (N - 2),
    ⨆ (_ : distance (SquareGridEmbedding.extend (N - 2) g) = (N : ℕ∞)), finiteExpected (N - 2) g

theorem expectedRecovery_translate (a : InfiniteGridModel.Site) (initial : Config) :
    expectedRecovery (InfiniteGridTranslation.translate a initial) = expectedRecovery initial := by
  exact ExtendedRecoveryExpectation.expectation_eq_of_map_eq _ _ _ _
    (HomogeneousRecoveryTime.synchronous_measurable _)
    (HomogeneousRecoveryTime.synchronous_measurable _)
    (HomogeneousRecoveryTime.synchronous_translate_map a initial)

theorem expectedRecovery_complement (initial : Config) :
    expectedRecovery (InfiniteGridComplement.complementConfig initial) = expectedRecovery initial := by
  exact ExtendedRecoveryExpectation.expectation_eq_of_map_eq _ _ _ _
    (HomogeneousRecoveryTime.synchronous_measurable _)
    (HomogeneousRecoveryTime.synchronous_measurable _)
    (HomogeneousRecoveryTime.synchronous_complement_map initial)

theorem expectedRecovery_finite_square (n : Nat) (g : SquareSpin.Config n) :
    expectedRecovery (SquareGridEmbedding.extend n g) = finiteExpected n g := by
  have ht : HomogeneousRecoveryTime.synchronous (SquareGridEmbedding.extend n g) =
      InfiniteGridRecoveryTime.synchronous (SquareGridEmbedding.extend n g) := by
    funext η
    exact HomogeneousRecoveryTime.synchronous_eq_zero_background (n + 2) _
      (SquareGridEmbedding.extend_supported n g) η
  unfold expectedRecovery finiteExpected
  rw [ht]
  exact ExtendedRecoveryExpectation.expectation_eq_of_map_eq _ _ _ _
    (InfiniteGridRecoveryTime.synchronous_measurable _)
    (SquareRecoveryTime.synchronous_measurable n g) (SquareGridLaw.synchronous_recovery_map n g)

theorem expectedRecovery_le_tau (N : Nat) (initial : Config) (h : distance initial = (N : ℕ∞)) :
    expectedRecovery initial ≤ tau N :=
  le_iSup_of_le initial (le_iSup_of_le h le_rfl)

theorem tau_le_iff (N : Nat) (bound : ℝ≥0∞) :
    tau N ≤ bound ↔ ∀ initial : Config, distance initial = (N : ℕ∞) → expectedRecovery initial ≤ bound := by
  simp only [tau, iSup_le_iff]

theorem distance_extend_top (n : Nat) :
    distance (SquareGridEmbedding.extend n (SquarePWMeasure.topConfig n)) = ((n + 2 : Nat) : ℕ∞) := by
  have he : SquareGridEmbedding.extend n (SquarePWMeasure.topConfig n) = squareConfig (n + 2) := by
    funext z
    by_cases hz : InfiniteGridModel.Inside (n + 2) z <;>
      simp [SquareGridEmbedding.extend, SquarePWMeasure.topConfig, squareConfig, hz]
  rw [he]
  exact distance_square (n + 2)

theorem exact_patterns_nonempty (N : Nat) (hN : 2 ≤ N) :
    ∃ g : SquareSpin.Config (N - 2),
      distance (SquareGridEmbedding.extend (N - 2) g) = (N : ℕ∞) := by
  refine ⟨SquarePWMeasure.topConfig (N - 2), ?_⟩
  rw [distance_extend_top, PerturbationGeometry.original_side_sub_two N hN]

theorem tau_eq_normalizedTau (N : Nat) (hN : 2 ≤ N) : tau N = normalizedTau N := by
  apply le_antisymm
  · apply iSup_le
    intro initial
    apply iSup_le
    intro h
    obtain ⟨a, b, g, he, hg⟩ := PerturbationNormalization.exists_normal_form_exact N hN initial h
    rw [he, expectedRecovery_translate]
    have hle : finiteExpected (N - 2) g ≤ normalizedTau N :=
      le_iSup_of_le g (le_iSup_of_le hg le_rfl)
    cases b with
    | false => simpa only [Bool.false_eq_true, ite_false, expectedRecovery_finite_square] using hle
    | true => simpa only [ite_true, expectedRecovery_complement, expectedRecovery_finite_square] using hle
  · apply iSup_le
    intro g
    apply iSup_le
    intro hg
    rw [← expectedRecovery_finite_square]
    exact expectedRecovery_le_tau N _ hg

theorem tau_attained_finite_pattern (N : Nat) (hN : 2 ≤ N) :
    ∃ g : SquareSpin.Config (N - 2),
      distance (SquareGridEmbedding.extend (N - 2) g) = (N : ℕ∞) ∧
        finiteExpected (N - 2) g = tau N := by
  let K := {g : SquareSpin.Config (N - 2) |
    distance (SquareGridEmbedding.extend (N - 2) g) = (N : ℕ∞)}
  have hn : Nonempty K := by
    obtain ⟨g, hg⟩ := exact_patterns_nonempty N hN
    exact ⟨⟨g, hg⟩⟩
  let : Nonempty K := hn
  have hs : (⨆ g : K, finiteExpected (N - 2) g.1) = normalizedTau N := by
    apply le_antisymm
    · apply iSup_le
      intro g
      exact le_iSup_of_le g.1 (le_iSup_of_le g.2 le_rfl)
    · apply iSup_le
      intro g
      apply iSup_le
      intro hg
      exact le_iSup_of_le (⟨g, hg⟩ : K) le_rfl
  obtain ⟨g, hg⟩ := Finite.ciSup_mem (fun g : K => finiteExpected (N - 2) g.1)
  refine ⟨g.1, g.2, ?_⟩
  calc
    finiteExpected (N - 2) g.1 = ⨆ q : K, finiteExpected (N - 2) q.1 := hg
    _ = normalizedTau N := hs
    _ = tau N := (tau_eq_normalizedTau N hN).symm

theorem tau_attained (N : Nat) (hN : 2 ≤ N) :
    ∃ initial : Config, distance initial = (N : ℕ∞) ∧ expectedRecovery initial = tau N := by
  obtain ⟨g, hg, he⟩ := tau_attained_finite_pattern N hN
  exact ⟨SquareGridEmbedding.extend (N - 2) g, hg,
    (expectedRecovery_finite_square (N - 2) g).trans he⟩

theorem square_expectedRecovery_le_tau (N : Nat) : expectedRecovery (squareConfig N) ≤ tau N :=
  expectedRecovery_le_tau N _ (distance_square N)

theorem distance_zero_iff_homogeneous (initial : Config) :
    distance initial = 0 ↔ HomogeneousRecoveryTime.Homogeneous initial := by
  constructor
  · intro h
    obtain ⟨b, _, hb⟩ := (distance_eq_nat_iff initial 0).mp h
    have hd := (PerturbationGeometry.diameter_eq_zero_iff _).mp hb
    have he : initial = (fun _ => b) := by
      funext z
      by_contra hz
      have hm : z ∈ PerturbationGeometry.difference initial b := hz
      rw [hd] at hm
      exact hm
    cases b with
    | false => exact Or.inl he
    | true => exact Or.inr he
  · rintro (h | h)
    · have hf : PerturbationGeometry.FinitePerturbation initial false := by
        rw [h]
        simpa only [PerturbationGeometry.FinitePerturbation, PerturbationGeometry.difference,
          ne_eq, not_true_eq_false, Set.ofPred_false] using (Set.finite_empty : (∅ : Set InfiniteGridModel.Site).Finite)
      rw [distance_of_finite_background initial false hf]
      apply (PerturbationGeometry.diameter_eq_zero_iff _).mpr
      ext z
      simp [PerturbationGeometry.difference, h]
    · have hf : PerturbationGeometry.FinitePerturbation initial true := by
        rw [h]
        simpa only [PerturbationGeometry.FinitePerturbation, PerturbationGeometry.difference,
          ne_eq, not_true_eq_false, Set.ofPred_false] using (Set.finite_empty : (∅ : Set InfiniteGridModel.Site).Finite)
      rw [distance_of_finite_background initial true hf]
      apply (PerturbationGeometry.diameter_eq_zero_iff _).mpr
      ext z
      simp [PerturbationGeometry.difference, h]

theorem expectedRecovery_homogeneous (initial : Config)
    (h : HomogeneousRecoveryTime.Homogeneous initial) : expectedRecovery initial = 0 := by
  have ht : HomogeneousRecoveryTime.synchronous initial = (fun _ => 0) :=
    funext (HomogeneousRecoveryTime.synchronous_eq_zero_of_homogeneous initial h)
  unfold expectedRecovery
  rw [ht]
  exact ExtendedRecoveryExpectation.expectation_zero _

theorem tau_zero : tau 0 = 0 := by
  apply le_antisymm
  · apply (tau_le_iff 0 0).mpr
    intro initial h
    exact le_of_eq (expectedRecovery_homogeneous initial ((distance_zero_iff_homogeneous initial).mp h))
  · exact bot_le

theorem expectedRecovery_eq_one_of_distance_one (initial : Config)
    (h : distance initial = (1 : ℕ∞)) : expectedRecovery initial = 1 := by
  have ht : HomogeneousRecoveryTime.synchronous initial = (fun _ => 1) :=
    funext (SmallDiameterRecovery.synchronous_eq_one_of_distance_one initial h)
  unfold expectedRecovery
  rw [ht, ExtendedRecoveryExpectation.expectation_const]
  simp

theorem tau_one : tau 1 = 1 := by
  apply le_antisymm
  · apply (tau_le_iff 1 1).mpr
    intro initial h
    exact le_of_eq (expectedRecovery_eq_one_of_distance_one initial h)
  · have h := expectedRecovery_le_tau 1 (squareConfig 1) (distance_square 1)
    rw [expectedRecovery_eq_one_of_distance_one _ (distance_square 1)] at h
    exact h

theorem tau_attained_all (N : Nat) :
    ∃ initial : Config, distance initial = (N : ℕ∞) ∧ expectedRecovery initial = tau N := by
  by_cases hN : 2 ≤ N
  · exact tau_attained N hN
  · have hsmall : N = 0 ∨ N = 1 := by omega
    rcases hsmall with rfl | rfl
    · refine ⟨squareConfig 0, distance_square 0, ?_⟩
      rw [tau_zero]
      exact expectedRecovery_homogeneous _ ((distance_zero_iff_homogeneous _).mp (distance_square 0))
    · refine ⟨squareConfig 1, distance_square 1, ?_⟩
      rw [tau_one]
      exact expectedRecovery_eq_one_of_distance_one _ (distance_square 1)

end MathResearchAnalysis.OriginalRecoveryProfile
