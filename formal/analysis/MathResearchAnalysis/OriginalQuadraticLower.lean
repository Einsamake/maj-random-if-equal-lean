module

public import MathResearchAnalysis.OriginalRecoveryProfile
public import MathResearchAnalysis.SynchronousQuadraticTail
public import MathResearchAnalysis.ExtendedTailLower

set_option autoImplicit false

/-!
# Original-size geometry for a quadratic recovery lower bound
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace MathResearchAnalysis.OriginalQuadraticLower

open PerturbationSymmetry

/-- Half-side of the largest odd square no larger than the original side. -/
def halfSide (N : Nat) : Nat := (N-1)/2

theorem halfSide_large (N : Nat) (hN : 786432000 ≤ N) :
    196608000 ≤ halfSide N := by
  unfold halfSide
  omega

theorem oddSide_le (N : Nat) (hN : 1 ≤ N) : 2*halfSide N+1 ≤ N := by
  unfold halfSide
  omega

theorem halfSide_ge_sixth (N : Nat) (hN : 6 ≤ N) :
    (N : Real)/6 ≤ (halfSide N : Real) := by
  have hn : N ≤ 6*halfSide N := by
    unfold halfSide
    omega
  have hn' : (N : Real) ≤ 6*(halfSide N : Real) := by exact_mod_cast hn
  linarith

theorem inside_mono {M N : Nat} (hMN : M ≤ N) {z : InfiniteGridModel.Site}
    (hz : InfiniteGridModel.Inside M z) : InfiniteGridModel.Inside N z := by
  unfold InfiniteGridModel.Inside at *
  omega

theorem square_supported_mono {M N : Nat} (hMN : M ≤ N) :
    InfiniteGridModel.Supported N (squareConfig M) := by
  intro z hz
  have hsmall : ¬InfiniteGridModel.Inside M z := fun hs => hz (inside_mono hMN hs)
  simp only [squareConfig, hsmall, decide_false]

theorem extend_top_eq_square (n : Nat) :
    SquareGridEmbedding.extend n (SquarePWMeasure.topConfig n) = squareConfig (n+2) := by
  funext z
  by_cases hz : InfiniteGridModel.Inside (n+2) z <;>
    simp [SquareGridEmbedding.extend, SquarePWMeasure.topConfig, squareConfig, hz]


/-- A round threshold quadratic in the original side, with floor/parity retained. -/
theorem rounds_quarter_ge_original_square (N : Nat) (hN : 786432000 ≤ N) :
    (N : Real)^2/56623104000 ≤ (SyncLowerScale.rounds (halfSide N) : Real)/4 := by
  have hlower := SyncLowerScale.rounds_lower_bound (halfSide N) (halfSide_large N hN)
  have hside := halfSide_ge_sixth N (by omega : 6 ≤ N)
  have hN0 : 0 ≤ (N : Real) := Nat.cast_nonneg N
  have hL0 : 0 ≤ (halfSide N : Real) := Nat.cast_nonneg _
  have hproduct := mul_nonneg (sub_nonneg.mpr hside)
    (show 0 ≤ (halfSide N : Real)+(N : Real)/6 by positivity)
  nlinarith

/-- The probability bound is for the original synchronous infinite-lattice law,
with the given original side, for both odd and even sizes. -/
theorem synchronous_square_tail_ge_quarter (N : Nat) (hN : 786432000 ≤ N) :
    (1/4 : Real) ≤ InfiniteGridRandomDynamics.measure.real
      {η | (SyncLowerScale.rounds (halfSide N) : ℕ∞) <
        InfiniteGridRecoveryTime.synchronous (squareConfig N) η} := by
  have hL := halfSide_large N hN
  have hsmall := SynchronousQuadraticTail.synchronous_tail_ge_quarter (halfSide N) hL
  have hside : ClippedSquareCoordinates.parameter (halfSide N)+2 ≤ (N-2)+2 := by
    rw [PerturbationGeometry.original_side_sub_two N (by omega : 2 ≤ N),
      ClippedSquareCoordinates.parameter_side (halfSide N) (by omega : 1 ≤ halfSide N)]
    exact oddSide_le N (by omega)
  have hsupp : InfiniteGridModel.Supported ((N-2)+2)
      (SquareGridEmbedding.extend (ClippedSquareCoordinates.parameter (halfSide N))
        (SquarePWMeasure.topConfig (ClippedSquareCoordinates.parameter (halfSide N)))) := by
    rw [extend_top_eq_square]
    exact square_supported_mono hside
  have hcomp := SquareGridLaw.supported_tail_le_top (N-2) _ hsupp
    (SyncLowerScale.rounds (halfSide N))
  rw [extend_top_eq_square (N-2), PerturbationGeometry.original_side_sub_two N (by omega : 2 ≤ N)] at hcomp
  exact hsmall.trans hcomp

/-- Actual homogeneous recovery retains infinity; a positive probability of
surviving quadratically many synchronous rounds pays a quadratic expectation. -/
theorem square_expectedRecovery_quadratic_lower (N : Nat) (hN : 786432000 ≤ N) :
    ENNReal.ofReal ((N : Real)^2/56623104000) ≤
      OriginalRecoveryProfile.expectedRecovery (squareConfig N) := by
  have hz : HomogeneousRecoveryTime.synchronous (squareConfig N) =
      InfiniteGridRecoveryTime.synchronous (squareConfig N) := by
    funext η
    exact HomogeneousRecoveryTime.synchronous_eq_zero_background N _
      (square_supported_mono (le_refl N)) η
  have hprob : (1/4 : Real) ≤ InfiniteGridRandomDynamics.measure.real
      {η | (SyncLowerScale.rounds (halfSide N) : ℕ∞) <
        HomogeneousRecoveryTime.synchronous (squareConfig N) η} := by
    rw [hz]
    exact synchronous_square_tail_ge_quarter N hN
  exact ExtendedTailLower.expectation_ge_of_quarter_tail InfiniteGridRandomDynamics.measure
    (HomogeneousRecoveryTime.synchronous (squareConfig N))
    (HomogeneousRecoveryTime.synchronous_measurable _) (SyncLowerScale.rounds (halfSide N))
    hprob _ (rounds_quarter_ge_original_square N hN)

/-- A completely instantiated exact-original-size lower bound. The optimization
uses distance exactly N; no tail, drift, or comparison bound is an input. -/
theorem tau_quadratic_lower_bound (N : Nat) (hN : 786432000 ≤ N) :
    ENNReal.ofReal ((N : Real)^2/56623104000) ≤ OriginalRecoveryProfile.tau N :=
  (square_expectedRecovery_quadratic_lower N hN).trans
    (OriginalRecoveryProfile.square_expectedRecovery_le_tau N)

/-- A positive constant and finite threshold for the original worst extended
expectation. This asserts only the lower half of the intended Theta theorem. -/
theorem exists_positive_quadratic_lower :
    ∃ c : Real, 0 < c ∧ ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N →
      ENNReal.ofReal (c*(N : Real)^2) ≤ OriginalRecoveryProfile.tau N := by
  refine ⟨1/56623104000, by norm_num, 786432000, ?_⟩
  intro N hN
  have he : (1/56623104000 : Real)*(N : Real)^2 = (N : Real)^2/56623104000 := by ring
  rw [he]
  exact tau_quadratic_lower_bound N hN

end MathResearchAnalysis.OriginalQuadraticLower


