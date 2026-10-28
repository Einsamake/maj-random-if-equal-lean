module

public import FullBlockThreshold
public import MathResearchAnalysis.OriginalQuadraticRecovery
public import MathResearchAnalysis.ClockEndpointSurvival

set_option autoImplicit false

/- Isolated phase2 extension. Original formal sources and phase1 sources remain
   frozen. All probability inputs below are instantiated proved interfaces.
   Validation and independent source review are recorded separately. -/

@[expose] public noncomputable section

namespace MathResearchExploration.ImprovedOriginalLower

open MeasureTheory
open MathResearchAnalysis
open PerturbationSymmetry
open OriginalQuadraticLower (halfSide oddSide_le square_supported_mono extend_top_eq_square)
open scoped ENNReal

def quotient (L : Nat) : Nat := L^2/8000000

def rounds (L : Nat) : Nat := quotient L-1

theorem quotient_ge_thirtytwo (L : Nat) (hL : 250000 ≤ L) : 32 ≤ quotient L := by
  unfold quotient
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 8000000)).mpr
  have hs := Nat.mul_le_mul hL hL
  nlinarith

theorem quotient_positive (L : Nat) (hL : 250000 ≤ L) : 0 < quotient L := by
  have h := quotient_ge_thirtytwo L hL
  omega

theorem rounds_succ (L : Nat) (hL : 250000 ≤ L) : rounds L+1=quotient L := by
  unfold rounds
  have h := quotient_positive L hL
  omega

theorem quotient_mul_le_square (L : Nat) : quotient L*8000000 ≤ L^2 := by
  exact Nat.div_mul_le_self (L^2) 8000000

theorem square_lt_quotient_succ (L : Nat) : L^2 < (quotient L+1)*8000000 := by
  have hm := Nat.mod_lt (L^2) (by norm_num : 0 < 8000000)
  have hd := Nat.mod_add_div (L^2) 8000000
  unfold quotient
  omega

theorem side_le_sixtyfour_quotient_sub_twelve (L : Nat) (hL : 250000 ≤ L) :
    L ≤ 64*(quotient L-12) := by
  have hf := square_lt_quotient_succ L
  have hq := quotient_ge_thirtytwo L hL
  have hquad : 250000*L ≤ L^2 := by
    have hh := Nat.mul_le_mul_right L hL
    nlinarith
  have hlinear : L ≤ 32*quotient L+31 := by nlinarith
  omega

theorem square_exponential_bound (L : Nat) (hL : 250000 ≤ L) :
    64*(L : Real)^2 ≤ (2 : Real)^(quotient L) := by
  let r := quotient L-12
  have hq := quotient_ge_thirtytwo L hL
  have hr : 16 ≤ r := by dsimp [r]; omega
  have hs : (L : Real) ≤ 64*(r : Real) := by
    exact_mod_cast side_le_sixtyfour_quotient_sub_twelve L hL
  have hsq := mul_self_le_mul_self (Nat.cast_nonneg L : (0 : Real) ≤ L) hs
  have he := SyncLowerScale.square_exponential_bound r hr
  have heq : r+12=quotient L := by dsimp [r]; omega
  calc
    64*(L : Real)^2 ≤ 4096*(64*(r : Real)^2) := by nlinarith
    _ ≤ 4096*(2 : Real)^r := mul_le_mul_of_nonneg_left he (by norm_num)
    _ = (2 : Real)^(r+12) := by rw [pow_add]; norm_num; ring
    _ = (2 : Real)^(quotient L) := by rw [heq]

theorem scheduling_time_le_horizon (L : Nat) (hL : 250000 ≤ L) :
    SchedulingFailure.time (rounds L) ≤
      (FullBlockThreshold.quadraticHorizon L : Real) := by
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h
    exact h
  have hq := quotient_mul_le_square L
  have hq' : (quotient L : Real)*8000000 ≤ (L : Real)^2 := by exact_mod_cast hq
  have hq0 : (0 : Real) ≤ quotient L := Nat.cast_nonneg _
  unfold SchedulingFailure.time
  rw [rounds_succ L hL]
  change 8*Real.log 2*(quotient L : Real) ≤ (L : Real)^2/1000000
  have hm := mul_le_mul_of_nonneg_right hlog hq0
  nlinarith

theorem scheduling_error_le_quarter (L : Nat) (hL : 250000 ≤ L) :
    ((6 : Real)/5)*(ClippedSquareCoordinates.parameter L+2 : Real)^2*
      ((2 : Real)⁻¹)^(rounds L+1) ≤ (1/4 : Real) := by
  have hexp := square_exponential_bound L hL
  have hs : (ClippedSquareCoordinates.parameter L+2 : Real)=2*(L : Real)+1 := by
    have he := ClippedSquareCoordinates.parameter_side L (by omega : 1 ≤ L)
    exact_mod_cast he
  have hL' : (1 : Real) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hside : (2*(L : Real)+1)^2 ≤ 9*(L : Real)^2 := by nlinarith
  rw [rounds_succ L hL,hs,inv_pow,← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : (0 : Real) < 2^(quotient L))).mpr
  nlinarith

theorem rounds_lower_bound (L : Nat) (hL : 250000 ≤ L) :
    (L : Real)^2/16000000 ≤ (rounds L : Real) := by
  have hq := quotient_ge_thirtytwo L hL
  have hs := rounds_succ L hL
  have hd := square_lt_quotient_succ L
  have hr : L^2 ≤ rounds L*16000000 := by nlinarith
  have hr' : (L : Real)^2 ≤ (rounds L : Real)*16000000 := by exact_mod_cast hr
  linarith

theorem original_clock_survival_at_horizon_ge_half (L : Nat) (hL : 250000 ≤ L) :
    (1/2 : Real) ≤ ClockRecoveryComparison.clockProbability
      (ClippedSquareCoordinates.parameter L) (FullBlockThreshold.quadraticHorizon L) := by
  have hx := FullBlockThreshold.original_clock_extinction_at_quadraticHorizon_le_half L hL
  change (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)).real
    {z | ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L)
      (FullBlockThreshold.quadraticHorizon L : Real)
      (SquarePWMeasure.topConfig (ClippedSquareCoordinates.parameter L)) z = fun _ => false} ≤ (1/2 : Real) at hx
  rw [SynchronousQuadraticTail.clockProbability_eq_one_sub_extinction]
  linarith

theorem original_clock_survival_ge_half (L : Nat) (hL : 250000 ≤ L)
    (T : NNReal) (hT : T ≤ FullBlockThreshold.quadraticHorizon L) :
    (1/2 : Real) ≤ ClockRecoveryComparison.clockProbability
      (ClippedSquareCoordinates.parameter L) T := by
  have htime : (T : Real) ≤ (FullBlockThreshold.quadraticHorizon L : Real) := hT
  exact (original_clock_survival_at_horizon_ge_half L hL).trans
    (ClockEndpointSurvival.clockProbability_antitone _ htime)

theorem synchronous_tail_ge_quarter (L : Nat) (hL : 250000 ≤ L) :
    (1/4 : Real) ≤ InfiniteGridRandomDynamics.measure.real
      {η | (rounds L : ℕ∞) < InfiniteGridRecoveryTime.synchronous
        (SquareGridEmbedding.extend (ClippedSquareCoordinates.parameter L)
          (SquarePWMeasure.topConfig (ClippedSquareCoordinates.parameter L))) η} := by
  have hclock := original_clock_survival_ge_half L hL
    ⟨SchedulingFailure.time (rounds L),(SchedulingFailure.time_positive _).le⟩
    (scheduling_time_le_horizon L hL)
  have hcompare := (SquareGridLaw.two_way_clock_tail
    (ClippedSquareCoordinates.parameter L) false (rounds L)).1
  have herror := scheduling_error_le_quarter L hL
  change (1/2 : Real) ≤ ClockRecoveryComparison.clockProbability
    (ClippedSquareCoordinates.parameter L) (SchedulingFailure.time (rounds L)) at hclock
  linarith

theorem halfSide_large (N : Nat) (hN : 500001 ≤ N) : 250000 ≤ halfSide N := by
  unfold halfSide
  omega

theorem halfSide_ge_third (N : Nat) (hN : 6 ≤ N) :
    (N : Real)/3 ≤ (halfSide N : Real) := by
  have hn : N ≤ 3*halfSide N := by unfold halfSide; omega
  have hn' : (N : Real) ≤ 3*(halfSide N : Real) := by exact_mod_cast hn
  linarith

theorem rounds_quarter_ge_original_square (N : Nat) (hN : 500001 ≤ N) :
    (N : Real)^2/576000000 ≤ (rounds (halfSide N) : Real)/4 := by
  have hlower := rounds_lower_bound (halfSide N) (halfSide_large N hN)
  have hside := halfSide_ge_third N (by omega : 6 ≤ N)
  have hproduct := mul_nonneg (sub_nonneg.mpr hside)
    (show 0 ≤ (halfSide N : Real)+(N : Real)/3 by positivity)
  nlinarith

theorem synchronous_square_tail_ge_quarter (N : Nat) (hN : 500001 ≤ N) :
    (1/4 : Real) ≤ InfiniteGridRandomDynamics.measure.real
      {η | (rounds (halfSide N) : ℕ∞) <
        InfiniteGridRecoveryTime.synchronous (squareConfig N) η} := by
  have hL := halfSide_large N hN
  have hsmall := synchronous_tail_ge_quarter (halfSide N) hL
  have hside : ClippedSquareCoordinates.parameter (halfSide N)+2 ≤ (N-2)+2 := by
    rw [PerturbationGeometry.original_side_sub_two N (by omega : 2 ≤ N),
      ClippedSquareCoordinates.parameter_side (halfSide N) (by omega : 1 ≤ halfSide N)]
    exact oddSide_le N (by omega)
  have hsupp : InfiniteGridModel.Supported ((N-2)+2)
      (SquareGridEmbedding.extend (ClippedSquareCoordinates.parameter (halfSide N))
        (SquarePWMeasure.topConfig (ClippedSquareCoordinates.parameter (halfSide N)))) := by
    rw [extend_top_eq_square]
    exact square_supported_mono hside
  have hcomp := SquareGridLaw.supported_tail_le_top (N-2) _ hsupp (rounds (halfSide N))
  rw [extend_top_eq_square (N-2),PerturbationGeometry.original_side_sub_two N (by omega : 2 ≤ N)] at hcomp
  exact hsmall.trans hcomp

theorem square_expectedRecovery_quadratic_lower (N : Nat) (hN : 500001 ≤ N) :
    ENNReal.ofReal ((N : Real)^2/576000000) ≤
      OriginalRecoveryProfile.expectedRecovery (squareConfig N) := by
  have hz : HomogeneousRecoveryTime.synchronous (squareConfig N) =
      InfiniteGridRecoveryTime.synchronous (squareConfig N) := by
    funext η
    exact HomogeneousRecoveryTime.synchronous_eq_zero_background N _
      (square_supported_mono (le_refl N)) η
  have hprob : (1/4 : Real) ≤ InfiniteGridRandomDynamics.measure.real
      {η | (rounds (halfSide N) : ℕ∞) < HomogeneousRecoveryTime.synchronous (squareConfig N) η} := by
    rw [hz]
    exact synchronous_square_tail_ge_quarter N hN
  exact ExtendedTailLower.expectation_ge_of_quarter_tail InfiniteGridRandomDynamics.measure
    (HomogeneousRecoveryTime.synchronous (squareConfig N))
    (HomogeneousRecoveryTime.synchronous_measurable _) (rounds (halfSide N))
    hprob _ (rounds_quarter_ge_original_square N hN)

theorem translated_square_witness (N : Nat) (hN : 500001 ≤ N)
    (a : InfiniteGridModel.Site) (b : Bool) :
    distance (InfiniteGridTranslation.translate a
      (if b then InfiniteGridComplement.complementConfig (squareConfig N) else squareConfig N)) = (N : ℕ∞) ∧
    ENNReal.ofReal ((N : Real)^2/576000000) ≤ OriginalRecoveryProfile.expectedRecovery
      (InfiniteGridTranslation.translate a
        (if b then InfiniteGridComplement.complementConfig (squareConfig N) else squareConfig N)) := by
  constructor
  · rw [distance_translate]
    cases b <;> simp [distance_complement,distance_square]
  · rw [OriginalRecoveryProfile.expectedRecovery_translate]
    cases b with
    | false => simpa only [Bool.false_eq_true,ite_false] using square_expectedRecovery_quadratic_lower N hN
    | true => simpa only [ite_true,OriginalRecoveryProfile.expectedRecovery_complement] using square_expectedRecovery_quadratic_lower N hN

theorem tau_quadratic_lower_bound (N : Nat) (hN : 500001 ≤ N) :
    ENNReal.ofReal ((N : Real)^2/576000000) ≤ OriginalRecoveryProfile.tau N :=
  (square_expectedRecovery_quadratic_lower N hN).trans
    (OriginalRecoveryProfile.square_expectedRecovery_le_tau N)

theorem tau_quadratic_bounds (N : Nat) (hN : 500001 ≤ N) :
    ENNReal.ofReal ((N : Real)^2/576000000) ≤ OriginalRecoveryProfile.tau N ∧
      OriginalRecoveryProfile.tau N ≤ ENNReal.ofReal (664066*(N : Real)^2) :=
  ⟨tau_quadratic_lower_bound N hN,
    OriginalQuadraticUpper.tau_quadratic_upper_bound N (by omega)⟩

theorem tau_theta_quadratic :
    ∃ c C : Real, 0<c ∧ 0<C ∧ ∃ N₀ : Nat, ∀ N : Nat, N₀≤N →
      ENNReal.ofReal (c*(N : Real)^2) ≤ OriginalRecoveryProfile.tau N ∧
        OriginalRecoveryProfile.tau N ≤ ENNReal.ofReal (C*(N : Real)^2) := by
  refine ⟨1/576000000,664066,by norm_num,by norm_num,500001,?_⟩
  intro N hN
  have he : (1/576000000 : Real)*(N : Real)^2=(N : Real)^2/576000000 := by ring
  rw [he]
  exact tau_quadratic_bounds N hN

#print axioms quotient
#print axioms rounds
#print axioms quotient_ge_thirtytwo
#print axioms quotient_positive
#print axioms rounds_succ
#print axioms quotient_mul_le_square
#print axioms square_lt_quotient_succ
#print axioms side_le_sixtyfour_quotient_sub_twelve
#print axioms square_exponential_bound
#print axioms scheduling_time_le_horizon
#print axioms scheduling_error_le_quarter
#print axioms rounds_lower_bound
#print axioms original_clock_survival_at_horizon_ge_half
#print axioms original_clock_survival_ge_half
#print axioms synchronous_tail_ge_quarter
#print axioms halfSide_large
#print axioms halfSide_ge_third
#print axioms rounds_quarter_ge_original_square
#print axioms synchronous_square_tail_ge_quarter
#print axioms square_expectedRecovery_quadratic_lower
#print axioms translated_square_witness
#print axioms tau_quadratic_lower_bound
#print axioms tau_quadratic_bounds
#print axioms tau_theta_quadratic

end MathResearchExploration.ImprovedOriginalLower
