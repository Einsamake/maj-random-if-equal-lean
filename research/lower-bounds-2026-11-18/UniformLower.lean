module
public import DirectionalDrift
public import SquareSurvival
public import Mathlib.Analysis.Complex.ExponentialBounds
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchLower
open MathResearchAnalysis MeasureTheory
open PerturbationSymmetry (squareConfig)
open OriginalQuadraticLower (halfSide)
open scoped ENNReal

abbrev survival (N k : ℕ) : ℝ := InfiniteGridRandomDynamics.measure.real
  {η | (k : ℕ∞) < HomogeneousRecoveryTime.synchronous (squareConfig N) η}

/-- Error of the actual clock comparison once the light cone can reach the centre. -/
theorem scheduling_error_small {L k : ℕ} (hL : 999999 ≤ L) (hk : L ≤ k) :
    (6/5 : ℝ)*(ClippedSquareCoordinates.parameter L+2 : ℝ)^2*((2 : ℝ)⁻¹)^(k+1) ≤ 1/1000 := by
  let r := k+1-12
  have hr : 16 ≤ r := by dsimp [r]; omega
  have he : r+12=k+1 := by dsimp [r]; omega
  have hs : 2*L+1 ≤ 3*r := by dsimp [r]; omega
  have hside : (ClippedSquareCoordinates.parameter L+2 : ℝ) ≤ 3*(r : ℝ) := by
    exact_mod_cast (ClippedSquareCoordinates.parameter_side L (by omega)).le.trans hs
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ (ClippedSquareCoordinates.parameter L+2 : ℝ)) hside
  have hpow := SyncLowerScale.square_exponential_bound r hr
  rw [inv_pow, ← div_eq_mul_inv, ← he, pow_add]
  apply (div_le_iff₀ (by positivity)).mpr
  norm_num
  nlinarith only [hsq,hpow,sq_nonneg (r : ℝ)]

theorem inner_tail_le_outer {N : ℕ} (hN : 3 ≤ N) (k : ℕ) :
    InfiniteGridRandomDynamics.measure.real {η | (k : ℕ∞) < InfiniteGridRecoveryTime.synchronous
      (SquareGridEmbedding.extend (ClippedSquareCoordinates.parameter (halfSide N))
        (SquarePWMeasure.topConfig (ClippedSquareCoordinates.parameter (halfSide N)))) η} ≤ survival N k := by
  have hs : ClippedSquareCoordinates.parameter (halfSide N)+2 ≤ N-2+2 := by
    rw [ClippedSquareCoordinates.parameter_side _ (by unfold halfSide; omega),
      PerturbationGeometry.original_side_sub_two N (by omega)]
    exact OriginalQuadraticLower.oddSide_le N (by omega)
  have hsup : InfiniteGridModel.Supported (N-2+2)
      (SquareGridEmbedding.extend (ClippedSquareCoordinates.parameter (halfSide N))
        (SquarePWMeasure.topConfig (ClippedSquareCoordinates.parameter (halfSide N)))) := by
    rw [OriginalQuadraticLower.extend_top_eq_square]
    exact OriginalQuadraticLower.square_supported_mono hs
  have h := SquareGridLaw.supported_tail_le_top (N-2) _ hsup k
  rw [OriginalQuadraticLower.extend_top_eq_square (N-2),
    PerturbationGeometry.original_side_sub_two N (by omega)] at h
  have hz : HomogeneousRecoveryTime.synchronous (squareConfig N) = InfiniteGridRecoveryTime.synchronous (squareConfig N) :=
    funext (HomogeneousRecoveryTime.synchronous_eq_zero_background N _ (OriginalQuadraticLower.square_supported_mono (le_refl N)))
  simpa only [survival,hz] using h

theorem clock_bound_numeric {L k : ℕ} (hL : 999999 ≤ L) :
    ((6*(L : ℝ)+6)*SchedulingFailure.time k+((L : ℝ)+2)*(4*L+2)) / ((L : ℝ)^3/12500)
      ≤ 59/1000 + 420000*((k : ℝ)+1)/(L : ℝ)^2 := by
  have hl : (999999 : ℝ) ≤ L := by exact_mod_cast hL
  have hl0 : 0 < (L : ℝ) := by linarith
  have hlog : 8*Real.log 2 ≤ 139/25 := by linarith [Real.log_two_lt_d9]
  have ht : SchedulingFailure.time k ≤ (139/25)*((k : ℝ)+1) := by
    unfold SchedulingFailure.time
    push_cast
    exact mul_le_mul_of_nonneg_right hlog (by positivity)
  have hcoef : 6*(L : ℝ)+6 ≤ (601/100)*(L : ℝ) := by linarith
  have hraw := mul_le_mul hcoef ht (SchedulingFailure.time_positive k).le (by positivity)
  have hsq := mul_le_mul_of_nonneg_right hl (sq_nonneg (L : ℝ))
  have hlin := mul_le_mul_of_nonneg_right hl hl0.le
  have hcross : 0 ≤ (L : ℝ)*((k : ℝ)+1) := by positivity
  field_simp [ne_of_gt hl0]
  nlinarith only [hraw,hsq,hlin,hl,hcross]

/-- An affine lower envelope for the original square's survival curve. -/
theorem square_survival_envelope {N : ℕ} (hN : 2000000 ≤ N) (k : ℕ) :
    (47/50 - survival N k)*(halfSide N : ℝ)^2 ≤ 420000*((k : ℝ)+1) := by
  let L := halfSide N
  have hL : 999999 ≤ L := by dsimp [L,halfSide]; omega
  change (47/50 - survival N k)*(L : ℝ)^2 ≤ _
  by_cases hsmall : 2*k < N
  · have he : {η | (k : ℕ∞) < HomogeneousRecoveryTime.synchronous (squareConfig N) η} = Set.univ :=
      Set.eq_univ_of_forall (pathwise_survival hsmall)
    simp only [survival,he,probReal_univ]
    nlinarith [sq_nonneg (L : ℝ), Nat.cast_nonneg k (α := ℝ)]
  have hk : L ≤ k := by dsimp [L,halfSide]; omega
  let t := SchedulingFailure.time k
  have he := clock_extinction_bound L (by omega) ⟨t,(SchedulingFailure.time_positive k).le⟩
  have hc := SynchronousQuadraticTail.clockProbability_eq_one_sub_extinction
    (ClippedSquareCoordinates.parameter L) t
  have hcmp := (SquareGridLaw.two_way_clock_tail (ClippedSquareCoordinates.parameter L) false k).1
  have hs := inner_tail_le_outer (N := N) (by omega) k
  have herr := scheduling_error_small hL hk
  have hnum := clock_bound_numeric (k := k) hL
  change (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)).real
    {z | ClockExecutionLaw.endpoint _ t (SquarePWMeasure.topConfig _) z = fun _ => false} ≤
      ((6*(L : ℝ)+6)*t+((L : ℝ)+2)*(4*L+2))/((L : ℝ)^3/12500) at he
  change InfiniteGridRandomDynamics.measure.real {η | (k : ℕ∞) < InfiniteGridRecoveryTime.synchronous
    (SquareGridEmbedding.extend (ClippedSquareCoordinates.parameter L) (SquarePWMeasure.topConfig _)) η} ≤ _ at hs
  dsimp only [t] at hc he
  have b : 47/50 - survival N k ≤ 420000*((k : ℝ)+1)/(L : ℝ)^2 := by linarith
  have hl : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  exact (le_div_iff₀ (sq_pos_of_pos hl)).mp b

private theorem sum_succ (K : ℕ) :
    (∑ k ∈ Finset.range K, ((k : ℝ)+1)) = (K : ℝ)*((K : ℝ)+1)/2 := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ,ih]; push_cast; ring

theorem square_expected_large {N : ℕ} (hN : 2000000 ≤ N) :
    ENNReal.ofReal ((N : ℝ)^2/4000000) ≤ OriginalRecoveryProfile.expectedRecovery (squareConfig N) := by
  let L := halfSide N
  let K := L^2/450000
  have hL : 999999 ≤ L := by dsimp [L,halfSide]; omega
  have hl : (999999 : ℝ) ≤ L := by exact_mod_cast hL
  have hK : K*450000 ≤ L^2 := Nat.div_mul_le_self _ _
  have hK' : L^2 < (K+1)*450000 := by
    dsimp [K]; have := Nat.mod_add_div (L^2) 450000; have := Nat.mod_lt (L^2) (by decide : 0 < 450000); omega
  have hsq := Nat.mul_le_mul hL hL
  have hpos : 0 < K := by nlinarith only [hK',hsq]
  have hKr : (K : ℝ)*450000 ≤ (L : ℝ)^2 := by exact_mod_cast hK
  have hKr' : (L : ℝ)^2 < ((K : ℝ)+1)*450000 := by exact_mod_cast hK'
  have hn : N ≤ 2*L+2 := by dsimp [L,halfSide]; omega
  have hnr : (N : ℝ) ≤ 2*(L : ℝ)+2 := by exact_mod_cast hn
  have hN2 := mul_self_le_mul_self (Nat.cast_nonneg N : (0 : ℝ) ≤ N) hnr
  have hl2 := mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  have hround : (N : ℝ)^2/4000000 ≤ (47/100)*((K : ℝ)-1) := by
    nlinarith only [hKr',hN2,hl2,hl]
  have hp (k : ℕ) : (47/50)*((K : ℝ)-((k : ℝ)+1)) ≤ (K : ℝ)*survival N k := by
    by_cases hb : 0 ≤ 47/50 - survival N k
    · have h := mul_le_mul_of_nonneg_right hKr hb
      have he := square_survival_envelope hN k
      change (47/50 - survival N k)*(L : ℝ)^2 ≤ _ at he
      nlinarith only [he,h,Nat.cast_nonneg k (α := ℝ)]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg K : (0 : ℝ) ≤ K) (le_of_not_ge hb),
        Nat.cast_nonneg k (α := ℝ)]
  have hsum := Finset.sum_le_sum (s := Finset.range K) (fun k _ => hp k)
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_succ] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hKrpos : (0 : ℝ) < K := by exact_mod_cast hpos
  have hsum' : (47/100)*((K : ℝ)-1) ≤ ∑ k ∈ Finset.range K, survival N k := by
    apply (le_of_mul_le_mul_left ?_ hKrpos : _)
    nlinarith only [hsum]
  exact (ENNReal.ofReal_le_ofReal (hround.trans hsum')).trans
    (finite_tail_sum_le InfiniteGridRandomDynamics.measure _ (HomogeneousRecoveryTime.synchronous_measurable _) K)

theorem square_expected_uniform_lower (N : ℕ) :
    ENNReal.ofReal ((N : ℝ)^2/4000000) ≤ OriginalRecoveryProfile.expectedRecovery (squareConfig N) := by
  by_cases h : 2000000 ≤ N
  · exact square_expected_large h
  · apply (ENNReal.ofReal_le_ofReal _).trans (square_expected_ge_half N)
    have hn : (N : ℝ) ≤ 2000000 := by exact_mod_cast (show N ≤ 2000000 by omega)
    nlinarith [mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

theorem tau_uniform_quadratic_lower (N : ℕ) :
    ENNReal.ofReal ((N : ℝ)^2/4000000) ≤ OriginalRecoveryProfile.tau N :=
  (square_expected_uniform_lower N).trans (OriginalRecoveryProfile.square_expectedRecovery_le_tau N)

end MathResearchLower
