module
public import TriangleLoss
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchLower.Triangle
open MathResearchAnalysis MeasureTheory
open ClippedDiamondGeometry (clippedDomain)
open ClippedProtectedGeometry (protectedSites)
open WeightedExitArea (missingWeight)
open PerturbationSymmetry (squareConfig)
open OriginalQuadraticLower (halfSide)
open scoped ENNReal

def cost (L : ℕ) : ℝ := (radius L : ℝ)*(radius L+1)*(radius L+2)/6

theorem physical_loss (L : ℕ) (hL : 10 ≤ L) (t : NNReal) :
    ∀ᵐ z ∂PhysicalAreaTail.law L, z ∈ PhysicalAreaTail.exitEvent L t →
      cost L ≤ WeightedAreaTail.missingArea L t z := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L] with z hz hexit
  have hm := (FrozenPhysicalExit.physicalExit_le_iff L _ _ _ z hz t.coe_nonneg).mp hexit
  let fallback : DropletModifiedWord.Event := ((0,0),false)
  change cost L ≤ missingWeight L (DropletStoppedClockLaw.stateAt L _ _ _ t z)
  rw [DropletStoppedClockLaw.stateAt_eq_stoppedTrajectory L _ _ _ t z fallback] at hm ⊢
  let events := DropletClockLaw.markedEvents L (ClockEventWord.word z.1 t) z.2
  have hs := (ProtectedEvolution.initial_stoppedTrajectory_shape (by omega : 2 ≤ L)
    (fun i => events.getD i fallback) events.length).1
  exact shape_loss hL hs.1 hs.2.1 hs.2.2.1 hm

theorem clock_cost_bound (L : ℕ) (hL : 40 ≤ L) (T : NNReal) :
    cost L * (PhysicalAreaTail.law L).real
      {z | ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L) (T : ℝ) (fun _ => true) z = fun _ => false} ≤
      (6*(L : ℝ)+6)*(T : ℝ)+((L : ℝ)+2)*(4*L+2) := by
  have h0 : 0 ≤ cost L := by unfold cost; positivity
  have hprob := (ENNReal.toReal_mono (measure_ne_top _ _)
    (FrozenPhysicalExit.original_extinction_measure_le_physical_exit L hL T T.coe_nonneg))
  have hexit : (PhysicalAreaTail.law L).real (PhysicalAreaTail.exitEvent L T) ≤
      (PhysicalAreaTail.law L).real {z | cost L ≤ WeightedAreaTail.missingArea L T z} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae (physical_loss L (by omega) T))
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (WeightedAreaTail.missingArea_nonnegative L T))
    (WeightedAreaTail.missingArea_integrable L T) (cost L)
  have hp (t : NNReal) : (∫ z, WeightedAreaTail.rawContribution L (t,z) ∂PhysicalAreaTail.law L) ≤ 6*(L : ℝ)+6 := by
    have hpoint : ∀ᵐ z ∂PhysicalAreaTail.law L, WeightedAreaTail.rawContribution L (t,z) ≤ 6*(L : ℝ)+6 := by
      filter_upwards [PhysicalWeightedDrift.beforeState_shape_all_times_ae L (by omega)] with z hz
      unfold WeightedAreaTail.rawContribution
      split
      · rename_i h
        exact raw_drift_le_six (by omega) (hz t)
          ((ClippedProtectedGeometry.innerDiamond_subset_protectedSites L).trans h)
          (ObservedPreState.state_supported L _ _ (Finset.Subset.refl _) t z)
      · positivity
    simpa using integral_mono_ae (WeightedAreaTail.rawContribution_sample_integrable L (by omega) t)
      (integrable_const (6*(L : ℝ)+6)) hpoint
  have hc : Integrable (fun _ : ℝ => 6*(L : ℝ)+6) ((volume : Measure ℝ).restrict (Set.Ioc 0 (T : ℝ))) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have ht := integral_mono_ae (WeightedAreaTail.rawContribution_time_mean_integrable L (by omega) T)
    hc (Filter.Eventually.of_forall (fun t : ℝ => hp t.toNNReal))
  rw [PhysicalWeightedDrift.integral_time_const] at ht
  have hmean := WeightedAreaTail.meanArea_le_raw_integral_add_budget L (by omega) T
  change (PhysicalAreaTail.law L).real _ ≤ (PhysicalAreaTail.law L).real (PhysicalAreaTail.exitEvent L T) at hprob
  exact (mul_le_mul_of_nonneg_left (hprob.trans hexit) h0).trans
    (hmark.trans (hmean.trans (by simpa only [mul_comm (6*(L : ℝ)+6)] using add_le_add ht (le_refl (((L : ℝ)+2)*(4*L+2))))))

theorem numerical_cost {L : ℕ} (hL : 10000 ≤ L) : (L : ℝ)^3/6100 ≤ cost L := by
  have hf : (998 : ℝ)*L ≤ 10000*(radius L : ℝ) := by
    exact_mod_cast (show 998*L ≤ 10000*radius L by unfold radius; omega)
  have hp := pow_le_pow_left₀ (by positivity) hf 3
  unfold cost
  nlinarith [sq_nonneg (radius L : ℝ), show 0 ≤ (radius L : ℝ)^3 by positivity,Nat.cast_nonneg (radius L) (α := ℝ)]

theorem extinction_budget {N k : ℕ} (hN : 100 ≤ N) :
    cost (halfSide N) * (1-survival N k -
      (6/5 : ℝ)*(ClippedSquareCoordinates.parameter (halfSide N)+2 : ℝ)^2*((2 : ℝ)⁻¹)^(k+1)) ≤
        (6*(halfSide N : ℝ)+6)*SchedulingFailure.time k+((halfSide N : ℝ)+2)*(4*halfSide N+2) := by
  let L := halfSide N
  have hL : 40 ≤ L := by dsimp [L,halfSide]; omega
  let t := SchedulingFailure.time k
  have hp := clock_cost_bound L hL ⟨t,(SchedulingFailure.time_positive k).le⟩
  have hc := SynchronousQuadraticTail.clockProbability_eq_one_sub_extinction (ClippedSquareCoordinates.parameter L) t
  have hm := (SquareGridLaw.two_way_clock_tail (ClippedSquareCoordinates.parameter L) false k).1
  have hs := inner_tail_le_outer (N := N) (by omega) k
  change InfiniteGridRandomDynamics.measure.real {η | (k : ℕ∞) < InfiniteGridRecoveryTime.synchronous
    (SquareGridEmbedding.extend (ClippedSquareCoordinates.parameter L) (SquarePWMeasure.topConfig _)) η} ≤ _ at hs
  change cost L * (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)).real
    {z | ClockExecutionLaw.endpoint _ t (SquarePWMeasure.topConfig _) z = fun _ => false} ≤ _ at hp
  apply le_trans _ hp
  apply mul_le_mul_of_nonneg_left _ (by unfold cost; positivity)
  dsimp only [t] at hc ⊢
  linarith

private theorem scheduling {L k : ℕ} (hL : 40 ≤ L) (hk : L ≤ k) :
    (6/5 : ℝ)*(ClippedSquareCoordinates.parameter L+2 : ℝ)^2*((2 : ℝ)⁻¹)^(k+1) ≤ 1/1000 := by
  let r := k+1-12
  have hr : 16 ≤ r := by dsimp [r]; omega
  have he : r+12=k+1 := by dsimp [r]; omega
  have hside : (ClippedSquareCoordinates.parameter L+2 : ℝ) ≤ 3*(r : ℝ) := by
    exact_mod_cast (ClippedSquareCoordinates.parameter_side L (by omega)).le.trans
      (show 2*L+1 ≤ 3*r by dsimp [r]; omega)
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ (ClippedSquareCoordinates.parameter L+2 : ℝ)) hside
  have hpow := SyncLowerScale.square_exponential_bound r hr
  rw [inv_pow,← div_eq_mul_inv,← he,pow_add]
  apply (div_le_iff₀ (by positivity)).mpr
  norm_num
  nlinarith only [hsq,hpow,sq_nonneg (r : ℝ)]

theorem affine_tail {N : ℕ} (hN : 950000 ≤ N) (k : ℕ) :
    (47/50-survival N k)*(halfSide N : ℝ)^2 ≤ 205000*((k : ℝ)+1) := by
  let L := halfSide N
  have hL : 474999 ≤ L := by dsimp [L,halfSide]; omega
  have hl : (474999 : ℝ) ≤ L := by exact_mod_cast hL
  change (47/50-survival N k)*(L : ℝ)^2 ≤ _
  by_cases h : 2*k < N
  · have he : {η | (k : ℕ∞) < HomogeneousRecoveryTime.synchronous (squareConfig N) η} = Set.univ :=
      Set.eq_univ_of_forall (pathwise_survival h)
    simp only [survival,he,probReal_univ]
    nlinarith [sq_nonneg (L : ℝ), Nat.cast_nonneg k (α := ℝ)]
  by_cases hb : 47/50 ≤ survival N k
  · nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hb) (sq_nonneg (L : ℝ)),Nat.cast_nonneg k (α := ℝ)]
  have hnon : 0 ≤ 999/1000-survival N k := by linarith
  have hp := extinction_budget (k := k) (by omega : 100 ≤ N)
  have hs := scheduling (by omega : 40 ≤ L) (show L ≤ k by dsimp [L,halfSide]; omega)
  have hrate := numerical_cost (by omega : 10000 ≤ L)
  have hcpos : 0 ≤ cost L := by unfold cost; positivity
  have h := mul_le_mul_of_nonneg_left (show 999/1000-survival N k ≤ 1-survival N k -
      (6/5 : ℝ)*(ClippedSquareCoordinates.parameter L+2 : ℝ)^2*((2 : ℝ)⁻¹)^(k+1) by linarith) hcpos
  have htotal := (mul_le_mul_of_nonneg_right hrate hnon).trans (h.trans hp)
  have hlog : 8*Real.log 2 ≤ 139/25 := by linarith [Real.log_two_lt_d9]
  have ht : SchedulingFailure.time k ≤ (139/25)*((k : ℝ)+1) := by
    unfold SchedulingFailure.time; push_cast
    exact mul_le_mul_of_nonneg_right hlog (by positivity)
  have hraw := mul_le_mul (show 6*(L : ℝ)+6 ≤ 601/100*L by linarith) ht
    (SchedulingFailure.time_positive k).le (by positivity)
  have hquad := mul_le_mul_of_nonneg_right hl (sq_nonneg (L : ℝ))
  have hlin := mul_le_mul_of_nonneg_right hl (by positivity : 0 ≤ (L : ℝ))
  have hkpos : 0 ≤ (L : ℝ)*((k : ℝ)+1) := by positivity
  apply le_of_mul_le_mul_right (a := (L : ℝ)) _ (by linarith)
  nlinarith only [htotal,hraw,hquad,hlin,hl,hkpos]

private theorem round_sum (K : ℕ) :
    (∑ k ∈ Finset.range K, ((k : ℝ)+1)) = (K : ℝ)*((K : ℝ)+1)/2 := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ,ih]; push_cast; ring

/-- Finite triangular summation, valid without an integrability assumption. -/
theorem integrate_envelope (N K : ℕ) {a b : ℝ} (h : ∀ k : ℕ, a-b*((k : ℝ)+1) ≤ survival N k) :
    ENNReal.ofReal ((K : ℝ)*(a-b*((K : ℝ)+1)/2)) ≤ OriginalRecoveryProfile.expectedRecovery (squareConfig N) := by
  have hs := Finset.sum_le_sum (s := Finset.range K) (fun k _ => h k)
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,round_sum] at hs
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
  apply le_trans _ (finite_tail_sum_le InfiniteGridRandomDynamics.measure _
    (HomogeneousRecoveryTime.synchronous_measurable (squareConfig N)) K)
  apply ENNReal.ofReal_le_ofReal
  linarith

theorem square_improved (N : ℕ) :
    ENNReal.ofReal ((N : ℝ)^2/1900000) ≤ OriginalRecoveryProfile.expectedRecovery (squareConfig N) := by
  by_cases hn : 950000 ≤ N
  · let L := halfSide N
    let K := L^2/219000
    have hL : 474999 ≤ L := by dsimp [L,halfSide]; omega
    have hl : (474999 : ℝ) ≤ L := by exact_mod_cast hL
    have hkr : (K : ℝ)*219000 ≤ (L : ℝ)^2 := by exact_mod_cast (Nat.div_mul_le_self (L^2) 219000)
    have hk' : L^2 < (K+1)*219000 := by
      dsimp [K]; have := Nat.mod_add_div (L^2) 219000; have := Nat.mod_lt (L^2) (by decide : 0 < 219000); omega
    have hk : (L : ℝ)^2 < ((K : ℝ)+1)*219000 := by exact_mod_cast hk'
    have hN : N ≤ 2*L+2 := by dsimp [L,halfSide]; omega
    have hN' : (N : ℝ) ≤ 2*(L : ℝ)+2 := by exact_mod_cast hN
    have hN2 := mul_self_le_mul_self (Nat.cast_nonneg N : (0 : ℝ) ≤ N) hN'
    have hround : (N : ℝ)^2/1900000 ≤ 47/100*((K : ℝ)-1) := by
      nlinarith only [hk,hN2,mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg L (α := ℝ)),hl]
    have hkp : 0 < K := by by_contra! hh; have := Nat.eq_zero_of_le_zero hh; rw [this] at hk'; nlinarith only [hk',Nat.mul_self_le_mul_self hL]
    have hkp' : (0 : ℝ) < K := by exact_mod_cast hkp
    have hen (k : ℕ) : 47/50-(47/50/(K : ℝ))*((k : ℝ)+1) ≤ survival N k := by
      have he := affine_tail hn k
      by_cases h : 0 ≤ 47/50-survival N k
      · have hm := mul_le_mul_of_nonneg_right hkr h
        change (47/50-survival N k)*(L : ℝ)^2 ≤ _ at he
        have hh : (47/50-survival N k)*(K : ℝ) ≤ (47/50)*((k : ℝ)+1) := by
          nlinarith only [he,hm,Nat.cast_nonneg k (α := ℝ)]
        have hf := (le_div_iff₀ hkp').mpr hh
        rw [div_mul_eq_mul_div]
        linarith
      · have hnn : 0 ≤ (47/50/(K : ℝ))*((k : ℝ)+1) := by positivity
        linarith
    apply le_trans _ (integrate_envelope N K hen)
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ _ := hround
      _ = _ := by field_simp [ne_of_gt hkp']; ring
  · apply le_trans _ (square_expected_ge_half N)
    apply ENNReal.ofReal_le_ofReal
    have hh : (N : ℝ) ≤ 950000 := by exact_mod_cast (show N ≤ 950000 by omega)
    nlinarith only [mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg N (α := ℝ))]

theorem tau_improved (N : ℕ) : ENNReal.ofReal ((N : ℝ)^2/1900000) ≤ OriginalRecoveryProfile.tau N :=
  (square_improved N).trans (OriginalRecoveryProfile.square_expectedRecovery_le_tau N)

end MathResearchLower.Triangle
