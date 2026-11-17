module
public import MathResearchAnalysis.OriginalQuadraticUpper
public import Mathlib.Analysis.SpecificLimits.Normed
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchRevision.SharpRecoveryTail
open MeasureTheory Filter
open scoped ENNReal
open MathResearchAnalysis
open SyncUpperScale (layers block)

/-- The retained original-clock failure and both scheduling errors. -/
def failure (N : Nat) : Real :=
  32/(8*(N : Real)+1) + (12/5 : Real)*(N : Real)^2*((2 : Real)⁻¹)^(layers N+1)

theorem failure_nonneg (N : Nat) : 0 ≤ failure N := by
  unfold failure
  positivity

theorem block_eq (N : Nat) : block N = 331776*N^2+257 := by
  unfold block SchedulingFailure.rankThreshold layers
  ring

theorem clock_survival_le (N : Nat) (hN : 2≤N) :
    ClockRecoveryComparison.clockProbability (N-2) (MixedHeatDecay.mixingTime (4*N)) ≤
      16/(8*(N : Real)+1) := by
  have hNs : N-2+2=N := by omega
  have hinc : N-2≤ClippedSquareCoordinates.parameter (4*N) := by
    unfold ClippedSquareCoordinates.parameter
    omega
  have hs := MixedClearingProbability.auxiliary_side N (by omega)
  have hsr : (ClippedSquareCoordinates.parameter (4*N)+2 : Real)=8*(N : Real)+1 := by
    exact_mod_cast hs
  have hp := CrossSquareClockBound.original_nonzero_probability_le_local_failure hinc
    (MixedHeatDecay.mixingTime (4*N)) (SquarePWMeasure.topConfig (N-2))
  rw [hNs] at hp
  have haux := MixedClearingProbability.failure_probability_le (4*N) (fun _ => true)
    (show Monotone (fun _ : DropletClockLaw.Vertex (4*N) => true) from fun _ _ _ => le_rfl) N
    (by rw [hsr]; linarith)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hp.trans haux)
  rw [ENNReal.toReal_ofReal (by positivity), hsr] at hreal
  exact hreal

theorem clock_at_scheduling_le (N : Nat) (hN : 2≤N) :
    ClockRecoveryComparison.clockProbability (N-2) (SchedulingFailure.time (layers N)) ≤
      16/(8*(N : Real)+1) :=
  (ClockEndpointSurvival.clockProbability_antitone (N-2)
    (SyncUpperScale.mixingTime_le_scheduling_time N (by omega))).trans
      (clock_survival_le N hN)

theorem synchronous_block_tail_le (N : Nat) (hN : 2≤N) :
    (SquareRandomDynamics.measure (N-2)).real
      {η | (block N : ℕ∞)<SquareRecoveryTime.synchronous (N-2)
        (SquarePWMeasure.topConfig (N-2)) η} ≤ failure N := by
  have h := (SquareRecoveryTime.two_way_clock_tail (N-2) false (layers N)).2
  have hc := clock_at_scheduling_le N hN
  have hNs : N-2+2=N := by omega
  have hsr : ((N-2 : Nat) : Real)+2=(N : Real) := by exact_mod_cast hNs
  change (SquareRandomDynamics.measure (N-2)).real
      {η | (block N : ℕ∞)<SquareRecoveryTime.synchronous (N-2)
        (SquarePWMeasure.topConfig (N-2)) η} ≤ _ at h
  rw [hsr] at h
  calc
    _ ≤ 2*(16/(8*(N : Real)+1)) +
      2*((6/5 : Real)*(N : Real)^2*((2 : Real)⁻¹)^(layers N+1)) := by linarith
    _ = failure N := by unfold failure; ring

theorem failure_le_half (N : Nat) (hN : 16≤N) : failure N ≤ 1/2 := by
  have he := SyncUpperScale.scheduling_error_le_eighth N hN
  have hNs : N-2+2=N := by omega
  rw [hNs] at he
  have hNr : (16 : Real)≤N := by exact_mod_cast hN
  have hc : 32/(8*(N : Real)+1)≤1/4 := by
    apply (div_le_iff₀ (by positivity : (0 : Real)<8*(N : Real)+1)).mpr
    linarith
  unfold failure
  linarith

theorem failure_lt_one (N : Nat) (hN : 16≤N) : failure N < 1 :=
  (failure_le_half N hN).trans_lt (by norm_num)

theorem recovery_block_tail (N : Nat) (hN : 2≤N)
    (g : SquareSpin.Config (N-2)) (j : Nat) :
    SquareRandomDynamics.measure (N-2)
      {η | ((j*block N : Nat) : ℕ∞)<SquareRecoveryTime.synchronous (N-2) g η} ≤
        (ENNReal.ofReal (failure N))^j := by
  have hp := SquareRandomRestart.recovery_block_le_pow (N-2) g (block N) j
  have hr := hp.trans (pow_le_pow_left₀ measureReal_nonneg (synchronous_block_tail_le N hN) j)
  have h := ENNReal.ofReal_le_ofReal hr
  rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
  simpa only [ENNReal.ofReal_pow (failure_nonneg N)] using h

theorem expectation_le_geometric {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℕ∞) (hT : Measurable T) (b : Nat) (hb : 1≤b)
    (q : ℝ≥0∞)
    (hTail : ∀ j : Nat, μ {ω | ((j*b : Nat) : ℕ∞)<T ω}≤q^j) :
    (∫⁻ ω, (T ω : ℝ≥0∞) ∂μ) ≤ (b : ℝ≥0∞)/(1-q) := by
  calc
    _ ≤ ∫⁻ ω, ∑' j : Nat, ExtendedBlockTail.blockWeight T b j ω ∂μ :=
      lintegral_mono (fun ω => by
        simpa only [ExtendedBlockTail.blockWeight_indicator, Set.indicator_apply, Set.mem_ofPred_eq]
          using ExtendedBlockTail.value_le_block_tsum (T ω) b hb)
    _ = ∑' j : Nat, ∫⁻ ω, ExtendedBlockTail.blockWeight T b j ω ∂μ :=
      lintegral_tsum (fun j => (ExtendedBlockTail.measurable_blockWeight T hT b j).aemeasurable)
    _ = ∑' j : Nat, (b : ℝ≥0∞)*μ {ω | ((j*b : Nat) : ℕ∞)<T ω} := by
      congr 1
      funext j
      exact ExtendedBlockTail.lintegral_blockWeight μ T hT b j
    _ ≤ ∑' j : Nat, (b : ℝ≥0∞)*q^j :=
      ENNReal.tsum_le_tsum (fun j => mul_le_mul_right (hTail j) (b : ℝ≥0∞))
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, div_eq_mul_inv]

theorem finiteExpected_le (N : Nat) (hN : 16≤N) (g : SquareSpin.Config (N-2)) :
    OriginalRecoveryProfile.finiteExpected (N-2) g ≤
      ENNReal.ofReal ((block N : Real)/(1-failure N)) := by
  have h := expectation_le_geometric (SquareRandomDynamics.measure (N-2))
    (SquareRecoveryTime.synchronous (N-2) g) (SquareRecoveryTime.synchronous_measurable _ _)
    (block N) (by have h := SyncUpperScale.block_positive N; omega)
    (ENNReal.ofReal (failure N)) (recovery_block_tail N (by omega) g)
  have hden : 0<1-failure N := sub_pos.mpr (failure_lt_one N hN)
  have hsub : 1-ENNReal.ofReal (failure N)=ENNReal.ofReal (1-failure N) := by
    simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_sub 1 (failure_nonneg N)).symm
  rw [hsub] at h
  simpa only [OriginalRecoveryProfile.finiteExpected, ExtendedRecoveryExpectation.expectation,
    ENNReal.ofReal_div_of_pos hden, ENNReal.ofReal_natCast] using h

theorem tau_le (N : Nat) (hN : 16≤N) :
    OriginalRecoveryProfile.tau N≤ENNReal.ofReal ((block N : Real)/(1-failure N)) := by
  rw [OriginalRecoveryProfile.tau_eq_normalizedTau N (by omega)]
  apply iSup_le
  intro g
  apply iSup_le
  intro _
  exact finiteExpected_le N hN g

theorem scheduling_majorant (N : Nat) :
    (12/5 : Real)*(N : Real)^2*((2 : Real)⁻¹)^(layers N+1) ≤
      (12/5 : Real)*((N : Real)^2*((2 : Real)⁻¹)^N) := by
  have hpow : ((2 : Real)⁻¹)^(layers N+1)≤((2 : Real)⁻¹)^N :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (SyncUpperScale.layers_succ_ge_side N)
  nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : (0 : Real)≤(12/5 : Real)*(N : Real)^2)]

theorem failure_tendsto_zero : Tendsto failure atTop (nhds 0) := by
  have hpoly : Tendsto (fun N : Nat => (N : Real)^2*((2 : Real)⁻¹)^N) atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one 2 (by norm_num) (by norm_num)
  have hsched : Tendsto (fun N : Nat => (12/5 : Real)*(N : Real)^2*
      ((2 : Real)⁻¹)^(layers N+1)) atTop (nhds 0) := by
    apply squeeze_zero (fun _ => by positivity) scheduling_majorant
    simpa only [mul_zero] using hpoly.const_mul (12/5 : Real)
  have hden : Tendsto (fun N : Nat => 8*(N : Real)+1) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : Real)<8))
  have hfrac : Tendsto (fun N : Nat => 32/(8*(N : Real)+1)) atTop (nhds 0) :=
    hden.const_div_atTop 32
  change Tendsto (fun N : Nat => 32/(8*(N : Real)+1) +
    (12/5 : Real)*(N : Real)^2*((2 : Real)⁻¹)^(layers N+1)) atTop (nhds 0)
  simpa only [zero_add] using hfrac.add hsched

end MathResearchRevision.SharpRecoveryTail

#print axioms MathResearchRevision.SharpRecoveryTail.failure
#print axioms MathResearchRevision.SharpRecoveryTail.failure_nonneg
#print axioms MathResearchRevision.SharpRecoveryTail.block_eq
#print axioms MathResearchRevision.SharpRecoveryTail.clock_survival_le
#print axioms MathResearchRevision.SharpRecoveryTail.clock_at_scheduling_le
#print axioms MathResearchRevision.SharpRecoveryTail.synchronous_block_tail_le
#print axioms MathResearchRevision.SharpRecoveryTail.failure_le_half
#print axioms MathResearchRevision.SharpRecoveryTail.failure_lt_one
#print axioms MathResearchRevision.SharpRecoveryTail.recovery_block_tail
#print axioms MathResearchRevision.SharpRecoveryTail.expectation_le_geometric
#print axioms MathResearchRevision.SharpRecoveryTail.finiteExpected_le
#print axioms MathResearchRevision.SharpRecoveryTail.tau_le
#print axioms MathResearchRevision.SharpRecoveryTail.scheduling_majorant
#print axioms MathResearchRevision.SharpRecoveryTail.failure_tendsto_zero
