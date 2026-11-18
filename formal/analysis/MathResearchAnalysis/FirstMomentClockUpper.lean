module
public import MathResearchAnalysis.OriginalQuadraticUpper
public import MathResearchAnalysis.DeterministicClockRestart
public import Mathlib.Tactic

set_option autoImplicit false

/-! The C2 first-moment route. The one-interval bound uses the original clock
law. The deterministic-time transition theorem supplies the restart used to
amplify this estimate before transferring it to synchronous rounds. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.FirstMomentClockUpper
open MeasureTheory Set

/-- A bounded count with mean at least M/4 is below M/8 with probability at most 6/7. -/
theorem count_failure_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X) (hi : Integrable X μ)
    (M : ℝ) (hM : 0 < M) (hcap : ∀ z, X z ≤ M)
    (hmean : M / 4 ≤ ∫ z, X z ∂μ) :
    μ.real {z | X z < M / 8} ≤ 6 / 7 := by
  let F : Set Ω := {z | X z < M / 8}
  have hF : MeasurableSet F := measurableSet_lt hX measurable_const
  let I : Ω → ℝ := F.indicator (1 : Ω → ℝ)
  have hI : Integrable I μ := (integrable_const 1).indicator hF
  have hpoint (z : Ω) : X z ≤ M - (7 * M / 8) * I z := by
    by_cases hz : z ∈ F
    · have hlt : X z < M / 8 := hz
      simp only [I, Set.indicator_of_mem hz, Pi.one_apply, mul_one]
      linarith
    · simpa only [I, Set.indicator_of_notMem hz, mul_zero, sub_zero] using hcap z
  have hb := integral_mono hi ((integrable_const M).sub (hI.const_mul _)) hpoint
  change (∫ z, X z ∂μ) ≤ ∫ z, M - (7 * M / 8) * I z ∂μ at hb
  have hIntegral : (∫ z, I z ∂μ) = μ.real F := by
    simpa only [I] using (integral_indicator_one (μ := μ) hF)
  rw [integral_sub (integrable_const M) (hI.const_mul _), integral_const,
    probReal_univ, one_smul, integral_const_mul, hIntegral] at hb
  have hmul : (7 * M / 8) * μ.real F ≤ (7 * M / 8) * (6 / 7) := by linarith
  exact le_of_mul_le_mul_left hmul (by positivity)

def interval (N : Nat) : ℝ := MixedHeatDecay.mixingTime (4 * N)

def survival (n : Nat) (g : SquareSpin.Config n) (t : ℝ) : ℝ :=
  (ClockWordMarks.measure n).real {z | ClockExecutionLaw.endpoint n t g z ≠ fun _ => false}

/-- One interval, uniformly over every deterministic zero-boundary initial pattern. -/
theorem one_interval (N : Nat) (hN : 2 ≤ N) (g : SquareSpin.Config (N - 2)) :
    survival (N - 2) g (interval N) ≤ 6 / 7 := by
  let L := 4 * N
  let m := ClippedSquareCoordinates.parameter L
  let initial : DropletClockLaw.Config L := fun _ => true
  have hmono : Monotone initial := fun _ _ _ => le_rfl
  have hside : m + 2 = 8 * N + 1 := SyncUpperScale.auxiliary_side N (by omega)
  have hinc : N - 2 ≤ m := by omega
  have hsmall : N - 2 + 2 = N := by omega
  have hsideReal : (m : ℝ) + 2 = 8 * (N : ℝ) + 1 := by exact_mod_cast hside
  have hNr : (N : ℝ) ≤ ((m : ℝ) + 2) / 8 := by linarith
  have hc := CrossSquareClockBound.original_nonzero_probability_le_local_failure
    hinc (interval N) g
  rw [hsmall] at hc
  have hX := count_failure_le (ClockWordMarks.measure m)
    (MixedRightCountMoments.count L initial (interval N))
    (MixedRightCountMoments.count_measurable L initial _)
    (MixedRightCountMoments.count_integrable L initial _)
    ((m : ℝ) + 2) (by positivity) (MixedRightCountMoments.count_le_side L initial _)
    (MixedRightCountHeat.mean_at_mixingTime L initial hmono)
  apply (ENNReal.toReal_mono (measure_ne_top _ _) hc).trans
  refine (measureReal_mono (MixedClearingProbability.failure_subset_count L initial hmono N
    (interval N))).trans ?_
  apply (measureReal_mono (μ := ClockWordMarks.measure m) ?_).trans hX
  intro z hz
  exact lt_of_lt_of_le hz hNr

/-- The deterministic-time transition identity on the original marked-clock
sample. This is the probabilistic input needed to concatenate intervals. -/
def RestartLaw (N : Nat) : Prop :=
  ∀ i : Nat,
    let n := N - 2
    let g := SquarePWMeasure.topConfig n
    survival n g ((i + 1 : Nat) * interval N) =
      ∑ f : SquareSpin.Config n,
        (ClockWordMarks.measure n).real {z | ClockExecutionLaw.endpoint n (i * interval N) g z = f} *
          survival n f (interval N)

theorem restartLaw (N : Nat) : RestartLaw N := by
  intro i
  let n := N - 2
  let g := SquarePWMeasure.topConfig n
  have hh : 0 ≤ interval N := MixedHeatDecay.mixingTime_nonneg (4 * N)
  let B : Set (SquareSpin.Config n) := {f | f ≠ fun _ => false}
  have hB : MeasurableSet B := (measurableSet_singleton (fun _ => false)).compl
  have h := DeterministicClockRestart.endpoint_probability (n := n)
    ((i : ℝ) * interval N) (interval N) (mul_nonneg (Nat.cast_nonneg _) hh) hh g B hB
  have htime : ((i : ℝ) + 1) * interval N = i * interval N + interval N := by ring
  simpa only [survival, n, g, B, Set.mem_ofPred_eq, Nat.cast_add, Nat.cast_one, htime] using h

private theorem survival_zero (n : Nat) (t : ℝ) :
    survival n (fun _ => false) t = 0 := by
  simp [survival, ClockExecutionLaw.endpoint, MarkedEventTrace.executeClockWord,
    ClockEndpointSurvival.execute_zero]

theorem survival_step_le (N : Nat) (hN : 2 ≤ N) (i : Nat) :
    survival (N - 2) (SquarePWMeasure.topConfig (N - 2)) ((i + 1 : Nat) * interval N) ≤
      (6 / 7) * survival (N - 2) (SquarePWMeasure.topConfig (N - 2)) (i * interval N) := by
  let n := N - 2
  let g := SquarePWMeasure.topConfig n
  let μ := ClockWordMarks.measure n
  let X := ClockExecutionLaw.endpoint n (i * interval N) g
  let F (f : SquareSpin.Config n) : Set (ClockWordMarks.Sample n) :=
    {z | X z = f ∧ f ≠ fun _ => false}
  have hX : Measurable X := ClockExecutionLaw.endpoint_measurable _ _ _
  have hF (f : SquareSpin.Config n) : MeasurableSet (F f) :=
    (hX (measurableSet_singleton f)).inter (MeasurableSet.const _)
  have hd : Pairwise (fun f g => Disjoint (F f) (F g)) := by
    intro f g hfg
    exact Set.disjoint_left.2 (fun _ hf hg => hfg (hf.1.symm.trans hg.1))
  have hs : {z | X z ≠ fun _ => false} = ⋃ f, F f := by
    ext z
    rw [mem_iUnion]
    constructor
    · intro hz
      exact ⟨X z, rfl, hz⟩
    · rintro ⟨f, hf, hne⟩
      exact fun hz => hne (hf.symm.trans hz)
  have hsum : survival n g (i * interval N) = ∑ f, μ.real (F f) := by
    change μ.real {z | X z ≠ fun _ => false} = _
    rw [hs]
    exact measureReal_iUnion_fintype hd hF
  change survival n g ((i + 1 : Nat) * interval N) ≤ (6 / 7) * survival n g (i * interval N)
  rw [restartLaw N i, hsum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro f _
  by_cases hf : f = (fun _ => false)
  · subst f
    simp [F, survival_zero]
  · have hFf : F f = {z | X z = f} := by
      ext z
      change (X z = f ∧ f ≠ fun _ => false) ↔ X z = f
      exact and_iff_left hf
    rw [hFf, mul_comm (6 / 7 : ℝ)]
    change μ.real {z | X z = f} * survival n f (interval N) ≤
      μ.real {z | X z = f} * (6 / 7)
    exact mul_le_mul_of_nonneg_left (one_interval N hN f) measureReal_nonneg

theorem survival_le_pow (N : Nat) (hN : 2 ≤ N) (i : Nat) :
    survival (N - 2) (SquarePWMeasure.topConfig (N - 2)) (i * interval N) ≤
      (6 / 7 : ℝ) ^ i := by
  induction i with
  | zero => simpa only [Nat.cast_zero, zero_mul, pow_zero] using
      (show survival (N - 2) (SquarePWMeasure.topConfig (N - 2)) 0 ≤ 1 from
        (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ)
  | succ i hi =>
    rw [pow_succ']
    exact (survival_step_le N hN i).trans (mul_le_mul_of_nonneg_left hi (by norm_num))

def layers (N : Nat) : Nat := 4536 * N^2

def block (N : Nat) : Nat := 2 * SchedulingFailure.rankThreshold (layers N) + 1

theorem block_eq (N : Nat) : block N = 1161216 * N^2 + 257 := by
  unfold block layers SchedulingFailure.rankThreshold
  ring

theorem fourteen_intervals_le_schedule (N : Nat) (hN : 1 ≤ N) :
    14 * interval N ≤ SchedulingFailure.time (layers N) := by
  have hmix := SyncUpperScale.mixingTime_le_layers N hN
  have hlog := SyncUpperScale.log_two_ge_half
  have hm := mul_le_mul_of_nonneg_right hlog
    (show (0 : ℝ) ≤ ((layers N + 1 : Nat) : ℝ) from Nat.cast_nonneg _)
  unfold SchedulingFailure.time
  simp only [interval, SyncUpperScale.layers, layers] at hmix hm ⊢
  push_cast at hmix hm ⊢
  nlinarith

theorem scheduling_error_le_eighth (N : Nat) (hN : 16 ≤ N) :
    ((6 : ℝ) / 5) * (N - 2 + 2 : Nat)^2 * ((2 : ℝ)⁻¹)^(layers N + 1) ≤ 1 / 8 := by
  have hindex : SyncUpperScale.layers N + 1 ≤ layers N + 1 := by
    unfold SyncUpperScale.layers layers
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by decide)) _
  have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ ≤ 1) hindex
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans
    (SyncUpperScale.scheduling_error_le_eighth N hN)

theorem synchronous_block_le_half (N : Nat) (hN : 16 ≤ N) :
    (SquareRandomDynamics.measure (N - 2)).real
      {η | (block N : ℕ∞) < SquareRecoveryTime.synchronous (N - 2)
        (SquarePWMeasure.topConfig (N - 2)) η} ≤ 1 / 2 := by
  have h14 := survival_le_pow N (by omega) 14
  norm_num only [Nat.cast_ofNat] at h14
  have hc : ClockRecoveryComparison.clockProbability (N - 2)
      (SchedulingFailure.time (layers N)) ≤ 1 / 8 :=
    (ClockEndpointSurvival.clockProbability_antitone (N - 2)
      (fourteen_intervals_le_schedule N (by omega))).trans
      (h14.trans (by norm_num))
  have he := scheduling_error_le_eighth N hN
  simp only [Nat.cast_add, Nat.cast_ofNat] at he
  have h := (SquareRecoveryTime.two_way_clock_tail (N - 2) false (layers N)).2
  change (SquareRandomDynamics.measure (N - 2)).real
    {η | (block N : ℕ∞) < SquareRecoveryTime.synchronous (N - 2)
      (SquarePWMeasure.topConfig (N - 2)) η} ≤ _ at h
  linarith

theorem recovery_block_tail (N : Nat) (hN : 16 ≤ N)
    (g : SquareSpin.Config (N - 2)) (j : Nat) :
    SquareRandomDynamics.measure (N - 2)
      {η | ((j * block N : Nat) : ℕ∞) < SquareRecoveryTime.synchronous (N - 2) g η} ≤
        (1 / 2 : ENNReal)^j := by
  have hp := SquareRandomRestart.recovery_block_le_pow (N - 2) g (block N) j
  have hr := hp.trans (pow_le_pow_left₀ measureReal_nonneg (synchronous_block_le_half N hN) j)
  have h := ENNReal.ofReal_le_ofReal hr
  rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
  simpa only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
    show ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num] using h

theorem tau_le_two_blocks (N : Nat) (hN : 16 ≤ N) :
    OriginalRecoveryProfile.tau N ≤ 2 * (block N : ENNReal) := by
  rw [OriginalRecoveryProfile.tau_eq_normalizedTau N (by omega)]
  apply iSup_le
  intro g
  apply iSup_le
  intro _
  exact ExtendedBlockTail.lintegral_le_two_blocks (SquareRandomDynamics.measure (N - 2))
    (SquareRecoveryTime.synchronous (N - 2) g) (SquareRecoveryTime.synchronous_measurable (N - 2) g)
    (block N) (by unfold block; omega) (recovery_block_tail N hN g)


/-- The explicit first-moment expectation bound for the original model. -/
theorem tau_explicit_upper (N : Nat) (hN : 16 ≤ N) :
    OriginalRecoveryProfile.tau N ≤ 2322432 * (N : ENNReal)^2 + 514 := by
  have h := tau_le_two_blocks N hN
  rw [block_eq] at h
  convert h using 1
  push_cast
  ring

end MathResearchAnalysis.FirstMomentClockUpper
