module

public import MathResearchAnalysis.ActualClockTail

set_option autoImplicit false

/-!
# Actual greedy clock chains and non-strict lower tails

A deterministic sequence of sites is embedded into the already constructed
task system using singleton predecessors. Its completion is the actual greedy
sequence of strict next rings. Closed fixed-path moments give its Laplace
transform and a non-strict lower-tail bound by integral Markov, without
factorial-moment or waiting-law assumptions.

A separate deterministic domination lemma compares with any given strictly
increasing arrival witness whose first event is strictly positive. It does not
construct a rank witness or prove its existence.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.GreedyClockChain

variable {V : Type*} [DecidableEq V]

def chainSystem (p : Nat → V) : TaskPaths.System V where
  predecessors k _ := {p (k - 1)}
  nonempty _k _ := Finset.singleton_nonempty _

def chainTime (p : Nat → V) (r : Nat) : ExponentialClocks.Sample V → WithTop ℝ :=
  ClockReadiness.completion (chainSystem p) r (p (r - 1))

def wait (p : Nat → V) (i : Nat) : ExponentialClocks.Sample V → ℝ :=
  TaskClockBridge.delay (chainSystem p) i (p i)

theorem ready_eq_chainTime (p : Nat → V) (i : Nat) (v : V)
    (ω : ExponentialClocks.Sample V) :
    ClockReadiness.ready (chainSystem p) i v ω = chainTime p i ω := by
  simp [ClockReadiness.ready, chainSystem, chainTime]

theorem chainTime_zero (p : Nat → V) (ω : ExponentialClocks.Sample V) :
    chainTime p 0 ω = 0 := rfl

theorem chainTime_succ (p : Nat → V) (i : Nat) (ω : ExponentialClocks.Sample V) :
    chainTime p (i + 1) ω = ExtendedNextRing.after
      (ArrivalFiltration.chronologicalArrival (p i)) (chainTime p i) ω := by
  change ClockReadiness.completion (chainSystem p) (i + 1) (p i) ω = _
  rw [ClockReadiness.completion_succ]
  have hready : ClockReadiness.ready (chainSystem p) i (p i) = chainTime p i := by
    funext η
    exact ready_eq_chainTime p i (p i) η
  rw [hready]

theorem chainTime_isStoppingTime (p : Nat → V) (r : Nat) :
    IsStoppingTime (ArrivalFiltration.clockHistory V) (chainTime p r) :=
  ClockReadiness.completion_isStoppingTime (chainSystem p) r (p (r - 1))

theorem chainTime_nonnegative (p : Nat → V) (r : Nat) (ω : ExponentialClocks.Sample V) :
    0 ≤ chainTime p r ω :=
  ClockReadiness.completion_nonnegative (chainSystem p) r (p (r - 1)) ω

theorem chainTime_monotone (p : Nat → V) (ω : ExponentialClocks.Sample V) :
    Monotone (fun r => chainTime p r ω) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [chainTime_succ]
  exact ExtendedNextRing.ready_le_after (ArrivalFiltration.chronologicalArrival (p i))
    (chainTime p i) ω

theorem fixed_edges (p : Nat → V) (r : Nat) : FixedClockPath.Edges (chainSystem p) p r := by
  intro i _
  simp [chainSystem]

theorem delay_add_previous (p : Nat → V) (i : Nat) (ω : ExponentialClocks.Sample V)
    (hfinite : ∀ r, chainTime p r ω ≠ ⊤) :
    wait p i ω + (chainTime p i ω).untopD 0 = (chainTime p (i + 1) ω).untopD 0 := by
  have hready : ClockReadiness.ready (chainSystem p) i (p i) ω ≠ ⊤ := by
    rw [ready_eq_chainTime]
    exact hfinite i
  have hcomplete : ClockReadiness.completion (chainSystem p) (i + 1) (p i) ω ≠ ⊤ :=
    hfinite (i + 1)
  simpa only [wait, TaskClockBridge.realReady, ready_eq_chainTime,
    TaskClockBridge.realCompletion, chainTime, Nat.add_sub_cancel] using
      TaskClockBridge.delay_add_realReady (chainSystem p) i (p i) ω hready hcomplete

theorem representative_eq_prefixSum (p : Nat → V) (ω : ExponentialClocks.Sample V)
    (hfinite : ∀ r, chainTime p r ω ≠ ⊤) (r : Nat) :
    (chainTime p r ω).untopD 0 = ConditionalMoment.prefixSum (wait p) r ω := by
  induction r with
  | zero => simp [chainTime_zero, ConditionalMoment.prefixSum]
  | succ r ih =>
    calc
      _ = wait p r ω + (chainTime p r ω).untopD 0 := (delay_add_previous p r ω hfinite).symm
      _ = wait p r ω + ConditionalMoment.prefixSum (wait p) r ω := by rw [ih]
      _ = ConditionalMoment.prefixSum (wait p) (r + 1) ω := by
        rw [ConditionalMoment.prefixSum]
        exact add_comm _ _

section Probability

variable [Countable V]

theorem chainTime_finite_ae (p : Nat → V) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ r, chainTime p r ω ≠ ⊤ :=
  (ClockReadiness.completion_finite_ae (chainSystem p)).mono fun _ω hω r => hω r (p (r - 1))

theorem representative_eq_prefixSum_ae (p : Nat → V) (r : Nat) :
    (fun ω => (chainTime p r ω).untopD 0) =ᵐ[ExponentialClocks.clockMeasure V]
      ConditionalMoment.prefixSum (wait p) r := by
  filter_upwards [chainTime_finite_ae p] with ω hω
  exact representative_eq_prefixSum p ω hω r

/-- Exact exponential integrability of the actual greedy completion representative. -/
theorem exponential_integrable (p : Nat → V) (r : Nat) (θ : ℝ) (hθ : θ < 1) :
    Integrable (fun ω => Real.exp (θ * (chainTime p r ω).untopD 0))
      (ExponentialClocks.clockMeasure V) := by
  have h := ActualClockTail.fixed_path_exponential_integrable (chainSystem p) p r
    (fixed_edges p r) θ hθ
  apply h.congr
  filter_upwards [representative_eq_prefixSum_ae p r] with ω hω
  simp only [ConditionalMoment.pathExp, hω]
  rfl

/-- The greedy chain MGF comes from actual task waits, without probability-law premises. -/
theorem exponential_moment (p : Nat → V) (r : Nat) (θ : ℝ) (hθ : θ < 1) :
    (∫ ω, Real.exp (θ * (chainTime p r ω).untopD 0) ∂ExponentialClocks.clockMeasure V) =
      ((1 - θ)⁻¹) ^ r := by
  calc
    _ = ∫ ω, Real.exp (θ * ConditionalMoment.prefixSum (wait p) r ω)
        ∂ExponentialClocks.clockMeasure V := by
      apply integral_congr_ae
      filter_upwards [representative_eq_prefixSum_ae p r] with ω hω
      rw [hω]
    _ = _ := ActualClockTail.fixed_path_exponential_moment (chainSystem p) p r
      (fixed_edges p r) θ hθ

/-- Integral Markov gives the non-strict lower tail, including an atom at the threshold.
No event `{chainTime ≤ t}` is replaced by `{chainTime < t}`. -/
theorem lower_tail (p : Nat → V) (r : Nat) (t a : ℝ) (ha : 0 < a) :
    MeasurableSet {ω | chainTime p r ω ≤ (t : WithTop ℝ)} ∧
      (ExponentialClocks.clockMeasure V).real {ω | chainTime p r ω ≤ (t : WithTop ℝ)} ≤
        Real.exp (a * t) * ((1 + a)⁻¹) ^ r := by
  refine ⟨(ArrivalFiltration.clockHistory V).le t _
    ((chainTime_isStoppingTime p r).measurableSet_le t), ?_⟩
  have heq : {ω | chainTime p r ω ≤ (t : WithTop ℝ)} =ᵐ[ExponentialClocks.clockMeasure V]
      {ω | Real.exp (-a * t) ≤ Real.exp (-a * (chainTime p r ω).untopD 0)} := by
    filter_upwards [chainTime_finite_ae p] with ω hω
    apply propext
    lift chainTime p r ω to ℝ using hω r with s hs
    simp only [WithTop.coe_le_coe, WithTop.untopD_coe, Real.exp_le_exp]
    constructor <;> intro h <;> nlinarith
  rw [measureReal_congr heq]
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (ExponentialClocks.clockMeasure V)
      (fun ω => (Real.exp_pos (-a * (chainTime p r ω).untopD 0)).le))
    (exponential_integrable p r (-a) (by linarith)) (Real.exp (-a * t))
  rw [exponential_moment p r (-a) (by linarith), sub_neg_eq_add] at hmarkov
  have hbound : (ExponentialClocks.clockMeasure V).real
      {ω | Real.exp (-a * t) ≤ Real.exp (-a * (chainTime p r ω).untopD 0)} ≤
      ((1 + a)⁻¹) ^ r / Real.exp (-a * t) := by
    apply (le_div_iff₀ (Real.exp_pos (-a * t))).mpr
    simpa only [mul_comm] using hmarkov
  refine hbound.trans_eq ?_
  rw [div_eq_mul_inv, ← Real.exp_neg,
    show -(-a * t) = a * t by ring, mul_comm]

theorem lower_tail_nine (p : Nat → V) (r : Nat) (t : ℝ) :
    MeasurableSet {ω | chainTime p r ω ≤ (t : WithTop ℝ)} ∧
      (ExponentialClocks.clockMeasure V).real {ω | chainTime p r ω ≤ (t : WithTop ℝ)} ≤
        Real.exp (9 * t) * ((10 : ℝ)⁻¹) ^ r := by
  simpa only [show (1 + 9 : ℝ) = 10 by norm_num] using lower_tail p r t 9 (by norm_num)

end Probability

/-- A given future arrival dominates the actual greedy next ring. -/
theorem chainTime_succ_le_arrival (p : Nat → V) (i k : Nat)
    (ω : ExponentialClocks.Sample V)
    (hfuture : chainTime p i ω < (ArrivalFiltration.chronologicalArrival (p i) k ω : WithTop ℝ)) :
    chainTime p (i + 1) ω ≤ (ArrivalFiltration.chronologicalArrival (p i) k ω : WithTop ℝ) := by
  rw [chainTime_succ]
  exact ExtendedNextRing.after_le_arrival (ArrivalFiltration.chronologicalArrival (p i))
    (chainTime p i) (ArrivalFiltration.chronologicalArrival_monotone (p i)) ω k hfuture

/-- Domination by a specified finite chronological arrival chain.
The first arrival must be strictly after zero; zero-time exceptional arrivals
cannot dominate the construction's first strict next ring. -/
theorem chainTime_le_witness (p : Nat → V) (index : Nat → Nat) (r : Nat)
    (ω : ExponentialClocks.Sample V) (hr : 0 < r)
    (hstart : 0 < ArrivalFiltration.chronologicalArrival (p 0) (index 0) ω)
    (hstep : ∀ i, i + 1 < r →
      ArrivalFiltration.chronologicalArrival (p i) (index i) ω <
        ArrivalFiltration.chronologicalArrival (p (i + 1)) (index (i + 1)) ω) :
    chainTime p r ω ≤
      (ArrivalFiltration.chronologicalArrival (p (r - 1)) (index (r - 1)) ω : WithTop ℝ) := by
  have hdom : ∀ j, j < r → chainTime p (j + 1) ω ≤
      (ArrivalFiltration.chronologicalArrival (p j) (index j) ω : WithTop ℝ) := by
    intro j
    induction j with
    | zero =>
      intro _
      apply chainTime_succ_le_arrival p 0 (index 0) ω
      rw [chainTime_zero]
      exact_mod_cast hstart
    | succ j ih =>
      intro hj
      apply chainTime_succ_le_arrival p (j + 1) (index (j + 1)) ω
      exact (ih (by omega)).trans_lt (WithTop.coe_lt_coe.mpr (hstep j hj))
  have hlast := hdom (r - 1) (by omega)
  have hr' : r - 1 + 1 = r := by omega
  simpa only [hr'] using hlast

end MathResearchAnalysis.GreedyClockChain
