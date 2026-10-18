module

public import MathResearchAnalysis.RankClockCensoring
public import MathResearchAnalysis.SchedulingFailure

set_option autoImplicit false

/-!
# Two-way actual clock/scan nonzero probabilities

The endpoint probability is taken in the genuine clock/identity-mark product
space. Fixed scan probabilities use the actual finite cold kernels. Fubini
and the two actual clock-wise censoring comparisons supply the inequalities;
only the actual scheduling failure probabilities are added. No droplet bound
or probability-comparison conclusion is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace MathResearchAnalysis.ClockRecoveryComparison

abbrev Site (n : Nat) := SquareTasks.Vertex n
abbrev Config (n : Nat) := SquareSpin.Config n
abbrev ClockSample (n : Nat) := ExponentialClocks.Sample (Site n)

def nonzero {n : Nat} (f : Config n) : ℝ := by
  classical
  exact if f = (fun _ => false) then 0 else 1

theorem nonzero_nonneg {n : Nat} (f : Config n) : 0 ≤ nonzero f := by
  classical
  unfold nonzero
  split_ifs <;> norm_num

theorem nonzero_le_one {n : Nat} (f : Config n) : nonzero f ≤ 1 := by
  classical
  unfold nonzero
  split_ifs <;> norm_num

theorem nonzero_monotone (n : Nat) : Monotone (@nonzero n) := by
  classical
  intro f g hfg
  by_cases hf : f = (fun _ => false)
  · simpa only [nonzero, ite_eq_left hf] using nonzero_nonneg g
  · by_cases hg : g = (fun _ => false)
    · have hz : f = (fun _ => false) := le_antisymm (by simpa only [hg] using hfg)
        (fun v => Bool.false_le _)
      exact False.elim (hf hz)
    · simp only [nonzero, ite_eq_right hf, ite_eq_right hg, le_refl]

theorem coldWord_nonzero_bounds {n : Nat} (word : List (Site n)) (f : Config n) :
    0 ≤ ZeroTemperature.coldWord word nonzero f ∧
      ZeroTemperature.coldWord word nonzero f ≤ 1 := by
  rw [ZeroTemperature.coldWord_eq_actualMajorityWordMean]
  induction word generalizing f with
  | nil => exact ⟨nonzero_nonneg f, nonzero_le_one f⟩
  | cons v rest ih =>
    have ht := ih (SquareSpin.cellUpdate f v true)
    have hf := ih (SquareSpin.cellUpdate f v false)
    simp only [ZeroTemperature.actualMajorityWordMean]
    constructor <;> linarith [ht.1, ht.2, hf.1, hf.2]

def scanProbability (n : Nat) (c : Bool) (count : Nat) : ℝ :=
  SquareScanKernel.scanMean n c 0 count nonzero (SquarePWMeasure.topConfig n)

def clockProbability (n : Nat) (t : ℝ) : ℝ :=
  (ClockWordMarks.measure n).real
    {z | ClockExecutionLaw.endpoint n t (SquarePWMeasure.topConfig n) z ≠ (fun _ => false)}

theorem clockProbability_eq_integral (n : Nat) (t : ℝ) :
    clockProbability n t =
      ∫ ω, ClockEndpointMean.wordMean n t nonzero (SquarePWMeasure.topConfig n) ω
        ∂ExponentialClocks.clockMeasure (Site n) := by
  classical
  let E := {z | ClockExecutionLaw.endpoint n t (SquarePWMeasure.topConfig n) z ≠
    (fun _ => false)}
  have hE : MeasurableSet E := by
    exact ((ClockExecutionLaw.endpoint_measurable n t (SquarePWMeasure.topConfig n))
      (measurableSet_singleton (fun _ => false))).compl
  have heq : (fun z => nonzero
      (ClockExecutionLaw.endpoint n t (SquarePWMeasure.topConfig n) z)) =
      E.indicator (fun _ => (1 : ℝ)) := by
    funext z
    by_cases hz : ClockExecutionLaw.endpoint n t (SquarePWMeasure.topConfig n) z =
        (fun _ => false) <;> simp [nonzero, E, hz]
  rw [← ClockEndpointMean.integral_endpoint_eq_integral_wordMean]
  rw [heq]
  exact (integral_indicator_one hE).symm

/-- An integral comparison paying for a single measurable bad event. -/
theorem integral_le_add_bad {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hi : Integrable f μ)
    (p : ℝ) (hp : 0 ≤ p) (B : Set Ω) (hB : MeasurableSet B)
    (hf : ∀ᵐ ω ∂μ, f ω ≤ 1)
    (hgood : ∀ᵐ ω ∂μ, ω ∉ B → f ω ≤ p) :
    (∫ ω, f ω ∂μ) ≤ p + μ.real B := by
  have hbint : Integrable (B.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hB
  have hbound : ∀ᵐ ω ∂μ, f ω ≤ p + B.indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [hf, hgood] with ω hf hg
    by_cases h : ω ∈ B
    · rw [Set.indicator_of_mem h]
      linarith
    · rw [Set.indicator_of_notMem h, add_zero]
      exact hg h
  have h := integral_mono_ae hi ((integrable_const p).add hbint) hbound
  simpa only [Pi.add_apply, integral_add (integrable_const p) hbint, integral_const,
    probReal_univ, one_smul, integral_indicator_const (1 : ℝ) hB,
    smul_eq_mul, mul_one, one_mul] using h

/-- Complete actual task layers bound the physical endpoint, with their genuine failure event. -/
theorem clockProbability_le_scan_add_completion (n : Nat) (c : Bool) (k : Nat) (t : ℝ) :
    clockProbability n t ≤ scanProbability n c (k + 1) +
      (ExponentialClocks.clockMeasure (Site n)).real
        {ω | (t : WithTop ℝ) < ClockMaximum.squareMaximum n c k ω} := by
  rw [clockProbability_eq_integral]
  apply integral_le_add_bad _ _
    (ClockEndpointMean.wordMean_integrable n t nonzero (SquarePWMeasure.topConfig n))
    _ (coldWord_nonzero_bounds _ _).1 _
    (ActualClockTail.actual_square_eight_tail n c k t).1
  · exact ae_of_all _ fun ω => (coldWord_nonzero_bounds _ _).2
  · filter_upwards [ClockSelectedWord.regular_ae n] with ω hω hgood
    have hmax : ClockMaximum.squareMaximum n c k ω ≤ (t : WithTop ℝ) :=
      le_of_not_gt hgood
    exact RankClockCensoring.clockMean_le_scanMean_of_completed n c k ω hω t hmax
      nonzero (nonzero_monotone n)

/-- The fixed complete scan is bounded by the actual physical endpoint and rank failure. -/
theorem scanProbability_le_clock_add_rank (n : Nat) (q : Nat) (t : ℝ) :
    scanProbability n true (2 * q) ≤ clockProbability n t +
      (ExponentialClocks.clockMeasure (Site n)).real (ClockRankTail.rankLarge n t q) := by
  let μ := ExponentialClocks.clockMeasure (Site n)
  let g := ClockEndpointMean.wordMean n t nonzero (SquarePWMeasure.topConfig n)
  let B := ClockRankTail.rankLarge n t q
  have hB : MeasurableSet B := ClockRankTail.rankLarge_measurable n t q
  have hi : Integrable g μ :=
    ClockEndpointMean.wordMean_integrable n t nonzero (SquarePWMeasure.topConfig n)
  have hbint : Integrable (B.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hB
  have hbound : ∀ ω, scanProbability n true (2 * q) ≤
      g ω + B.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases h : ω ∈ B
    · rw [Set.indicator_of_mem h]
      have hp := (coldWord_nonzero_bounds (SquareScanKernel.scanWord n true 0 (2 * q))
        (SquarePWMeasure.topConfig n)).2
      have hg := (coldWord_nonzero_bounds ((ClockEventWord.word ω t).reverse.map Prod.fst)
        (SquarePWMeasure.topConfig n)).1
      change scanProbability n true (2 * q) ≤ g ω + 1
      change scanProbability n true (2 * q) ≤ 1 at hp
      change 0 ≤ g ω at hg
      linarith
    · rw [Set.indicator_of_notMem h, add_zero]
      exact RankClockCensoring.scanMean_le_wordMean ω t q h nonzero (nonzero_monotone n)
  have h := integral_mono_ae (integrable_const (scanProbability n true (2 * q)))
    (hi.add hbint) (ae_of_all _ hbound)
  change (∫ _ω, scanProbability n true (2 * q) ∂μ) ≤
    ∫ ω, g ω + B.indicator (fun _ => (1 : ℝ)) ω ∂μ at h
  rw [integral_const, probReal_univ, one_smul,
    integral_add hi hbint, integral_indicator_const (1 : ℝ) hB,
    smul_eq_mul, mul_one] at h
  rw [clockProbability_eq_integral]
  exact h

/-- Both directions at the actual common explicit scheduling scale. -/
theorem two_way_scheduling_scale (n : Nat) (c : Bool) (k : Nat) :
    clockProbability n (SchedulingFailure.time k) ≤ scanProbability n c (k + 1) +
        ((6 : ℝ) / 5) * (n + 2 : ℝ) ^ 2 * ((2 : ℝ)⁻¹) ^ (k + 1) ∧
      scanProbability n true (2 * SchedulingFailure.rankThreshold k) ≤
        clockProbability n (SchedulingFailure.time k) +
          ((6 : ℝ) / 5) * (n + 2 : ℝ) ^ 2 * ((2 : ℝ)⁻¹) ^ (k + 1) := by
  have hbad := SchedulingFailure.bad_tail n c k
  have hcompletion : (ExponentialClocks.clockMeasure (Site n)).real
      {ω | (SchedulingFailure.time k : WithTop ℝ) < ClockMaximum.squareMaximum n c k ω} ≤
      (ExponentialClocks.clockMeasure (Site n)).real (SchedulingFailure.bad n c k) :=
    measureReal_mono Set.subset_union_right
  have hrank : (ExponentialClocks.clockMeasure (Site n)).real
      (ClockRankTail.rankLarge n (SchedulingFailure.time k) (SchedulingFailure.rankThreshold k)) ≤
      (ExponentialClocks.clockMeasure (Site n)).real (SchedulingFailure.bad n c k) :=
    measureReal_mono Set.subset_union_left
  constructor
  · exact (clockProbability_le_scan_add_completion n c k (SchedulingFailure.time k)).trans
      (add_le_add le_rfl (hcompletion.trans hbad))
  · exact (scanProbability_le_clock_add_rank n (SchedulingFailure.rankThreshold k)
      (SchedulingFailure.time k)).trans (add_le_add le_rfl (hrank.trans hbad))

end MathResearchAnalysis.ClockRecoveryComparison
