module
public import MathResearchAnalysis.ClockGapReset
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
set_option autoImplicit false
/-! A deterministic partition of elapsed time by actual clipped clock gaps.
No expectation identity, Poisson law or compensation formula is an input. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.ClockGapOccupation
open MeasureTheory Filter
variable {V : Type*}

def exposure (v : V) (k : Nat) (t : Real) (ω : ExponentialClocks.Sample V) : Real :=
  min (max (ExponentialClocks.gap v k ω) 0)
    (max 0 (t - ClockCandidateIntervals.before v k ω))

theorem exposure_nonnegative (v : V) (k : Nat) (t : Real) (ω : ExponentialClocks.Sample V) :
    0 ≤ exposure v k t ω :=
  le_min (le_max_right _ _) (le_max_left _ _)

theorem exposure_measurable (v : V) (k : Nat) (t : Real) : Measurable (exposure v k t) :=
  ((ExponentialClocks.gap_measurable v k).max measurable_const).min
    (measurable_const.max (measurable_const.sub (ClockCandidateIntervals.before_measurable v k)))

theorem exposure_le_horizon (v : V) (k : Nat) (t : Real) (ht : 0 ≤ t)
    (ω : ExponentialClocks.Sample V) : exposure v k t ω ≤ t := by
  apply (min_le_right _ _).trans
  exact max_le ht (sub_le_self _ (ClockCandidateIntervals.before_nonnegative v k ω))

theorem min_gap_eq_difference (a d t : Real) (hd : 0 ≤ d) :
    min d (max 0 (t-a)) = min t (a+d) - min t a := by
  by_cases ha : a ≤ t
  · rw [max_eq_right (sub_nonneg.mpr ha), min_eq_right ha]
    by_cases had : a+d ≤ t
    · rw [min_eq_right had, min_eq_left (by linarith)]
      ring
    · rw [min_eq_left (by linarith : t ≤ a+d), min_eq_right (by linarith : t-a ≤ d)]
  · have hta : t ≤ a := le_of_not_ge ha
    rw [max_eq_left (by linarith : t-a ≤ 0), min_eq_right hd,
      min_eq_left (by linarith : t ≤ a+d), min_eq_left hta, sub_self]

theorem exposure_eq_min_sub (v : V) (k : Nat) (t : Real) (ω : ExponentialClocks.Sample V) :
    exposure v k t ω = min t (ClockCandidateIntervals.before v (k+1) ω) -
      min t (ClockCandidateIntervals.before v k ω) := by
  rw [exposure, min_gap_eq_difference _ _ _ (le_max_right _ _),
    ← ClockCandidateIntervals.arrival_eq_before_add, ← ClockCandidateIntervals.before_succ]

theorem sum_exposure (v : V) (n : Nat) (t : Real) (ht : 0 ≤ t)
    (ω : ExponentialClocks.Sample V) :
    ∑ k ∈ Finset.range n, exposure v k t ω = min t (ClockCandidateIntervals.before v n ω) := by
  simp_rw [exposure_eq_min_sub]
  simpa only [ClockCandidateIntervals.before_zero, min_eq_right ht, sub_zero] using
    Finset.sum_range_sub (fun j : Nat => min t (ClockCandidateIntervals.before v j ω)) n

theorem exposure_zero_of_horizon_le_before (v : V) (k : Nat) (t : Real)
    (ω : ExponentialClocks.Sample V) (h : t ≤ ClockCandidateIntervals.before v k ω) :
    exposure v k t ω = 0 := by
  simp only [exposure, max_eq_left (sub_nonpos.mpr h), min_eq_right (le_max_right _ _)]

theorem tsum_exposure_of_before (v : V) (n : Nat) (t : Real) (ht : 0 ≤ t)
    (ω : ExponentialClocks.Sample V) (hn : t ≤ ClockCandidateIntervals.before v n ω) :
    ∑' k : Nat, ENNReal.ofReal (exposure v k t ω) = ENNReal.ofReal t := by
  rw [tsum_eq_sum (s := Finset.range n) (fun k hk => ?_)]
  · rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => exposure_nonnegative v k t ω),
      sum_exposure v n t ht ω, min_eq_left hn]
  · rw [exposure_zero_of_horizon_le_before v k t ω
      (hn.trans (ClockCandidateIntervals.before_monotone v ω (by simpa using hk))), ENNReal.ofReal_zero]

theorem tsum_exposure_ae [Countable V] :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ v t, 0 ≤ t →
      ∑' k : Nat, ENNReal.ofReal (exposure v k t ω) = ENNReal.ofReal t := by
  filter_upwards [ArrivalFiltration.chronologicalArrival_unbounded_ae (V := V)] with ω hω
  intro v t ht
  obtain ⟨n, hn⟩ := eventually_atTop.mp ((tendsto_atTop.mp (hω v)) t)
  exact tsum_exposure_of_before v (n+1) t ht ω (by
    simpa only [ClockCandidateIntervals.before_succ] using hn n le_rfl)
end MathResearchAnalysis.ClockGapOccupation
