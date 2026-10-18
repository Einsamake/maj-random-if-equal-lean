module

public import MathResearchAnalysis.ArrivalFiltration
public import MathResearchAnalysis.ExtendedNextRing
public import Mathlib.MeasureTheory.Measure.NullMeasurable

set_option autoImplicit false

/-!
# Deterministic-time candidate gap intervals

The `k`th candidate interval is the half-open interval from the sum of the
first `k` clipped gaps to arrival `k`. Candidates are disjoint and, for each
nonnegative deterministic time, cover almost every actual clock sample. A
candidate forces the least strict-next-arrival index to equal `k`, so the
extended next-ring survival event has an explicit current-gap representation.

Bad paths without future arrivals retain their infinite next ring. Coverage
and the full event decomposition are almost-everywhere statements proved from
the actual clock construction. No history factorization, reset argument,
memorylessness at random readiness, or strong Markov property is asserted.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Function
open scoped BigOperators

namespace MathResearchAnalysis.ClockCandidateIntervals

variable {V : Type*}

/-- Time immediately before the `k`th gap, including zero before the first gap. -/
def before (v : V) (k : Nat) (ω : ExponentialClocks.Sample V) : ℝ :=
  ∑ j ∈ Finset.range k, max (ExponentialClocks.gap v j ω) 0

/-- Arrival `k` is the first strict arrival after deterministic time `r`. -/
def candidate (v : V) (r : ℝ) (k : Nat) (ω : ExponentialClocks.Sample V) : Prop :=
  before v k ω ≤ r ∧ r < ArrivalFiltration.chronologicalArrival v k ω

theorem before_zero (v : V) (ω : ExponentialClocks.Sample V) : before v 0 ω = 0 := by
  simp [before]

theorem before_succ (v : V) (k : Nat) (ω : ExponentialClocks.Sample V) :
    before v (k + 1) ω = ArrivalFiltration.chronologicalArrival v k ω := rfl

theorem arrival_eq_before_add (v : V) (k : Nat) (ω : ExponentialClocks.Sample V) :
    ArrivalFiltration.chronologicalArrival v k ω =
      before v k ω + max (ExponentialClocks.gap v k ω) 0 := by
  exact Finset.sum_range_succ _ k

theorem before_nonnegative (v : V) (k : Nat) (ω : ExponentialClocks.Sample V) :
    0 ≤ before v k ω :=
  Finset.sum_nonneg (fun j _ => le_max_right (ExponentialClocks.gap v j ω) 0)

theorem before_monotone (v : V) (ω : ExponentialClocks.Sample V) :
    Monotone (fun k => before v k ω) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [before_succ, arrival_eq_before_add]
  exact le_add_of_nonneg_right (le_max_right _ _)

theorem arrival_le_before_of_lt (v : V) (ω : ExponentialClocks.Sample V)
    (j k : Nat) (hjk : j < k) :
    ArrivalFiltration.chronologicalArrival v j ω ≤ before v k ω := by
  rw [← before_succ]
  exact before_monotone v ω (Nat.succ_le_of_lt hjk)

theorem before_measurable (v : V) (k : Nat) : Measurable (before v k) := by
  unfold before
  exact Finset.measurable_sum _ (fun j _ =>
    (ExponentialClocks.gap_measurable v j).max measurable_const)

theorem candidate_measurableSet (v : V) (r : ℝ) (k : Nat) :
    MeasurableSet {ω | candidate v r k ω} :=
  (measurableSet_le (before_measurable v k) measurable_const).inter
    (measurableSet_lt measurable_const (ArrivalFiltration.chronologicalArrival_measurable v k))

/-- Knowing which gap straddles `r` only uses actual observations through `r`. -/
theorem candidate_history_measurableSet (v : V) (r : ℝ) (k : Nat) :
    MeasurableSet[ArrivalFiltration.clockHistory V r] {ω | candidate v r k ω} := by
  cases k with
  | zero =>
    by_cases hr : 0 ≤ r
    · simpa only [candidate, before_zero, hr, true_and, WithTop.coe_lt_coe] using
        (ArrivalFiltration.clock_arrival_isStoppingTime v 0).measurableSet_gt r
    · have heq : {ω | candidate v r 0 ω} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, candidate, before_zero, hr, false_and,
          Set.mem_empty_iff_false]
      rw [heq]
      exact @MeasurableSet.empty _ (ArrivalFiltration.clockHistory V r)
  | succ k =>
    have hb : MeasurableSet[ArrivalFiltration.clockHistory V r]
        {ω | ArrivalFiltration.chronologicalArrival v k ω ≤ r} := by
      simpa only [WithTop.coe_le_coe] using
        (ArrivalFiltration.clock_arrival_isStoppingTime v k).measurableSet_le r
    have ha : MeasurableSet[ArrivalFiltration.clockHistory V r]
        {ω | r < ArrivalFiltration.chronologicalArrival v (k + 1) ω} := by
      simpa only [WithTop.coe_lt_coe] using
        (ArrivalFiltration.clock_arrival_isStoppingTime v (k + 1)).measurableSet_gt r
    exact hb.inter ha

/-- The candidate interval selects exactly the actual least strict future arrival. -/
theorem candidate_iff_find (v : V) (r : ℝ) (hr : 0 ≤ r) (k : Nat)
    (ω : ExponentialClocks.Sample V)
    (hex : ∃ j, r < ArrivalFiltration.chronologicalArrival v j ω) :
    candidate v r k ω ↔ Nat.find hex = k := by
  constructor
  · rintro ⟨hbefore, hafter⟩
    apply (Nat.find_eq_iff hex).mpr
    refine ⟨hafter, fun j hj => ?_⟩
    exact not_lt_of_ge ((arrival_le_before_of_lt v ω j k hj).trans hbefore)
  · intro hfind
    have hafter : r < ArrivalFiltration.chronologicalArrival v k ω := by
      simpa only [hfind] using Nat.find_spec hex
    refine ⟨?_, hafter⟩
    cases k with
    | zero => simpa only [before_zero] using hr
    | succ k =>
      rw [before_succ]
      exact le_of_not_gt (Nat.find_min hex (by omega))

theorem candidate_unique (v : V) (r : ℝ) (i j : Nat)
    (ω : ExponentialClocks.Sample V) (hi : candidate v r i ω) (hj : candidate v r j ω) :
    i = j := by
  have hr : 0 ≤ r := (before_nonnegative v i ω).trans hi.1
  have hex : ∃ k, r < ArrivalFiltration.chronologicalArrival v k ω := ⟨i, hi.2⟩
  exact ((candidate_iff_find v r hr i ω hex).mp hi).symm.trans
    ((candidate_iff_find v r hr j ω hex).mp hj)

theorem candidate_pairwise_disjoint (v : V) (r : ℝ) :
    Pairwise (Disjoint on (fun k => {ω | candidate v r k ω})) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro ω hi hj
  exact hij (candidate_unique v r i j ω hi hj)

theorem candidate_exists_of_future (v : V) (r : ℝ) (hr : 0 ≤ r)
    (ω : ExponentialClocks.Sample V)
    (hex : ∃ k, r < ArrivalFiltration.chronologicalArrival v k ω) :
    ∃ k, candidate v r k ω :=
  ⟨Nat.find hex, (candidate_iff_find v r hr (Nat.find hex) ω hex).mpr rfl⟩

/-- This uses actual unbounded clock streams; no future ring is assumed as a model input. -/
theorem candidate_exists_ae [Countable V] (v : V) (r : ℝ) (hr : 0 ≤ r) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∃ k, candidate v r k ω := by
  filter_upwards [ArrivalFiltration.clock_future_arrival_ae v (fun _ => r)] with ω hω
  exact candidate_exists_of_future v r hr ω hω

theorem candidate_iUnion_ae_univ [Countable V] (v : V) (r : ℝ) (hr : 0 ≤ r) :
    (⋃ k, {ω | candidate v r k ω}) =ᵐ[ExponentialClocks.clockMeasure V] Set.univ := by
  filter_upwards [candidate_exists_ae v r hr] with ω hω
  apply propext
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact hω

theorem gap_positive_of_candidate (v : V) (r : ℝ) (k : Nat)
    (ω : ExponentialClocks.Sample V) (hc : candidate v r k ω) :
    0 < ExponentialClocks.gap v k ω := by
  by_contra hnot
  have hgap : ExponentialClocks.gap v k ω ≤ 0 := le_of_not_gt hnot
  have hafter := hc.2
  rw [arrival_eq_before_add, max_eq_right hgap, add_zero] at hafter
  exact not_lt_of_ge hc.1 hafter

theorem next_eq_arrival_of_candidate (v : V) (r : ℝ) (k : Nat)
    (ω : ExponentialClocks.Sample V) (hc : candidate v r k ω) :
    NextRing.extendedNextRing (ArrivalFiltration.chronologicalArrival v) (fun _ => r) ω =
      (ArrivalFiltration.chronologicalArrival v k ω : WithTop ℝ) := by
  have hr : 0 ≤ r := (before_nonnegative v k ω).trans hc.1
  have hex : ∃ j, r < ArrivalFiltration.chronologicalArrival v j ω := ⟨k, hc.2⟩
  rw [NextRing.extendedNextRing_eq_coe _ _ ω hex,
    (candidate_iff_find v r hr k ω hex).mp hc]

theorem after_eq_arrival_of_candidate (v : V) (r : ℝ) (k : Nat)
    (ω : ExponentialClocks.Sample V) (hc : candidate v r k ω) :
    ExtendedNextRing.after (ArrivalFiltration.chronologicalArrival v)
      (fun _ => (r : WithTop ℝ)) ω =
        (ArrivalFiltration.chronologicalArrival v k ω : WithTop ℝ) := by
  rw [ExtendedNextRing.after_eq_extendedNextRing]
  exact next_eq_arrival_of_candidate v r k ω hc

/-- On the candidate interval the next-ring survival event is a single raw-gap inequality.
This pointwise equivalence holds for every real `t`, and hence in particular for `t ≥ 0`. -/
theorem next_survival_iff_gap (v : V) (r t : ℝ) (k : Nat)
    (ω : ExponentialClocks.Sample V) (hc : candidate v r k ω) :
    ((r + t : ℝ) : WithTop ℝ) <
      NextRing.extendedNextRing (ArrivalFiltration.chronologicalArrival v) (fun _ => r) ω ↔
        r + t - before v k ω < ExponentialClocks.gap v k ω := by
  rw [next_eq_arrival_of_candidate v r k ω hc, WithTop.coe_lt_coe,
    arrival_eq_before_add, max_eq_left (gap_positive_of_candidate v r k ω hc).le]
  constructor <;> intro h <;> linarith

theorem candidate_survival_measurableSet (v : V) (r t : ℝ) (k : Nat) :
    MeasurableSet {ω | candidate v r k ω ∧
      r + t - before v k ω < ExponentialClocks.gap v k ω} :=
  (candidate_measurableSet v r k).inter
    (measurableSet_lt (measurable_const.sub (before_measurable v k))
      (ExponentialClocks.gap_measurable v k))

theorem candidate_survival_eq (v : V) (r t : ℝ) (k : Nat) :
    {ω | candidate v r k ω ∧ ((r + t : ℝ) : WithTop ℝ) <
      NextRing.extendedNextRing (ArrivalFiltration.chronologicalArrival v) (fun _ => r) ω} =
      {ω | candidate v r k ω ∧ r + t - before v k ω < ExponentialClocks.gap v k ω} := by
  ext ω
  change (candidate v r k ω ∧ _) ↔ (candidate v r k ω ∧ _)
  exact and_congr_right (next_survival_iff_gap v r t k ω)

theorem candidate_survival_pairwise_disjoint (v : V) (r t : ℝ) :
    Pairwise (Disjoint on (fun k => {ω | candidate v r k ω ∧
      r + t - before v k ω < ExponentialClocks.gap v k ω})) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro ω hi hj
  exact hij (candidate_unique v r i j ω hi.1 hj.1)

/-- The only discarded samples are the proved null exceptional set lacking a candidate. -/
theorem next_survival_iUnion_ae [Countable V] (v : V) (r t : ℝ) (hr : 0 ≤ r) :
    {ω | ((r + t : ℝ) : WithTop ℝ) <
      NextRing.extendedNextRing (ArrivalFiltration.chronologicalArrival v) (fun _ => r) ω}
        =ᵐ[ExponentialClocks.clockMeasure V]
      ⋃ k, {ω | candidate v r k ω ∧
        r + t - before v k ω < ExponentialClocks.gap v k ω} := by
  filter_upwards [candidate_exists_ae v r hr] with ω hω
  apply propext
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · intro hnext
    obtain ⟨k, hc⟩ := hω
    exact ⟨k, hc, (next_survival_iff_gap v r t k ω hc).mp hnext⟩
  · rintro ⟨k, hc, hgap⟩
    exact (next_survival_iff_gap v r t k ω hc).mpr hgap

/-- A countable disjoint-measure decomposition, with no finite-next-ring assumption. -/
theorem next_survival_measure_tsum [Countable V] (v : V) (r t : ℝ) (hr : 0 ≤ r) :
    ExponentialClocks.clockMeasure V {ω | ((r + t : ℝ) : WithTop ℝ) <
      NextRing.extendedNextRing (ArrivalFiltration.chronologicalArrival v) (fun _ => r) ω} =
        ∑' k : Nat, ExponentialClocks.clockMeasure V {ω | candidate v r k ω ∧
          r + t - before v k ω < ExponentialClocks.gap v k ω} := by
  rw [measure_congr (next_survival_iUnion_ae v r t hr)]
  exact measure_iUnion (candidate_survival_pairwise_disjoint v r t)
    (candidate_survival_measurableSet v r t)

/-- Intersecting any measurable event gives the same disjoint sum interface.
This is an event decomposition, not a factorization or independence assertion. -/
theorem next_survival_inter_measure_tsum [Countable V] (v : V) (r t : ℝ) (hr : 0 ≤ r)
    (E : Set (ExponentialClocks.Sample V)) (hE : MeasurableSet E) :
    ExponentialClocks.clockMeasure V (E ∩ {ω | ((r + t : ℝ) : WithTop ℝ) <
      NextRing.extendedNextRing (ArrivalFiltration.chronologicalArrival v) (fun _ => r) ω}) =
        ∑' k : Nat, ExponentialClocks.clockMeasure V (E ∩ {ω | candidate v r k ω ∧
          r + t - before v k ω < ExponentialClocks.gap v k ω}) := by
  have heq : (E ∩ {ω | ((r + t : ℝ) : WithTop ℝ) <
      NextRing.extendedNextRing (ArrivalFiltration.chronologicalArrival v) (fun _ => r) ω})
        =ᵐ[ExponentialClocks.clockMeasure V]
      E ∩ ⋃ k, {ω | candidate v r k ω ∧
        r + t - before v k ω < ExponentialClocks.gap v k ω} := by
    filter_upwards [next_survival_iUnion_ae v r t hr] with ω hω
    exact congrArg (fun p : Prop => ω ∈ E ∧ p) hω
  rw [measure_congr heq, Set.inter_iUnion]
  apply measure_iUnion
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    exact hij (candidate_unique v r i j ω hi.2.1 hj.2.1)
  · exact fun k => hE.inter (candidate_survival_measurableSet v r t k)

end MathResearchAnalysis.ClockCandidateIntervals
