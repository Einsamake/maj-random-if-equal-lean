module

public import MathResearchAnalysis.RandomThresholdSurvival
public import MathResearchAnalysis.HistoryEventInvariant
public import MathResearchAnalysis.ClockCandidateIntervals

set_option autoImplicit false

/-!
# Deleting and resetting a fixed exponential gap

The reset is a total measurable map of the actual coordinate sample space.
All deterministic chronological statements use clipped gaps, including on
exceptional negative-coordinate paths. No residual distribution or strong
Markov property is presumed here.
-/

public noncomputable section

open MeasureTheory Set

namespace MathResearchAnalysis.ClockGapReset

variable {V : Type*}

/-- Insert one gap into the deleted-coordinate sample without changing the others. -/
@[expose] def reconstruct (v : V) (k : Nat) (d : ℝ)
    (h : RandomThresholdSurvival.RestSample V v k) : ExponentialClocks.Sample V := by
  classical
  exact fun i => if hi : i = (v, k) then d else h ⟨i, hi⟩

theorem reconstruct_chosen (v : V) (k : Nat) (d : ℝ)
    (h : RandomThresholdSurvival.RestSample V v k) : reconstruct v k d h (v, k) = d := by
  simp [reconstruct]

theorem reconstruct_other (v : V) (k : Nat) (d : ℝ)
    (h : RandomThresholdSurvival.RestSample V v k) (i : V × Nat) (hi : i ≠ (v, k)) :
    reconstruct v k d h i = h ⟨i, hi⟩ := by
  simp [reconstruct, hi]

theorem rest_reconstruct (v : V) (k : Nat) (d : ℝ)
    (h : RandomThresholdSurvival.RestSample V v k) :
    RandomThresholdSurvival.restCoordinates v k (reconstruct v k d h) = h := by
  funext i
  exact reconstruct_other v k d h i i.property

/-- The actual sample is recovered by inserting its original gap into its own remaining coordinates. -/
theorem reconstruct_actual (v : V) (k : Nat) (ω : ExponentialClocks.Sample V) :
    reconstruct v k (ExponentialClocks.gap v k ω)
      (RandomThresholdSurvival.restCoordinates v k ω) = ω := by
  funext i
  by_cases hi : i = (v, k)
  · subst i
    exact reconstruct_chosen v k _ _
  · exact reconstruct_other v k _ _ i hi

theorem reconstruct_measurable (v : V) (k : Nat)
    (d : RandomThresholdSurvival.RestSample V v k → ℝ) (hd : Measurable d) :
    Measurable (fun h => reconstruct v k (d h) h) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i = (v, k)
  · simpa only [reconstruct, dite_eq_left hi] using hd
  · simpa only [reconstruct, dite_eq_right hi] using
      (measurable_pi_apply (⟨i, hi⟩ : {i : V × Nat // i ≠ (v, k)}) :
        Measurable (fun h : RandomThresholdSurvival.RestSample V v k => h ⟨i, hi⟩))

/-- The preceding time uses only the first `k` clipped gaps.
The inserted zero is never accessed by this prefix sum. -/
@[expose] def prior (v : V) (k : Nat)
    (h : RandomThresholdSurvival.RestSample V v k) : ℝ :=
  ∑ j ∈ Finset.range k, max (reconstruct v k 0 h (v, j)) 0

theorem prior_nonnegative (v : V) (k : Nat)
    (h : RandomThresholdSurvival.RestSample V v k) : 0 ≤ prior v k h := by
  apply Finset.sum_nonneg
  exact fun _ _ => le_max_right _ _

theorem prior_measurable (v : V) (k : Nat) : Measurable (prior v k) := by
  unfold prior
  exact Finset.measurable_sum _ (fun j _ =>
    ((measurable_pi_apply (v, j)).comp
      (reconstruct_measurable v k (fun _ => 0) measurable_const)).max measurable_const)

theorem prior_rest_eq_sum (v : V) (k : Nat) (ω : ExponentialClocks.Sample V) :
    prior v k (RandomThresholdSurvival.restCoordinates v k ω) =
      ∑ j ∈ Finset.range k, max (ExponentialClocks.gap v j ω) 0 := by
  apply Finset.sum_congr rfl
  intro j hj
  have hne : (v, j) ≠ (v, k) := by
    intro heq
    have h := congrArg Prod.snd heq
    exact (Nat.ne_of_lt (Finset.mem_range.mp hj)) h
  rw [reconstruct_other v k 0 _ (v, j) hne]
  rfl

/-- A nonnegative elapsed cutoff, defined even before the previous ring. -/
@[expose] def cutoff (v : V) (k : Nat) (r : ℝ)
    (h : RandomThresholdSurvival.RestSample V v k) : ℝ := max 0 (r - prior v k h)

theorem cutoff_nonnegative (v : V) (k : Nat) (r : ℝ)
    (h : RandomThresholdSurvival.RestSample V v k) : 0 ≤ cutoff v k r h :=
  le_max_left _ _

theorem cutoff_ge_sub (v : V) (k : Nat) (r : ℝ)
    (h : RandomThresholdSurvival.RestSample V v k) : r - prior v k h ≤ cutoff v k r h :=
  le_max_right _ _

theorem cutoff_eq_sub (v : V) (k : Nat) (r : ℝ)
    (h : RandomThresholdSurvival.RestSample V v k) (hp : prior v k h ≤ r) :
    cutoff v k r h = r - prior v k h :=
  max_eq_right (sub_nonneg.mpr hp)

theorem cutoff_measurable (v : V) (k : Nat) (r : ℝ) : Measurable (cutoff v k r) :=
  measurable_const.max (measurable_const.sub (prior_measurable v k))

/-- The measurable reset places the current gap beyond the elapsed cutoff. -/
@[expose] def reset (v : V) (k : Nat) (r : ℝ)
    (h : RandomThresholdSurvival.RestSample V v k) : ExponentialClocks.Sample V :=
  reconstruct v k (cutoff v k r h + 1) h

theorem reset_measurable (v : V) (k : Nat) (r : ℝ) : Measurable (reset v k r) :=
  reconstruct_measurable v k _ ((cutoff_measurable v k r).add_const 1)

theorem rest_reset (v : V) (k : Nat) (r : ℝ)
    (h : RandomThresholdSurvival.RestSample V v k) :
    RandomThresholdSurvival.restCoordinates v k (reset v k r h) = h :=
  rest_reconstruct v k _ h

theorem reset_chosen_gap (v : V) (k : Nat) (r : ℝ)
    (h : RandomThresholdSurvival.RestSample V v k) :
    ExponentialClocks.gap v k (reset v k r h) = cutoff v k r h + 1 :=
  reconstruct_chosen v k _ h

theorem reset_other_gap (v : V) (k : Nat) (r : ℝ)
    (ω : ExponentialClocks.Sample V) (i : V × Nat) (hi : i ≠ (v, k)) :
    reset v k r (RandomThresholdSurvival.restCoordinates v k ω) i = ω i :=
  reconstruct_other v k _ _ i hi

/-- The rings of every other site retain their exact times on all samples. -/
theorem arrival_other_site_eq (v w : V) (k n : Nat) (r : ℝ)
    (ω : ExponentialClocks.Sample V) (hwv : w ≠ v) :
    ArrivalFiltration.chronologicalArrival w n
      (reset v k r (RandomThresholdSurvival.restCoordinates v k ω)) =
      ArrivalFiltration.chronologicalArrival w n ω := by
  apply Finset.sum_congr rfl
  intro j _
  have hne : (w, j) ≠ (v, k) := fun h => hwv (congrArg Prod.fst h)
  rw [show ExponentialClocks.gap w j
      (reset v k r (RandomThresholdSurvival.restCoordinates v k ω)) =
      ExponentialClocks.gap w j ω from reset_other_gap v k r ω (w, j) hne]

/-- The first `k` rings at the reset site likewise retain their exact times. -/
theorem arrival_before_gap_eq (v : V) (k n : Nat) (r : ℝ)
    (ω : ExponentialClocks.Sample V) (hn : n < k) :
    ArrivalFiltration.chronologicalArrival v n
      (reset v k r (RandomThresholdSurvival.restCoordinates v k ω)) =
      ArrivalFiltration.chronologicalArrival v n ω := by
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hne : (v, j) ≠ (v, k) := by
    intro heq
    exact (Nat.ne_of_lt (hjn.trans_lt hn)) (congrArg Prod.snd heq)
  rw [show ExponentialClocks.gap v j
      (reset v k r (RandomThresholdSurvival.restCoordinates v k ω)) =
      ExponentialClocks.gap v j ω from reset_other_gap v k r ω (v, j) hne]

theorem reset_arrival_current_eq (v : V) (k : Nat) (r : ℝ)
    (h : RandomThresholdSurvival.RestSample V v k) :
    ArrivalFiltration.chronologicalArrival v k (reset v k r h) =
      prior v k h + cutoff v k r h + 1 := by
  unfold ArrivalFiltration.chronologicalArrival
  rw [Finset.sum_range_succ]
  have hp : (∑ j ∈ Finset.range k, max (ExponentialClocks.gap v j (reset v k r h)) 0) =
      prior v k h := by
    rw [← prior_rest_eq_sum v k (reset v k r h), rest_reset]
  rw [hp, reset_chosen_gap, max_eq_left (by linarith [cutoff_nonnegative v k r h])]
  ring

/-- The reset current ring is strictly beyond the observation time, pointwise. -/
theorem reset_arrival_current_gt (v : V) (k : Nat) (r : ℝ)
    (h : RandomThresholdSurvival.RestSample V v k) :
    r < ArrivalFiltration.chronologicalArrival v k (reset v k r h) := by
  rw [reset_arrival_current_eq]
  linarith [cutoff_ge_sub v k r h]

theorem reset_arrival_later_gt (v : V) (k n : Nat) (r : ℝ)
    (h : RandomThresholdSurvival.RestSample V v k) (hkn : k ≤ n) :
    r < ArrivalFiltration.chronologicalArrival v n (reset v k r h) :=
  (reset_arrival_current_gt v k r h).trans_le
    (ArrivalFiltration.chronologicalArrival_monotone v _ hkn)

/-- The Rest prefix is exactly the previous time used by the actual candidate intervals. -/
theorem prior_rest_eq_before (v : V) (k : Nat) (ω : ExponentialClocks.Sample V) :
    prior v k (RandomThresholdSurvival.restCoordinates v k ω) =
      ClockCandidateIntervals.before v k ω :=
  prior_rest_eq_sum v k ω

theorem before_reset_eq_prior (v : V) (k : Nat) (r : ℝ)
    (h : RandomThresholdSurvival.RestSample V v k) :
    ClockCandidateIntervals.before v k (reset v k r h) = prior v k h := by
  rw [← prior_rest_eq_before v k (reset v k r h), rest_reset]

/-- On an actual candidate interval, reset preserves each observation through physical time `r`. -/
theorem reset_generator_event_iff (v : V) (k : Nat) (r : ℝ)
    (ω : ExponentialClocks.Sample V) (hc : ClockCandidateIntervals.candidate v r k ω)
    (w : V) (j : Nat) (u : ℝ) (hu : u ≤ r) :
    (ArrivalFiltration.chronologicalArrival w j ω ≤ u ↔
      ArrivalFiltration.chronologicalArrival w j
        (reset v k r (RandomThresholdSurvival.restCoordinates v k ω)) ≤ u) := by
  by_cases hwv : w = v
  · subst w
    by_cases hjk : j < k
    · rw [arrival_before_gap_eq v k j r ω hjk]
    · have hkj : k ≤ j := Nat.le_of_not_gt hjk
      have horig : u < ArrivalFiltration.chronologicalArrival v j ω :=
        hu.trans_lt (hc.2.trans_le (ArrivalFiltration.chronologicalArrival_monotone v ω hkj))
      have hreset : u < ArrivalFiltration.chronologicalArrival v j
          (reset v k r (RandomThresholdSurvival.restCoordinates v k ω)) :=
        hu.trans_lt (reset_arrival_later_gt v k j r _ hkj)
      simp only [not_le.mpr horig, not_le.mpr hreset]
  · rw [arrival_other_site_eq v w k j r ω hwv]

/-- Every actual common-history event, including other sites, is preserved on that candidate. -/
theorem reset_history_event_iff (v : V) (k : Nat) (r : ℝ)
    (ω : ExponentialClocks.Sample V) (hc : ClockCandidateIntervals.candidate v r k ω)
    (E : Set (ExponentialClocks.Sample V))
    (hE : MeasurableSet[ArrivalFiltration.clockHistory V r] E) :
    (ω ∈ E ↔ reset v k r (RandomThresholdSurvival.restCoordinates v k ω) ∈ E) :=
  HistoryEventInvariant.clock_event_invariant r E hE ω _
    (reset_generator_event_iff v k r ω hc)

end MathResearchAnalysis.ClockGapReset
