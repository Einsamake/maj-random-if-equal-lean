module

public import MathResearchAnalysis.ClockMaximum
public import MathResearchAnalysis.ExponentialMemoryless

set_option autoImplicit false

/-!
# Unconditional first-layer laws and physical maximum tails

Readiness at the first positive layer is zero. On the full-measure event where
the initial interarrival gap is positive, `Nat.find` selects arrival index zero.
Thus the actual first completion and delay inherit the genuine exponential law
from the already constructed product coordinates. The physical first-layer
maximum tail follows from the exact exponential survival probability and a
finite union bound, without any waiting-law or history-independence assumption.

This does not prove the waiting law or strong Markov property at later random
readiness times.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace MathResearchAnalysis.FirstLayerClock

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem chronologicalArrival_zero (v : V) (ω : ExponentialClocks.Sample V) :
    ArrivalFiltration.chronologicalArrival v 0 ω = max (ExponentialClocks.gap v 0 ω) 0 := by
  simp [ArrivalFiltration.chronologicalArrival]

/-- Positive first gaps force the actual least strict-arrival index to be zero. -/
theorem completion_one_eq_of_gap_positive (M : TaskPaths.System V) (v : V)
    (ω : ExponentialClocks.Sample V) (hpos : 0 < ExponentialClocks.gap v 0 ω) :
    ClockReadiness.completion M 1 v ω = (ExponentialClocks.gap v 0 ω : WithTop ℝ) := by
  have hfirst : ClockReadiness.ready M 0 v ω <
      (ArrivalFiltration.chronologicalArrival v 0 ω : WithTop ℝ) := by
    rw [ClockReadiness.ready_zero, chronologicalArrival_zero, max_eq_left hpos.le]
    exact WithTop.coe_lt_coe.mpr hpos
  have hex : ∃ k, ClockReadiness.ready M 0 v ω <
      (ArrivalFiltration.chronologicalArrival v k ω : WithTop ℝ) := ⟨0, hfirst⟩
  have hfind : Nat.find hex = 0 := (Nat.find_eq_zero hex).mpr hfirst
  rw [ClockReadiness.completion_succ M 0 v ω,
    ExtendedNextRing.after_eq_coe (ArrivalFiltration.chronologicalArrival v)
      (ClockReadiness.ready M 0 v) ω hex,
    hfind, chronologicalArrival_zero, max_eq_left hpos.le]

theorem completion_one_eq_gap_ae (M : TaskPaths.System V) (v : V) :
    ClockReadiness.completion M 1 v =ᵐ[ExponentialClocks.clockMeasure V]
      fun ω => (ExponentialClocks.gap v 0 ω : WithTop ℝ) := by
  filter_upwards [ExponentialClocks.gap_positive_ae v 0] with ω hω
  exact completion_one_eq_of_gap_positive M v ω hω

theorem delay_zero_eq_gap_ae (M : TaskPaths.System V) (v : V) :
    TaskClockBridge.delay M 0 v =ᵐ[ExponentialClocks.clockMeasure V]
      ExponentialClocks.gap v 0 := by
  filter_upwards [ExponentialClocks.gap_positive_ae v 0] with ω hω
  simp [TaskClockBridge.delay, TaskClockBridge.realCompletion, TaskClockBridge.realReady,
    completion_one_eq_of_gap_positive M v ω hω, ClockReadiness.ready_zero,
    max_eq_left hω.le]

/-- The first actual delay has its exponential law from the probability model. -/
theorem delay_zero_hasLaw (M : TaskPaths.System V) (v : V) :
    HasLaw (TaskClockBridge.delay M 0 v) (expMeasure 1) (ExponentialClocks.clockMeasure V) :=
  (ExponentialClocks.gap_hasLaw v 0).congr (delay_zero_eq_gap_ae M v)

theorem completion_one_exceeds_ae (M : TaskPaths.System V) (v : V) (t : ℝ) :
    {ω | (t : WithTop ℝ) < ClockReadiness.completion M 1 v ω}
      =ᵐ[ExponentialClocks.clockMeasure V] {ω | t < ExponentialClocks.gap v 0 ω} := by
  filter_upwards [completion_one_eq_gap_ae M v] with ω hω
  apply propext
  simp only [hω, WithTop.coe_lt_coe]

/-- Exact survival probability for an actual first completion. -/
theorem completion_one_tail_real (M : TaskPaths.System V) (v : V) (t : ℝ) (ht : 0 ≤ t) :
    (ExponentialClocks.clockMeasure V).real
      {ω | (t : WithTop ℝ) < ClockReadiness.completion M 1 v ω} = Real.exp (-t) := by
  rw [measureReal_congr (completion_one_exceeds_ae M v t)]
  have hlaw := (ExponentialClocks.gap_hasLaw v 0).measureReal_eq
    (p := fun x : ℝ => t < x) (measurableSet_lt measurable_const measurable_id)
  exact hlaw.trans (ExponentialMemoryless.tail_real ht)

theorem squareMaximum_zero (n : Nat) (c : Bool)
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) :
    ClockMaximum.squareMaximum n c 0 ω = ClockMaximum.squareLayer n c 0 ω := by
  simp [ClockMaximum.squareMaximum]

/-- An exact event identity for the extended physical maximum, including exceptional paths. -/
theorem squareMaximum_zero_exceeds_eq (n : Nat) (c : Bool) (t : ℝ) :
    {ω | (t : WithTop ℝ) < ClockMaximum.squareMaximum n c 0 ω} =
      ⋃ v ∈ SquareTasks.tasks n c 0,
        {ω | (t : WithTop ℝ) < ClockReadiness.completion (SquareTasks.system n) 1 v ω} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, squareMaximum_zero,
    ClockMaximum.squareLayer]
  exact Finset.lt_sup'_iff (SquareTasks.tasks_nonempty n c 0)

/-- Unconditional first-layer physical tail, counted by the actual selected task set. -/
theorem actual_square_first_tail (n : Nat) (c : Bool) (t : ℝ) (ht : 0 ≤ t) :
    MeasurableSet {ω | (t : WithTop ℝ) < ClockMaximum.squareMaximum n c 0 ω} ∧
      (ExponentialClocks.clockMeasure (SquareTasks.Vertex n)).real
        {ω | (t : WithTop ℝ) < ClockMaximum.squareMaximum n c 0 ω} ≤
          ((SquareTasks.tasks n c 0).card : ℝ) * Real.exp (-t) := by
  refine ⟨(ArrivalFiltration.clockHistory (SquareTasks.Vertex n)).le t _
    ((ClockMaximum.squareMaximum_isStoppingTime n c 0).measurableSet_gt t), ?_⟩
  rw [squareMaximum_zero_exceeds_eq]
  calc
    _ ≤ ∑ v ∈ SquareTasks.tasks n c 0,
        (ExponentialClocks.clockMeasure (SquareTasks.Vertex n)).real
          {ω | (t : WithTop ℝ) < ClockReadiness.completion (SquareTasks.system n) 1 v ω} :=
      measureReal_biUnion_finset_le (SquareTasks.tasks n c 0) _
    _ = ∑ _v ∈ SquareTasks.tasks n c 0, Real.exp (-t) := by
      apply Finset.sum_congr rfl
      intro v _
      exact completion_one_tail_real (SquareTasks.system n) v t ht
    _ = ((SquareTasks.tasks n c 0).card : ℝ) * Real.exp (-t) := by simp

/-- The corresponding square-area bound has no law, independence or MGF hypotheses. -/
theorem actual_square_first_area_tail (n : Nat) (c : Bool) (t : ℝ) (ht : 0 ≤ t) :
    MeasurableSet {ω | (t : WithTop ℝ) < ClockMaximum.squareMaximum n c 0 ω} ∧
      (ExponentialClocks.clockMeasure (SquareTasks.Vertex n)).real
        {ω | (t : WithTop ℝ) < ClockMaximum.squareMaximum n c 0 ω} ≤
          (n + 2 : ℝ) ^ 2 * Real.exp (-t) := by
  have h := actual_square_first_tail n c t ht
  have hcard : ((SquareTasks.tasks n c 0).card : ℝ) ≤ (n + 2 : ℝ) ^ 2 := by
    exact_mod_cast SquareTasks.tasks_card_le n c 0
  exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le)⟩

end MathResearchAnalysis.FirstLayerClock
