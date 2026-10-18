module

public import MathResearchAnalysis.ClockMaximum
public import MathResearchAnalysis.ClockStoppedResidual

set_option autoImplicit false

/-!
# Actual fixed-path histories and closed clock-maximum tails

For an index inside a predetermined finite legal path, its constructed path
filtration is exactly the actual task-readiness stopping sigma-algebra. This
connects the stopped waiting law and independence to the existing actual
physical clock maximum, without supplying either as a new hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace MathResearchAnalysis.ActualClockTail

variable {V : Type*} [DecidableEq V]

theorem pathFiltration_eq_ready_sigma (M : TaskPaths.System V) (p : Nat → V) (r : Nat)
    (hedges : FixedClockPath.Edges M p r) (i : Nat) (hi : i < r) :
    FixedClockPath.pathFiltration M p r hedges i =
      (ClockReadiness.ready_isStoppingTime M i (p i)).measurableSpace := by
  apply MeasurableSpace.ext
  intro E
  change (MeasurableSet[⨆ t : ℝ, ArrivalFiltration.clockHistory V t] E ∧
    ∀ t : ℝ, MeasurableSet[ArrivalFiltration.clockHistory V t]
      (E ∩ {ω | FixedClockPath.pathReady M p r i ω ≤ (t : WithTop ℝ)})) ↔
    (MeasurableSet[⨆ t : ℝ, ArrivalFiltration.clockHistory V t] E ∧
    ∀ t : ℝ, MeasurableSet[ArrivalFiltration.clockHistory V t]
      (E ∩ {ω | ClockReadiness.ready M i (p i) ω ≤ (t : WithTop ℝ)}))
  simp only [FixedClockPath.pathReady, ite_eq_left hi]

/-- A legal list's sigma-algebra is the exact sigma-algebra at that actual task's readiness. -/
theorem listFiltration_eq_ready_sigma (M : TaskPaths.System V) (fallback : V) (k : Nat)
    (v : V) {p : List V} (hlegal : (TaskClockBridge.positiveSystem M).Legal k v p)
    (i : Nat) (hi : i < p.length) :
    FixedClockPath.listFiltration M fallback p i =
      (ClockReadiness.ready_isStoppingTime M i
        (FixedClockPath.forwardVertex fallback p i)).measurableSpace := by
  have hedges := FixedClockPath.legal_edges M fallback k v hlegal
  rw [FixedClockPath.listFiltration_of_edges M fallback p hedges]
  exact pathFiltration_eq_ready_sigma M (FixedClockPath.forwardVertex fallback p)
    p.length hedges i hi

theorem terminal_listFiltration_eq_ready_sigma (M : TaskPaths.System V) (fallback : V)
    (tasks : Finset V) (k : Nat) {p : List V}
    (hp : p ∈ (TaskClockBridge.positiveSystem M).terminalPaths tasks k)
    (i : Nat) (hi : i < k + 1) :
    FixedClockPath.listFiltration M fallback p i =
      (ClockReadiness.ready_isStoppingTime M i
        (FixedClockPath.forwardVertex fallback p i)).measurableSpace := by
  obtain ⟨v, _, hlegal⟩ :=
    ((TaskClockBridge.positiveSystem M).mem_terminalPaths_iff tasks k p).mp hp
  have hlength : p.length = k + 1 :=
    (TaskClockBridge.positiveSystem M).path_length k v
      (((TaskClockBridge.positiveSystem M).mem_paths_iff_legal k v p).mpr hlegal)
  exact listFiltration_eq_ready_sigma M fallback k v hlegal i (by simpa only [hlength] using hi)

section ActualProbability

variable [Countable V]

/-- A predetermined list entry is an actual task delay, so its law is proved by the model. -/
theorem pathWait_hasLaw (M : TaskPaths.System V) (fallback : V) (p : List V)
    (i : Nat) (hi : i < p.length) :
    HasLaw (TaskPathTail.pathWait (TaskClockBridge.delay M) p i) (expMeasure 1)
      (ExponentialClocks.clockMeasure V) := by
  rw [FixedClockPath.pathWait_eq_forward (TaskClockBridge.delay M) fallback p i hi]
  exact ClockStoppedResidual.task_delay_hasLaw M i (FixedClockPath.forwardVertex fallback p i)

/-- The actual stopped-wait independence is transferred to the equal path-history sigma-algebra. -/
theorem pathWait_indep_of_legal (M : TaskPaths.System V) (fallback : V) (k : Nat)
    (v : V) {p : List V} (hlegal : (TaskClockBridge.positiveSystem M).Legal k v p)
    (i : Nat) (hi : i < p.length) :
    Indep ((borel ℝ).comap (TaskPathTail.pathWait (TaskClockBridge.delay M) p i))
      (FixedClockPath.listFiltration M fallback p i) (ExponentialClocks.clockMeasure V) := by
  rw [FixedClockPath.pathWait_eq_forward (TaskClockBridge.delay M) fallback p i hi,
    listFiltration_eq_ready_sigma M fallback k v hlegal i hi]
  exact ClockStoppedResidual.task_delay_indep M i (FixedClockPath.forwardVertex fallback p i)

theorem terminal_pathWait_hasLaw (M : TaskPaths.System V) (fallback : V)
    (tasks : Finset V) (k : Nat) {p : List V}
    (hp : p ∈ (TaskClockBridge.positiveSystem M).terminalPaths tasks k)
    (i : Nat) (hi : i < k + 1) :
    HasLaw (TaskPathTail.pathWait (TaskClockBridge.delay M) p i) (expMeasure 1)
      (ExponentialClocks.clockMeasure V) := by
  obtain ⟨v, _, hlegal⟩ :=
    ((TaskClockBridge.positiveSystem M).mem_terminalPaths_iff tasks k p).mp hp
  have hlength : p.length = k + 1 :=
    (TaskClockBridge.positiveSystem M).path_length k v
      (((TaskClockBridge.positiveSystem M).mem_paths_iff_legal k v p).mpr hlegal)
  exact pathWait_hasLaw M fallback p i (by simpa only [hlength] using hi)

theorem terminal_pathWait_indep (M : TaskPaths.System V) (fallback : V)
    (tasks : Finset V) (k : Nat) {p : List V}
    (hp : p ∈ (TaskClockBridge.positiveSystem M).terminalPaths tasks k)
    (i : Nat) (hi : i < k + 1) :
    Indep ((borel ℝ).comap (TaskPathTail.pathWait (TaskClockBridge.delay M) p i))
      (FixedClockPath.listFiltration M fallback p i) (ExponentialClocks.clockMeasure V) := by
  obtain ⟨v, _, hlegal⟩ :=
    ((TaskClockBridge.positiveSystem M).mem_terminalPaths_iff tasks k p).mp hp
  have hlength : p.length = k + 1 :=
    (TaskClockBridge.positiveSystem M).path_length k v
      (((TaskClockBridge.positiveSystem M).mem_paths_iff_legal k v p).mpr hlegal)
  exact pathWait_indep_of_legal M fallback k v hlegal i (by simpa only [hlength] using hi)

/-- Actual fixed-path exponential integrability, with no conditional-law or prefix-integrability input. -/
theorem fixed_path_exponential_integrable (M : TaskPaths.System V) (p : Nat → V) (r : Nat)
    (hedges : FixedClockPath.Edges M p r) (θ : ℝ) (hθ : θ < 1) :
    Integrable (ConditionalMoment.pathExp θ (fun i => TaskClockBridge.delay M i (p i)) r)
      (ExponentialClocks.clockMeasure V) := by
  apply ExponentialMoment.fixed_path_integrable_of_hasLaw_indep
    (FixedClockPath.pathFiltration M p r hedges) hθ _ r
  · exact fun i hi => FixedClockPath.delay_known M p r hedges i hi
  · exact fun i _ => ClockStoppedResidual.task_delay_hasLaw M i (p i)
  · intro i hi
    rw [pathFiltration_eq_ready_sigma M p r hedges i hi]
    exact ClockStoppedResidual.task_delay_indep M i (p i)

/-- The actual fixed-path MGF is now proved without waiting-law or history-independence inputs.
This proves a fixed-path statement, rather than global independence of task delays. -/
theorem fixed_path_exponential_moment (M : TaskPaths.System V) (p : Nat → V) (r : Nat)
    (hedges : FixedClockPath.Edges M p r) (θ : ℝ) (hθ : θ < 1) :
    (∫ ω, Real.exp (θ * ConditionalMoment.prefixSum
      (fun i => TaskClockBridge.delay M i (p i)) r ω) ∂ExponentialClocks.clockMeasure V) =
        ((1 - θ)⁻¹) ^ r := by
  apply ExponentialMoment.fixed_path_moment_of_hasLaw_indep
    (FixedClockPath.pathFiltration M p r hedges) hθ _ r
  · exact fun i hi => FixedClockPath.delay_known M p r hedges i hi
  · exact fun i _ => ClockStoppedResidual.task_delay_hasLaw M i (p i)
  · intro i hi
    rw [pathFiltration_eq_ready_sigma M p r hedges i hi]
    exact ClockStoppedResidual.task_delay_indep M i (p i)

theorem path_weight_exponential_moment (M : TaskPaths.System V) (fallback : V) (k : Nat)
    (v : V) {p : List V} (hlegal : (TaskClockBridge.positiveSystem M).Legal k v p)
    (θ : ℝ) (hθ : θ < 1) :
    (∫ ω, Real.exp (θ * TaskPaths.System.weight
      (fun i u => TaskClockBridge.delay M i u ω) p) ∂ExponentialClocks.clockMeasure V) =
        ((1 - θ)⁻¹) ^ (k + 1) := by
  have h := ExponentialMoment.fixed_path_moment_of_hasLaw_indep
    (FixedClockPath.listFiltration M fallback p) hθ
    (TaskPathTail.pathWait (TaskClockBridge.delay M) p) p.length
    (fun i hi => FixedClockPath.pathWait_known_of_legal M fallback k v hlegal i hi)
    (fun i hi => pathWait_hasLaw M fallback p i hi)
    (fun i hi => pathWait_indep_of_legal M fallback k v hlegal i hi)
  have hlength : p.length = k + 1 :=
    (TaskClockBridge.positiveSystem M).path_length k v
      (((TaskClockBridge.positiveSystem M).mem_paths_iff_legal k v p).mpr hlegal)
  simp only [TaskPathTail.prefixSum_pathWait] at h
  simpa only [hlength] using h

end ActualProbability

/-- The actual square physical clock maximum has the stated tail with no probabilistic premises.
The index `k` means `k + 1` positive task layers, on a square of side `n + 2`. -/
theorem actual_square_eight_tail (n : Nat) (c : Bool) (k : Nat) (threshold : ℝ) :
    MeasurableSet {ω | (threshold : WithTop ℝ) < ClockMaximum.squareMaximum n c k ω} ∧
      (ExponentialClocks.clockMeasure (SquareTasks.Vertex n)).real
        {ω | (threshold : WithTop ℝ) < ClockMaximum.squareMaximum n c k ω} ≤
          (n + 2 : ℝ) ^ 2 * (8 : ℝ) ^ (k + 1) * Real.exp (-threshold / 2) := by
  apply ClockMaximum.actual_square_eight_tail n c k threshold
  · intro p hp i hi
    have hp' : p ∈ (TaskClockBridge.positiveSystem (SquareTasks.system n)).terminalPaths
        (SquareTasks.tasks n c k) k := by
      simpa only [TaskClockBridge.positiveSystem_square] using hp
    exact terminal_pathWait_hasLaw (SquareTasks.system n) (ClockMaximum.origin n)
      (SquareTasks.tasks n c k) k hp' i hi
  · intro p hp i hi
    have hp' : p ∈ (TaskClockBridge.positiveSystem (SquareTasks.system n)).terminalPaths
        (SquareTasks.tasks n c k) k := by
      simpa only [TaskClockBridge.positiveSystem_square] using hp
    exact terminal_pathWait_indep (SquareTasks.system n) (ClockMaximum.origin n)
      (SquareTasks.tasks n c k) k hp' i hi

end MathResearchAnalysis.ActualClockTail
