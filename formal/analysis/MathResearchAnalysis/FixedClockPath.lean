module

public import MathResearchAnalysis.TaskClockBridge
public import MathResearchAnalysis.TaskPathTail

set_option autoImplicit false

/-!
# Actual stopping sigma-algebras along a predetermined finite clock path

The chronological path is deterministic. Its readiness and completion use the
actual clock recurrence on the required finite prefix. Afterwards both are
frozen at the last completion, rather than reset to zero. This gives a genuine
infinite filtration of stopping sigma-algebras and proves the known-past input
for actual delays. No task stopping-time or known-past assumption is supplied.
The conditional exponential moment and its integrability remain explicit inputs.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.FixedClockPath

variable {V : Type*} [DecidableEq V]

/-- Exactly the predecessor condition needed on the finite chronological path. -/
def Edges (M : TaskPaths.System V) (p : Nat → V) (r : Nat) : Prop :=
  ∀ i, i + 1 < r → p i ∈ M.predecessors (i + 1) (p (i + 1))

def finalCompletion (M : TaskPaths.System V) (p : Nat → V) (r : Nat) :
    ExponentialClocks.Sample V → WithTop ℝ :=
  ClockReadiness.completion M r (p (r - 1))

def pathReady (M : TaskPaths.System V) (p : Nat → V) (r i : Nat) :
    ExponentialClocks.Sample V → WithTop ℝ :=
  if i < r then ClockReadiness.ready M i (p i) else finalCompletion M p r

def pathComplete (M : TaskPaths.System V) (p : Nat → V) (r i : Nat) :
    ExponentialClocks.Sample V → WithTop ℝ :=
  if i < r then ClockReadiness.completion M (i + 1) (p i) else finalCompletion M p r

theorem pathReady_isStoppingTime (M : TaskPaths.System V) (p : Nat → V)
    (r i : Nat) : IsStoppingTime (ArrivalFiltration.clockHistory V) (pathReady M p r i) := by
  by_cases hi : i < r
  · simp only [pathReady, ite_eq_left hi]
    exact ClockReadiness.ready_isStoppingTime M i (p i)
  · simp only [pathReady, ite_eq_right hi, finalCompletion]
    exact ClockReadiness.completion_isStoppingTime M r (p (r - 1))

theorem pathComplete_isStoppingTime (M : TaskPaths.System V) (p : Nat → V)
    (r i : Nat) : IsStoppingTime (ArrivalFiltration.clockHistory V) (pathComplete M p r i) := by
  by_cases hi : i < r
  · simp only [pathComplete, ite_eq_left hi]
    exact ClockReadiness.completion_isStoppingTime M (i + 1) (p i)
  · simp only [pathComplete, ite_eq_right hi, finalCompletion]
    exact ClockReadiness.completion_isStoppingTime M r (p (r - 1))

theorem ready_le_complete (M : TaskPaths.System V) (p : Nat → V) (r i : Nat)
    (ω : ExponentialClocks.Sample V) : pathReady M p r i ω ≤ pathComplete M p r i ω := by
  by_cases hi : i < r
  · simp only [pathReady, pathComplete, ite_eq_left hi]
    exact ClockReadiness.ready_le_completion M i (p i) ω
  · simp only [pathReady, pathComplete, ite_eq_right hi, le_refl]

theorem complete_le_next_ready (M : TaskPaths.System V) (p : Nat → V) (r : Nat)
    (hedges : Edges M p r) (i : Nat) (ω : ExponentialClocks.Sample V) :
    pathComplete M p r i ω ≤ pathReady M p r (i + 1) ω := by
  by_cases hinext : i + 1 < r
  · have hi : i < r := by omega
    simp only [pathComplete, pathReady, ite_eq_left hi, ite_eq_left hinext]
    exact ClockReadiness.predecessor_completion_le_ready M (i + 1) (p (i + 1))
      (p i) (hedges i hinext) ω
  · by_cases hi : i < r
    · have hir : i + 1 = r := by omega
      have hilast : i = r - 1 := by omega
      simp only [pathComplete, pathReady, ite_eq_left hi, ite_eq_right hinext, finalCompletion]
      rw [hir, hilast]
    · simp only [pathComplete, pathReady, ite_eq_right hi, ite_eq_right hinext, le_refl]

/-- Every sigma-algebra is an actual stopping sigma-algebra, including after the prefix. -/
def pathFiltration (M : TaskPaths.System V) (p : Nat → V) (r : Nat)
    (hedges : Edges M p r) : Filtration Nat (inferInstance : MeasurableSpace
      (ExponentialClocks.Sample V)) :=
  ExtendedStoppingPath.readinessFiltration (ArrivalFiltration.clockHistory V)
    (pathReady M p r) (pathReady_isStoppingTime M p r)
    (ExtendedStoppingPath.readiness_order (pathReady M p r) (pathComplete M p r)
      (ready_le_complete M p r) (complete_le_next_ready M p r hedges))

theorem pathWaiting_eq_delay (M : TaskPaths.System V) (p : Nat → V) (r i : Nat)
    (hi : i < r) : ExtendedStoppingPath.waiting (pathReady M p r)
      (pathComplete M p r) i = TaskClockBridge.delay M i (p i) := by
  funext ω
  simp only [ExtendedStoppingPath.waiting, pathReady, pathComplete, ite_eq_left hi,
    TaskClockBridge.delay, TaskClockBridge.realCompletion, TaskClockBridge.realReady]

/-- Known-past measurability is a theorem for the actual constructed delays. -/
theorem delay_known (M : TaskPaths.System V) (p : Nat → V) (r : Nat)
    (hedges : Edges M p r) (i : Nat) (hi : i < r) :
    StronglyMeasurable[pathFiltration M p r hedges (i + 1)]
      (TaskClockBridge.delay M i (p i)) := by
  have h := ExtendedStoppingPath.waiting_known (ArrivalFiltration.clockHistory V)
    (pathReady M p r) (pathComplete M p r)
    (pathReady_isStoppingTime M p r) (pathComplete_isStoppingTime M p r)
    (ready_le_complete M p r) (complete_le_next_ready M p r hedges) i
  rw [pathWaiting_eq_delay M p r i hi] at h
  exact h

theorem path_times_finite_ae [Countable V] (M : TaskPaths.System V) (p : Nat → V)
    (r : Nat) : ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ i,
      pathReady M p r i ω ≠ ⊤ ∧ pathComplete M p r i ω ≠ ⊤ := by
  filter_upwards [ClockReadiness.all_times_finite_ae M] with ω hω
  intro i
  by_cases hi : i < r
  · simp only [pathReady, pathComplete, ite_eq_left hi]
    exact ⟨hω.2 i (p i), hω.1 (i + 1) (p i)⟩
  · simp only [pathReady, pathComplete, ite_eq_right hi, finalCompletion]
    exact ⟨hω.1 r (p (r - 1)), hω.1 r (p (r - 1))⟩

/-- The fixed-path moment now has no known-past or stopping-time inputs.
The single-step conditional moment and exponential integrability remain inputs. -/
theorem fixed_path_moment (M : TaskPaths.System V) (p : Nat → V) (r : Nat)
    (hedges : Edges M p r) (θ constant : ℝ)
    (hwaitInt : ∀ i < r, Integrable (fun ω => Real.exp
      (θ * TaskClockBridge.delay M i (p i) ω)) (ExponentialClocks.clockMeasure V))
    (hconditional : ∀ i < r, (ExponentialClocks.clockMeasure V)[(fun ω => Real.exp
      (θ * TaskClockBridge.delay M i (p i) ω)) | pathFiltration M p r hedges i]
        =ᵐ[ExponentialClocks.clockMeasure V] fun _ => constant) :
    Integrable (ConditionalMoment.pathExp θ (fun i => TaskClockBridge.delay M i (p i)) r)
      (ExponentialClocks.clockMeasure V) ∧
      (∫ ω, Real.exp (θ * ConditionalMoment.prefixSum
        (fun i => TaskClockBridge.delay M i (p i)) r ω)
        ∂ExponentialClocks.clockMeasure V) = constant ^ r := by
  have hknown := fun i hi => delay_known M p r hedges i hi
  exact ⟨NonnegativeMoment.fixed_path_exponential_integrable (pathFiltration M p r hedges)
      θ constant _ r hknown hwaitInt hconditional,
    NonnegativeMoment.fixed_path_exponential_moment (pathFiltration M p r hedges)
      θ constant _ r hknown hwaitInt hconditional⟩

/-- Total deterministic chronological indexing of a reversed path list. -/
def forwardVertex (fallback : V) : List V → Nat → V
  | [], _ => fallback
  | v :: q, i => if i = q.length then v else forwardVertex fallback q i

omit [DecidableEq V] in
theorem pathWait_eq_forward (delay : Nat → V → ExponentialClocks.Sample V → ℝ)
    (fallback : V) (q : List V) (i : Nat) (hi : i < q.length) :
    TaskPathTail.pathWait delay q i = delay i (forwardVertex fallback q i) := by
  induction q with
  | nil => simp at hi
  | cons v q ih =>
    by_cases hitop : i = q.length
    · simp only [TaskPathTail.pathWait, forwardVertex, ite_eq_left hitop]
    · have hiq : i < q.length := by
        simp only [List.length_cons] at hi
        omega
      simp only [TaskPathTail.pathWait, forwardVertex, ite_eq_right hitop]
      exact ih hiq

theorem forwardVertex_last (M : TaskPaths.System V) (fallback : V) (k : Nat)
    (v : V) {q : List V} (hlegal : M.Legal k v q) :
    forwardVertex fallback q k = v := by
  cases k with
  | zero =>
    change q = [v] at hlegal
    subst q
    simp [forwardVertex]
  | succ k =>
    obtain ⟨u, _, q', hq, rfl⟩ := hlegal
    have hlength : q'.length = k + 1 :=
      M.path_length k u ((M.mem_paths_iff_legal k u q').mpr hq)
    simp [forwardVertex, hlength]

/-- A legal reversed max-plus path supplies exactly the actual clock predecessor edges. -/
theorem legal_edges (M : TaskPaths.System V) (fallback : V) (k : Nat)
    (v : V) {q : List V} (hlegal : (TaskClockBridge.positiveSystem M).Legal k v q) :
    Edges M (forwardVertex fallback q) q.length := by
  induction k generalizing v q with
  | zero =>
    change q = [v] at hlegal
    subst q
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    omega
  | succ k ih =>
    obtain ⟨u, hu, q', hq, rfl⟩ := hlegal
    have hlength : q'.length = k + 1 :=
      (TaskClockBridge.positiveSystem M).path_length k u
        (((TaskClockBridge.positiveSystem M).mem_paths_iff_legal k u q').mpr hq)
    intro i hi
    by_cases hitop : i + 1 = q'.length
    · have hik : i = k := by omega
      have hine : i ≠ q'.length := by omega
      simp only [forwardVertex, ite_eq_right hine, ite_eq_left hitop]
      rw [hik, forwardVertex_last (TaskClockBridge.positiveSystem M) fallback k u hq]
      exact hu
    · have hiq : i + 1 < q'.length := by
        simp only [List.length_cons] at hi
        omega
      have hine : i ≠ q'.length := by omega
      simp only [forwardVertex, ite_eq_right hine, ite_eq_right hitop]
      exact ih u hq i hiq

/-- Illegal lists receive a genuine zero-prefix stopping filtration; this makes
the path-indexed family total without adding any assumption for legal paths. -/
def listFiltration (M : TaskPaths.System V) (fallback : V) (q : List V) :
    Filtration Nat (inferInstance : MeasurableSpace (ExponentialClocks.Sample V)) := by
  classical
  exact if hedge : Edges M (forwardVertex fallback q) q.length then
    pathFiltration M (forwardVertex fallback q) q.length hedge
  else pathFiltration M (fun _ => fallback) 0 (fun i hi => by omega)

theorem listFiltration_of_edges (M : TaskPaths.System V) (fallback : V) (q : List V)
    (hedge : Edges M (forwardVertex fallback q) q.length) :
    listFiltration M fallback q = pathFiltration M (forwardVertex fallback q) q.length hedge := by
  simp only [listFiltration, dite_eq_left hedge]

/-- The existing reversed-list wait is known in the constructed path filtration. -/
theorem pathWait_known_of_legal (M : TaskPaths.System V) (fallback : V) (k : Nat)
    (v : V) {q : List V} (hlegal : (TaskClockBridge.positiveSystem M).Legal k v q)
    (i : Nat) (hi : i < q.length) :
    StronglyMeasurable[listFiltration M fallback q (i + 1)]
      (TaskPathTail.pathWait (TaskClockBridge.delay M) q i) := by
  have hedge := legal_edges M fallback k v hlegal
  rw [pathWait_eq_forward (TaskClockBridge.delay M) fallback q i hi]
  rw [listFiltration_of_edges M fallback q hedge]
  exact delay_known M (forwardVertex fallback q) q.length hedge i hi

theorem terminal_pathWait_known (M : TaskPaths.System V) (fallback : V)
    (tasks : Finset V) (k : Nat) {q : List V}
    (hq : q ∈ (TaskClockBridge.positiveSystem M).terminalPaths tasks k)
    (i : Nat) (hi : i < k + 1) :
    StronglyMeasurable[listFiltration M fallback q (i + 1)]
      (TaskPathTail.pathWait (TaskClockBridge.delay M) q i) := by
  obtain ⟨v, _, hlegal⟩ :=
    ((TaskClockBridge.positiveSystem M).mem_terminalPaths_iff tasks k q).mp hq
  have hlength : q.length = k + 1 :=
    (TaskClockBridge.positiveSystem M).path_length k v
      (((TaskClockBridge.positiveSystem M).mem_paths_iff_legal k v q).mpr hlegal)
  exact pathWait_known_of_legal M fallback k v hlegal i (by simpa only [hlength] using hi)

/-- The actual clock delay tail interface has no known-past measurability input. -/
theorem terminal_degree_half_tail (M : TaskPaths.System V) (fallback : V)
    (tasks : Finset V) (ht : tasks.Nonempty) (d k : Nat)
    (degree : ∀ j v, (M.predecessors (j + 1) v).card ≤ d) (threshold : ℝ)
    (hwaitInt : ∀ q ∈ (TaskClockBridge.positiveSystem M).terminalPaths tasks k,
      ∀ i < k + 1, Integrable (fun ω => Real.exp ((1 / 2 : ℝ) *
        TaskPathTail.pathWait (TaskClockBridge.delay M) q i ω)) (ExponentialClocks.clockMeasure V))
    (hconditional : ∀ q ∈ (TaskClockBridge.positiveSystem M).terminalPaths tasks k,
      ∀ i < k + 1, (ExponentialClocks.clockMeasure V)[(fun ω => Real.exp ((1 / 2 : ℝ) *
        TaskPathTail.pathWait (TaskClockBridge.delay M) q i ω)) | listFiltration M fallback q i]
          =ᵐ[ExponentialClocks.clockMeasure V] fun _ => 2) :
    MeasurableSet {ω | threshold < (TaskClockBridge.positiveSystem M).terminalMaximum tasks ht
        (fun i v => TaskClockBridge.delay M i v ω) k} ∧
      (ExponentialClocks.clockMeasure V).real {ω | threshold <
        (TaskClockBridge.positiveSystem M).terminalMaximum tasks ht
          (fun i v => TaskClockBridge.delay M i v ω) k} ≤
        (tasks.card : ℝ) * (d : ℝ) ^ k * (2 : ℝ) ^ (k + 1) *
          Real.exp (-threshold / 2) :=
  TaskPathTail.terminal_degree_half_tail (TaskClockBridge.positiveSystem M) tasks ht
    (TaskClockBridge.delay M) (listFiltration M fallback) d k degree threshold
    (fun _q hq i hi => terminal_pathWait_known M fallback tasks k hq i hi)
    hwaitInt hconditional

/-- Actual nonnegative delays and predetermined path sigma-algebras discharge both
of the structural inputs in the previous generic prefix-maximum tail theorem. -/
theorem prefix_degree_half_tail (M : TaskPaths.System V) (fallback : V)
    (tasks : Nat → Finset V) (ht : ∀ j, (tasks j).Nonempty)
    (successors : ∀ j u, u ∈ tasks j →
      ∃ v ∈ tasks (j + 1), u ∈ M.predecessors (j + 1) v)
    (d k : Nat) (degree : ∀ j v, (M.predecessors (j + 1) v).card ≤ d) (threshold : ℝ)
    (hwaitInt : ∀ q ∈ (TaskClockBridge.positiveSystem M).terminalPaths (tasks k) k,
      ∀ i < k + 1, Integrable (fun ω => Real.exp ((1 / 2 : ℝ) *
        TaskPathTail.pathWait (TaskClockBridge.delay M) q i ω)) (ExponentialClocks.clockMeasure V))
    (hconditional : ∀ q ∈ (TaskClockBridge.positiveSystem M).terminalPaths (tasks k) k,
      ∀ i < k + 1, (ExponentialClocks.clockMeasure V)[(fun ω => Real.exp ((1 / 2 : ℝ) *
        TaskPathTail.pathWait (TaskClockBridge.delay M) q i ω)) | listFiltration M fallback q i]
          =ᵐ[ExponentialClocks.clockMeasure V] fun _ => 2) :
    MeasurableSet {ω | threshold < (TaskClockBridge.positiveSystem M).prefixMaximum tasks ht
        (fun i v => TaskClockBridge.delay M i v ω) k} ∧
      (ExponentialClocks.clockMeasure V).real {ω | threshold <
        (TaskClockBridge.positiveSystem M).prefixMaximum tasks ht
          (fun i v => TaskClockBridge.delay M i v ω) k} ≤
        ((tasks k).card : ℝ) * (d : ℝ) ^ k * (2 : ℝ) ^ (k + 1) *
          Real.exp (-threshold / 2) :=
  TaskPathTail.prefix_degree_half_tail (TaskClockBridge.positiveSystem M) tasks ht
    (TaskClockBridge.delay M) (listFiltration M fallback)
    (fun ω j v => TaskClockBridge.delay_nonnegative M j v ω) successors d k degree threshold
    (fun _q hq i hi => terminal_pathWait_known M fallback (tasks k) k hq i hi)
    hwaitInt hconditional

section FiniteVertices

variable [Fintype V] [Nonempty V]

omit [Nonempty V] in
theorem allPaths_pathWait_known (M : TaskPaths.System V) (fallback : V)
    (k : Nat) {q : List V} (hq : q ∈ (TaskClockBridge.positiveSystem M).allPaths k)
    (i : Nat) (hi : i < k + 1) :
    StronglyMeasurable[listFiltration M fallback q (i + 1)]
      (TaskPathTail.pathWait (TaskClockBridge.delay M) q i) := by
  obtain ⟨v, hlegal⟩ := ((TaskClockBridge.positiveSystem M).mem_allPaths_iff k q).mp hq
  have hlength := TaskPathTail.allPaths_length (TaskClockBridge.positiveSystem M) k hq
  exact pathWait_known_of_legal M fallback k v hlegal i (by simpa only [hlength] using hi)

theorem allPaths_degree_half_tail (M : TaskPaths.System V) (fallback : V) (d k : Nat)
    (degree : ∀ j v, (M.predecessors (j + 1) v).card ≤ d) (threshold : ℝ)
    (hwaitInt : ∀ q ∈ (TaskClockBridge.positiveSystem M).allPaths k,
      ∀ i < k + 1, Integrable (fun ω => Real.exp ((1 / 2 : ℝ) *
        TaskPathTail.pathWait (TaskClockBridge.delay M) q i ω)) (ExponentialClocks.clockMeasure V))
    (hconditional : ∀ q ∈ (TaskClockBridge.positiveSystem M).allPaths k,
      ∀ i < k + 1, (ExponentialClocks.clockMeasure V)[(fun ω => Real.exp ((1 / 2 : ℝ) *
        TaskPathTail.pathWait (TaskClockBridge.delay M) q i ω)) | listFiltration M fallback q i]
          =ᵐ[ExponentialClocks.clockMeasure V] fun _ => 2) :
    MeasurableSet {ω | threshold < (TaskClockBridge.positiveSystem M).layerMaximum
        (fun i v => TaskClockBridge.delay M i v ω) k} ∧
      (ExponentialClocks.clockMeasure V).real {ω | threshold <
        (TaskClockBridge.positiveSystem M).layerMaximum
          (fun i v => TaskClockBridge.delay M i v ω) k} ≤
        (Fintype.card V : ℝ) * (d : ℝ) ^ k * (2 : ℝ) ^ (k + 1) *
          Real.exp (-threshold / 2) :=
  TaskPathTail.degree_half_tail (TaskClockBridge.positiveSystem M)
    (TaskClockBridge.delay M) (listFiltration M fallback) d k degree threshold
    (fun _q hq i hi => allPaths_pathWait_known M fallback k hq i hi)
    hwaitInt hconditional

end FiniteVertices

end MathResearchAnalysis.FixedClockPath
