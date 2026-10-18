module

public import MathResearchAnalysis.ClockSelectedWord
public import MathResearchAnalysis.SquareDynamics

set_option autoImplicit false

/-!
# Actual checkerboard batches and selected clock dynamics

The same-color batch theorem uses the actual square rule: sites of one color
cannot read each other's writes, including their own writes. A complete task
layer therefore equals the genuine simultaneous checkerboard step.

The layer-word identity below holds for every clock sample, including samples
with repeated identities across layers. Marks are read from each actual
site/ring identity and then placed at their corresponding positive layer.
Only the chronological rearrangement needs the already proved clock-regularity
event and the condition that the actual selected maximum is at most the bound.
No censoring inequality or independence of the two checkerboard chains is claimed.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.SquareBatch

open SquareTasks

/-- Sequentially update a site list using its fixed per-site marks. -/
def batch {n : ℕ} (marks : SquareDynamics.Mark n) (sites : List (Vertex n))
    (initial : SquareSpin.Config n) : SquareSpin.Config n :=
  EventTrace.execute (fun v f => SquareSpin.cellUpdate f v (marks v)) sites initial

/-- Update exactly the listed sites, with every rule reading the same initial state. -/
def parallel {n : ℕ} (marks : SquareDynamics.Mark n) (sites : List (Vertex n))
    (initial : SquareSpin.Config n) : SquareSpin.Config n :=
  fun v => if v ∈ sites then SquareSpin.rule initial v (marks v) else initial v

@[simp] theorem batch_nil {n : ℕ} (marks : SquareDynamics.Mark n)
    (initial : SquareSpin.Config n) : batch marks [] initial = initial := rfl

theorem batch_cons {n : ℕ} (marks : SquareDynamics.Mark n) (v : Vertex n)
    (rest : List (Vertex n)) (initial : SquareSpin.Config n) :
    batch marks (v :: rest) initial =
      batch marks rest (SquareSpin.cellUpdate initial v (marks v)) := rfl

private theorem not_adjacent_of_colour_eq {n : ℕ} {v u : Vertex n}
    (hc : colour v = colour u) : ¬ Adjacent v u := by
  intro hadj
  have hf := adjacent_colour_flip hadj
  rw [← hc] at hf
  cases hv : colour v <;> simp [hv] at hf

/-- Same-color sequential writes equal simultaneous reads of the original state.
Repeated sites are harmless here because their per-site mark is fixed. -/
theorem batch_eq_parallel {n : ℕ} (marks : SquareDynamics.Mark n)
    (sites : List (Vertex n)) (c : Bool)
    (hc : ∀ v ∈ sites, colour v = c) (initial : SquareSpin.Config n) :
    batch marks sites initial = parallel marks sites initial := by
  induction sites generalizing initial with
  | nil => funext v; simp [batch, parallel, EventTrace.execute]
  | cons a rest ih =>
    have hca : colour a = c := hc a (by simp)
    have hcrest : ∀ v ∈ rest, colour v = c :=
      fun v hv => hc v (List.mem_cons_of_mem a hv)
    rw [batch_cons, ih hcrest]
    funext v
    by_cases hv : v ∈ rest
    · have hnon : ¬ Adjacent v a :=
        not_adjacent_of_colour_eq ((hcrest v hv).trans hca.symm)
      simp only [parallel, List.mem_cons, hv, or_true, ite_true]
      exact SquareSpin.rule_eq_after_nonadjacent_update initial v a (marks v) (marks a) hnon
    · by_cases heq : v = a
      · subst v
        simp [parallel, hv, SquareSpin.cellUpdate_same]
      · simp [parallel, hv, heq, SquareSpin.cellUpdate_other initial a v (marks a) heq]

/-- A full task layer is the actual checkerboard step at its positive-slot color. -/
theorem taskBatch_eq_checkerboard (n : ℕ) (c : Bool) (j : ℕ)
    (marks : SquareDynamics.Mark n) (initial : SquareSpin.Config n) :
    batch marks (tasks n c j).toList initial =
      SquareSpin.checkerboardStep initial (BipartiteDynamics.activeColour (!c) (j + 1)) marks := by
  have hmem (v : Vertex n) : v ∈ (tasks n c j).toList ↔
      colour v = BipartiteDynamics.activeColour (!c) (j + 1) := by
    rw [Finset.mem_toList]
    simpa only [Bool.not_not] using SquareDynamics.mem_tasks_positive_slot n (!c) j v
  rw [batch_eq_parallel marks _ _ (fun v hv => (hmem v).mp hv)]
  funext v
  simp only [parallel, SquareSpin.checkerboardStep, hmem]

/-- Marks selected by the actual task's site/ring event identity at positive layer `j`. -/
def chosenMarks {n : ℕ} (ω : ClockSelectedWord.Sample n) (η : SquareSpin.Event n → Bool) :
    SquareDynamics.Marks n := fun j v => η (ClockEventOrder.eventId n j v ω)

theorem execute_layer_eq_batch (n : ℕ) (ω : ClockSelectedWord.Sample n)
    (η : SquareSpin.Event n → Bool) (j : ℕ) (sites : List (Vertex n))
    (initial : SquareSpin.Config n) :
    MarkedEventTrace.execute η (sites.map fun v => ClockEventOrder.eventId n j v ω) initial =
      batch (chosenMarks ω η j) sites initial := by
  unfold MarkedEventTrace.execute batch EventTrace.execute
  rw [List.foldl_map]
  rfl

theorem layerTasks_zero (n : ℕ) (c : Bool) :
    ClockSelectedWord.layerTasks n c 0 = (tasks n c 0).toList.map fun v => (1, v) := by
  simp [ClockSelectedWord.layerTasks]

theorem layerTasks_succ (n : ℕ) (c : Bool) (k : ℕ) :
    ClockSelectedWord.layerTasks n c (k + 1) = ClockSelectedWord.layerTasks n c k ++
      (tasks n c (k + 1)).toList.map (fun v => (k + 2, v)) := by
  unfold ClockSelectedWord.layerTasks
  rw [List.range_succ, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem layerWord_zero (n : ℕ) (c : Bool) (ω : ClockSelectedWord.Sample n) :
    ClockSelectedWord.layerWord n c 0 ω =
      (tasks n c 0).toList.map fun v => ClockEventOrder.eventId n 1 v ω := by
  simp only [ClockSelectedWord.layerWord, layerTasks_zero, List.map_map, Function.comp_def]

theorem layerWord_succ (n : ℕ) (c : Bool) (k : ℕ) (ω : ClockSelectedWord.Sample n) :
    ClockSelectedWord.layerWord n c (k + 1) ω = ClockSelectedWord.layerWord n c k ω ++
      (tasks n c (k + 1)).toList.map (fun v => ClockEventOrder.eventId n (k + 2) v ω) := by
  simp only [ClockSelectedWord.layerWord, layerTasks_succ, List.map_append, List.map_map,
    Function.comp_def]

/-- Every layer word executes precisely the actual common-mark alternating trajectory.
This identity requires no regularity or distinct-event assumption. -/
theorem execute_layerWord_eq_alternating (n : ℕ) (c : Bool) (k : ℕ)
    (ω : ClockSelectedWord.Sample n) (η : SquareSpin.Event n → Bool)
    (initial : SquareSpin.Config n) :
    MarkedEventTrace.execute η (ClockSelectedWord.layerWord n c k ω) initial =
      SquareDynamics.alternating (chosenMarks ω η) initial (!c) (k + 1) := by
  induction k with
  | zero =>
    rw [layerWord_zero, execute_layer_eq_batch, taskBatch_eq_checkerboard,
      SquareDynamics.alternating_succ, SquareDynamics.alternating_zero]
  | succ k ih =>
    rw [layerWord_succ]
    change EventTrace.execute (SquareSpin.updateEvent η) (_ ++ _) initial = _
    rw [EventTrace.execute_append]
    change MarkedEventTrace.execute η
      ((tasks n c (k + 1)).toList.map fun v => ClockEventOrder.eventId n (k + 2) v ω)
      (MarkedEventTrace.execute η (ClockSelectedWord.layerWord n c k ω) initial) = _
    rw [ih, execute_layer_eq_batch, taskBatch_eq_checkerboard]
    exact (SquareDynamics.alternating_succ (chosenMarks ω η) initial (!c) (k + 1)).symm

theorem execute_selectedChrono_eq_alternating (n : ℕ) (c : Bool) (k : ℕ)
    (ω : ClockSelectedWord.Sample n) (hω : ClockSelectedWord.Regular n ω) (t : ℝ)
    (hmax : ClockMaximum.squareMaximum n c k ω ≤ (t : WithTop ℝ))
    (η : SquareSpin.Event n → Bool) (initial : SquareSpin.Config n) :
    MarkedEventTrace.execute η (ClockSelectedWord.selectedChrono n c k ω t) initial =
      SquareDynamics.alternating (chosenMarks ω η) initial (!c) (k + 1) :=
  (ClockSelectedWord.execute_selectedChrono_eq_layerWord n c k ω hω t hmax η initial).trans
    (execute_layerWord_eq_alternating n c k ω η initial)

/-- The actual chronological deletion word is the actual alternating trajectory almost surely. -/
theorem execute_selectedChrono_eq_alternating_ae (n : ℕ) (c : Bool) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (Vertex n),
      ∀ (k : ℕ) (t : ℝ), ClockMaximum.squareMaximum n c k ω ≤ (t : WithTop ℝ) →
        ∀ (η : SquareSpin.Event n → Bool) (initial : SquareSpin.Config n),
          MarkedEventTrace.execute η (ClockSelectedWord.selectedChrono n c k ω t) initial =
            SquareDynamics.alternating (chosenMarks ω η) initial (!c) (k + 1) := by
  filter_upwards [ClockSelectedWord.regular_ae n] with ω hω
  exact fun k t hmax η initial => execute_selectedChrono_eq_alternating n c k ω hω t hmax η initial

end MathResearchAnalysis.SquareBatch
