module

public import MathResearchAnalysis.ExtendedNextRing
public import MathResearchAnalysis.ArrivalFiltration
public import MathResearchAnalysis.SquareTasks

set_option autoImplicit false

/-!
# Constructed clock readiness and completion times

The zero layer is initialized at time zero. Each positive task waits until
the maximum of its actual finite predecessor completions, and then takes
the strict next arrival of its site's constructed exponential stream.

All times take values in `WithTop ℝ`. Stopping-time properties, nonnegativity,
and almost-sure finiteness are conclusions of the construction. Finiteness
uses the proved nonexplosion/cofinality of the actual clock streams, not a
finiteness assumption about tasks. No waiting-time law or strong Markov
property is established in this module.

`completion M (k + 1)` is the `k`th positive layer of `TaskPaths`; its
readiness is `ready M k`. For layer-dependent predecessor sets the matching
positive-layer task system must have predecessors `k v := M.predecessors (k + 1) v`:
the edge from positive layer `k` to positive layer `k + 1` uses that set. The
concrete square's predecessor set does not depend on its layer.
-/

public noncomputable section

open MeasureTheory Set Filter

namespace MathResearchAnalysis.ClockReadiness

variable {Ω α : Type*} {mΩ : MeasurableSpace Ω}

/-- An actual nonempty finite maximum of stopping times is a stopping time. -/
theorem finset_sup'_isStoppingTime (clocks : Filtration ℝ mΩ)
    (s : Finset α) (hs : s.Nonempty) (time : α → Ω → WithTop ℝ)
    (hstop : ∀ a ∈ s, IsStoppingTime clocks (time a)) :
    IsStoppingTime clocks (fun ω => s.sup' hs (fun a => time a ω)) := by
  intro t
  have heq : {ω | s.sup' hs (fun a => time a ω) ≤ (t : WithTop ℝ)} =
      ⋂ a : {a // a ∈ s}, {ω | time a.val ω ≤ (t : WithTop ℝ)} := by
    ext ω
    simp [Finset.sup'_le_iff]
  rw [heq]
  exact MeasurableSet.iInter (fun a => hstop a.val a.property t)

theorem finset_sup'_ne_top (s : Finset α) (hs : s.Nonempty)
    (time : α → WithTop ℝ) (hfinite : ∀ a ∈ s, time a ≠ ⊤) :
    s.sup' hs time ≠ ⊤ := by
  obtain ⟨a, ha, heq⟩ := Finset.exists_mem_eq_sup' hs time
  rw [heq]
  exact hfinite a ha

variable {V : Type*} [DecidableEq V]

/-- The actual extended completion recurrence, including its zero initialization. -/
@[expose] def completion (M : TaskPaths.System V) :
    ℕ → V → ExponentialClocks.Sample V → WithTop ℝ
  | 0, _, _ => 0
  | j + 1, v, ω => ExtendedNextRing.after (ArrivalFiltration.chronologicalArrival v)
      (fun η => (M.predecessors j v).sup' (M.nonempty j v)
        (fun u => completion M j u η)) ω

/-- Readiness for positive layer `j + 1`, determined by previous actual completions. -/
@[expose] def ready (M : TaskPaths.System V) (j : ℕ) (v : V)
    (ω : ExponentialClocks.Sample V) : WithTop ℝ :=
  (M.predecessors j v).sup' (M.nonempty j v) (fun u => completion M j u ω)

theorem completion_zero (M : TaskPaths.System V) (v : V)
    (ω : ExponentialClocks.Sample V) : completion M 0 v ω = 0 := rfl

theorem completion_succ (M : TaskPaths.System V) (j : ℕ) (v : V)
    (ω : ExponentialClocks.Sample V) :
    completion M (j + 1) v ω =
      ExtendedNextRing.after (ArrivalFiltration.chronologicalArrival v) (ready M j v) ω := rfl

theorem ready_zero (M : TaskPaths.System V) (v : V)
    (ω : ExponentialClocks.Sample V) : ready M 0 v ω = 0 := by
  unfold ready
  simp only [completion_zero, Finset.sup'_const]

theorem completion_isStoppingTime (M : TaskPaths.System V) (j : ℕ) (v : V) :
    IsStoppingTime (ArrivalFiltration.clockHistory V) (completion M j v) := by
  induction j generalizing v with
  | zero => exact isStoppingTime_const (ArrivalFiltration.clockHistory V) (0 : ℝ)
  | succ j ih =>
    apply ExtendedNextRing.after_isStoppingTime (ArrivalFiltration.clockHistory V)
      (ArrivalFiltration.chronologicalArrival v) (ready M j v)
      (ArrivalFiltration.chronologicalArrival_monotone v)
    · exact finset_sup'_isStoppingTime (ArrivalFiltration.clockHistory V)
        (M.predecessors j v) (M.nonempty j v) (fun u => completion M j u)
        (fun u _ => ih u)
    · exact ArrivalFiltration.clock_arrival_isStoppingTime v

theorem ready_isStoppingTime (M : TaskPaths.System V) (j : ℕ) (v : V) :
    IsStoppingTime (ArrivalFiltration.clockHistory V) (ready M j v) :=
  finset_sup'_isStoppingTime (ArrivalFiltration.clockHistory V)
    (M.predecessors j v) (M.nonempty j v) (fun u => completion M j u)
    (fun u _ => completion_isStoppingTime M j u)

theorem ready_le_completion (M : TaskPaths.System V) (j : ℕ) (v : V)
    (ω : ExponentialClocks.Sample V) : ready M j v ω ≤ completion M (j + 1) v ω :=
  ExtendedNextRing.ready_le_after (ArrivalFiltration.chronologicalArrival v) (ready M j v) ω

theorem predecessor_completion_le_ready (M : TaskPaths.System V) (j : ℕ) (v u : V)
    (hu : u ∈ M.predecessors j v) (ω : ExponentialClocks.Sample V) :
    completion M j u ω ≤ ready M j v ω :=
  Finset.le_sup' (fun u => completion M j u ω) hu

theorem predecessor_completion_le (M : TaskPaths.System V) (j : ℕ) (v u : V)
    (hu : u ∈ M.predecessors j v) (ω : ExponentialClocks.Sample V) :
    completion M j u ω ≤ completion M (j + 1) v ω :=
  (predecessor_completion_le_ready M j v u hu ω).trans (ready_le_completion M j v ω)

theorem completion_nonnegative (M : TaskPaths.System V) (j : ℕ) (v : V)
    (ω : ExponentialClocks.Sample V) : 0 ≤ completion M j v ω := by
  induction j generalizing v with
  | zero => exact le_rfl
  | succ j ih =>
    obtain ⟨u, hu⟩ := M.nonempty j v
    exact ((ih u).trans (predecessor_completion_le_ready M j v u hu ω)).trans
      (ready_le_completion M j v ω)

theorem ready_nonnegative (M : TaskPaths.System V) (j : ℕ) (v : V)
    (ω : ExponentialClocks.Sample V) : 0 ≤ ready M j v ω := by
  obtain ⟨u, hu⟩ := M.nonempty j v
  exact (completion_nonnegative M j u ω).trans
    (predecessor_completion_le_ready M j v u hu ω)

omit [DecidableEq V] in
/-- The actual clock construction provides all real thresholds on one full-measure set. -/
theorem arrival_cofinal_ae [Countable V] (v : V) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ r : ℝ,
      ∃ k, r < ArrivalFiltration.chronologicalArrival v k ω := by
  filter_upwards [ArrivalFiltration.chronologicalArrival_unbounded_ae (V := V)] with ω hω
  intro r
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_atTop.mp (hω v)) (r + 1))
  exact ⟨N, lt_of_lt_of_le (by linarith) (hN N le_rfl)⟩

/-- Finiteness is proved by actual layer recursion; no completion finiteness is an input. -/
theorem completion_layer_finite_ae [Countable V] (M : TaskPaths.System V) (j : ℕ) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ v, completion M j v ω ≠ ⊤ := by
  induction j with
  | zero => exact ae_of_all _ (fun ω v => WithTop.coe_ne_top)
  | succ j ih =>
    rw [ae_all_iff]
    intro v
    have hr : ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ready M j v ω ≠ ⊤ :=
      ih.mono (fun ω hω => finset_sup'_ne_top (M.predecessors j v) (M.nonempty j v)
        (fun u => completion M j u ω) (fun u _ => hω u))
    exact ExtendedNextRing.after_ae_finite (ArrivalFiltration.chronologicalArrival v)
      (ready M j v) hr (arrival_cofinal_ae v)

theorem ready_layer_finite_ae [Countable V] (M : TaskPaths.System V) (j : ℕ) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ v, ready M j v ω ≠ ⊤ :=
  (completion_layer_finite_ae M j).mono (fun ω hω v =>
    finset_sup'_ne_top (M.predecessors j v) (M.nonempty j v)
      (fun u => completion M j u ω) (fun u _ => hω u))

/-- All layers and vertices are simultaneously finite almost surely. -/
theorem completion_finite_ae [Countable V] (M : TaskPaths.System V) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ j v, completion M j v ω ≠ ⊤ := by
  rw [ae_all_iff]
  exact completion_layer_finite_ae M

theorem ready_finite_ae [Countable V] (M : TaskPaths.System V) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ j v, ready M j v ω ≠ ⊤ := by
  rw [ae_all_iff]
  exact ready_layer_finite_ae M

theorem all_times_finite_ae [Countable V] (M : TaskPaths.System V) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V,
      (∀ j v, completion M j v ω ≠ ⊤) ∧ (∀ j v, ready M j v ω ≠ ⊤) :=
  (completion_finite_ae M).and (ready_finite_ae M)

theorem ready_lt_completion (M : TaskPaths.System V) (j : ℕ) (v : V)
    (ω : ExponentialClocks.Sample V) (hfinite : ready M j v ω ≠ ⊤) :
    ready M j v ω < completion M (j + 1) v ω :=
  ExtendedNextRing.ready_lt_after (ArrivalFiltration.chronologicalArrival v) (ready M j v)
    ω hfinite

theorem ready_lt_completion_ae [Countable V] (M : TaskPaths.System V) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ j v,
      ready M j v ω < completion M (j + 1) v ω :=
  (ready_finite_ae M).mono (fun ω hω j v => ready_lt_completion M j v ω (hω j v))

/-- The concrete nonperiodic square needs no graph or finiteness hypotheses. -/
theorem square_all_times_finite_ae (n : ℕ) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (SquareTasks.Vertex n),
      (∀ j v, completion (SquareTasks.system n) j v ω ≠ ⊤) ∧
      (∀ j v, ready (SquareTasks.system n) j v ω ≠ ⊤) :=
  all_times_finite_ae (SquareTasks.system n)

end MathResearchAnalysis.ClockReadiness
