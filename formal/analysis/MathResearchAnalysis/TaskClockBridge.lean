module

public import MathResearchAnalysis.ClockReadiness
public import MathResearchAnalysis.ExtendedStoppingPath

set_option autoImplicit false

/-!
# Actual clock completion and the real path recurrence

Real representatives are used only after all actual extended times have been
proved finite on a common full-measure set. They are not asserted to be real
stopping times. The generic predecessor table needs a one-layer shift, since
the clock recurrence includes a zero initialization layer. The concrete square
table is layer-independent and needs no change.
-/

public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.TaskClockBridge

variable {V α : Type*} [DecidableEq V]

/-- The positive-layer path table for a zero-initialized clock recurrence. -/
@[expose] def positiveSystem (M : TaskPaths.System V) : TaskPaths.System V where
  predecessors := fun k v => M.predecessors (k + 1) v
  nonempty := fun k v => M.nonempty (k + 1) v

theorem representative_le {a b : WithTop ℝ} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (hab : a ≤ b) : a.untopD 0 ≤ b.untopD 0 := by
  lift a to ℝ using ha
  lift b to ℝ using hb
  simpa using hab

theorem representative_sup' (s : Finset α) (hs : s.Nonempty) (f : α → WithTop ℝ)
    (hfinite : ∀ a ∈ s, f a ≠ ⊤) :
    (s.sup' hs f).untopD 0 = s.sup' hs (fun a => (f a).untopD 0) := by
  have hmax := ClockReadiness.finset_sup'_ne_top s hs f hfinite
  apply le_antisymm
  · obtain ⟨a, ha, heq⟩ := Finset.exists_mem_eq_sup' hs f
    rw [heq]
    exact Finset.le_sup' (fun a => (f a).untopD 0) ha
  · apply Finset.sup'_le
    intro a ha
    exact representative_le (hfinite a ha) hmax (Finset.le_sup' f ha)

@[expose] def realCompletion (M : TaskPaths.System V) (j : Nat) (v : V)
    (ω : ExponentialClocks.Sample V) : ℝ := (ClockReadiness.completion M j v ω).untopD 0

@[expose] def realReady (M : TaskPaths.System V) (j : Nat) (v : V)
    (ω : ExponentialClocks.Sample V) : ℝ := (ClockReadiness.ready M j v ω).untopD 0

@[expose] def delay (M : TaskPaths.System V) (k : Nat) (v : V)
    (ω : ExponentialClocks.Sample V) : ℝ :=
  max (realCompletion M (k + 1) v ω - realReady M k v ω) 0

theorem realCompletion_measurable (M : TaskPaths.System V) (j : Nat) (v : V) :
    Measurable (realCompletion M j v) :=
  (ExtendedStoppingPath.representative_measurable (ArrivalFiltration.clockHistory V)
    (ClockReadiness.completion M j v) (ClockReadiness.completion_isStoppingTime M j v)).mono
      (ClockReadiness.completion_isStoppingTime M j v).measurableSpace_le le_rfl

theorem realReady_measurable (M : TaskPaths.System V) (j : Nat) (v : V) :
    Measurable (realReady M j v) :=
  (ExtendedStoppingPath.representative_measurable (ArrivalFiltration.clockHistory V)
    (ClockReadiness.ready M j v) (ClockReadiness.ready_isStoppingTime M j v)).mono
      (ClockReadiness.ready_isStoppingTime M j v).measurableSpace_le le_rfl

theorem delay_measurable (M : TaskPaths.System V) (k : Nat) (v : V) :
    Measurable (delay M k v) :=
  ((realCompletion_measurable M (k + 1) v).sub (realReady_measurable M k v)).max measurable_const

theorem delay_nonnegative (M : TaskPaths.System V) (k : Nat) (v : V)
    (ω : ExponentialClocks.Sample V) : 0 ≤ delay M k v ω := le_max_right _ _

theorem realReady_eq_sup (M : TaskPaths.System V) (j : Nat) (v : V)
    (ω : ExponentialClocks.Sample V)
    (hfinite : ∀ u, ClockReadiness.completion M j u ω ≠ ⊤) :
    realReady M j v ω = (M.predecessors j v).sup' (M.nonempty j v)
      (fun u => realCompletion M j u ω) :=
  representative_sup' (M.predecessors j v) (M.nonempty j v)
    (fun u => ClockReadiness.completion M j u ω) (fun u _ => hfinite u)

theorem delay_add_realReady (M : TaskPaths.System V) (j : Nat) (v : V)
    (ω : ExponentialClocks.Sample V)
    (hready : ClockReadiness.ready M j v ω ≠ ⊤)
    (hcomplete : ClockReadiness.completion M (j + 1) v ω ≠ ⊤) :
    delay M j v ω + realReady M j v ω = realCompletion M (j + 1) v ω := by
  have hle : realReady M j v ω ≤ realCompletion M (j + 1) v ω :=
    representative_le hready hcomplete (ClockReadiness.ready_le_completion M j v ω)
  unfold delay
  rw [max_eq_left (sub_nonneg.mpr hle)]
  ring

theorem realCompletion_eq_pathCompletion (M : TaskPaths.System V)
    (ω : ExponentialClocks.Sample V)
    (hcomplete : ∀ j v, ClockReadiness.completion M j v ω ≠ ⊤)
    (hready : ∀ j v, ClockReadiness.ready M j v ω ≠ ⊤) (k : Nat) (v : V) :
    realCompletion M (k + 1) v ω =
      (positiveSystem M).completion (fun j u => delay M j u ω) k v := by
  induction k generalizing v with
  | zero =>
    have h := delay_add_realReady M 0 v ω (hready 0 v) (hcomplete 1 v)
    have hzero : realReady M 0 v ω = 0 := by simp [realReady, ClockReadiness.ready_zero]
    simpa only [hzero, add_zero, TaskPaths.System.completion] using h.symm
  | succ k ih =>
    calc
      realCompletion M (k + 1 + 1) v ω = delay M (k + 1) v ω +
          realReady M (k + 1) v ω :=
        (delay_add_realReady M (k + 1) v ω (hready (k + 1) v) (hcomplete (k + 1 + 1) v)).symm
      _ = delay M (k + 1) v ω + (M.predecessors (k + 1) v).sup'
          (M.nonempty (k + 1) v) (fun u => realCompletion M (k + 1) u ω) := by
        rw [realReady_eq_sup M (k + 1) v ω (hcomplete (k + 1))]
      _ = (positiveSystem M).completion (fun j u => delay M j u ω) (k + 1) v := by
        simp only [TaskPaths.System.completion, positiveSystem, ih]

theorem realCompletion_eq_pathCompletion_ae [Countable V] (M : TaskPaths.System V) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ k v,
      realCompletion M (k + 1) v ω =
        (positiveSystem M).completion (fun j u => delay M j u ω) k v := by
  filter_upwards [ClockReadiness.all_times_finite_ae M] with ω hω
  exact fun k v => realCompletion_eq_pathCompletion M ω hω.1 hω.2 k v

theorem positiveSystem_square (n : Nat) : positiveSystem (SquareTasks.system n) =
    SquareTasks.system n := rfl

theorem square_realCompletion_eq_pathCompletion_ae (n : Nat) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (SquareTasks.Vertex n), ∀ k v,
      realCompletion (SquareTasks.system n) (k + 1) v ω =
        (SquareTasks.system n).completion
          (fun j u => delay (SquareTasks.system n) j u ω) k v := by
  simpa only [positiveSystem_square] using realCompletion_eq_pathCompletion_ae (SquareTasks.system n)

end MathResearchAnalysis.TaskClockBridge
