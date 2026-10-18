module

public import MathResearchAnalysis.TaskClockBridge
public import MathResearchAnalysis.FixedClockPath
public import MathResearchAnalysis.SquareTaskTail

set_option autoImplicit false

/-!
# The actual extended clock maximum and its conditional tail

The maximum is built from the constructed clock completions at the actually
selected square tasks. No real-valued completion, integrability or known-past
hypothesis is supplied. The remaining waiting-law and history-independence
inputs are exactly the unresolved strong-Markov interface.
-/

public noncomputable section

open MeasureTheory ProbabilityTheory

namespace MathResearchAnalysis.ClockMaximum

@[expose] def squareLayer (n : Nat) (c : Bool) (j : Nat)
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) : WithTop ℝ :=
  (SquareTasks.tasks n c j).sup' (SquareTasks.tasks_nonempty n c j)
    (fun v => ClockReadiness.completion (SquareTasks.system n) (j + 1) v ω)

@[expose] def squareMaximum (n : Nat) (c : Bool) (k : Nat)
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) : WithTop ℝ :=
  (Finset.range (k + 1)).sup' (by simp) (fun j => squareLayer n c j ω)

theorem squareMaximum_isStoppingTime (n : Nat) (c : Bool) (k : Nat) :
    IsStoppingTime (ArrivalFiltration.clockHistory (SquareTasks.Vertex n)) (squareMaximum n c k) := by
  apply ClockReadiness.finset_sup'_isStoppingTime
  intro j _
  apply ClockReadiness.finset_sup'_isStoppingTime
  intro v _
  exact ClockReadiness.completion_isStoppingTime (SquareTasks.system n) (j + 1) v

theorem squareMaximum_ne_top (n : Nat) (c : Bool) (k : Nat)
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n))
    (hfinite : ∀ j v, ClockReadiness.completion (SquareTasks.system n) j v ω ≠ ⊤) :
    squareMaximum n c k ω ≠ ⊤ := by
  apply ClockReadiness.finset_sup'_ne_top
  intro j _
  apply ClockReadiness.finset_sup'_ne_top
  intro v _
  exact hfinite (j + 1) v

theorem squareMaximum_finite_ae (n : Nat) (c : Bool) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (SquareTasks.Vertex n), ∀ k,
      squareMaximum n c k ω ≠ ⊤ := by
  filter_upwards [ClockReadiness.completion_finite_ae (SquareTasks.system n)] with ω hω
  exact fun k => squareMaximum_ne_top n c k ω hω

theorem real_squareLayer_eq (n : Nat) (c : Bool) (j : Nat)
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n))
    (hcomplete : ∀ i v, ClockReadiness.completion (SquareTasks.system n) i v ω ≠ ⊤)
    (hready : ∀ i v, ClockReadiness.ready (SquareTasks.system n) i v ω ≠ ⊤) :
    (squareLayer n c j ω).untopD 0 = (SquareTasks.system n).terminalMaximum
      (SquareTasks.tasks n c j) (SquareTasks.tasks_nonempty n c j)
      (fun i v => TaskClockBridge.delay (SquareTasks.system n) i v ω) j := by
  calc
    _ = (SquareTasks.tasks n c j).sup' (SquareTasks.tasks_nonempty n c j)
        (fun v => TaskClockBridge.realCompletion (SquareTasks.system n) (j + 1) v ω) :=
      TaskClockBridge.representative_sup' _ _ _ (fun v _ => hcomplete (j + 1) v)
    _ = (SquareTasks.tasks n c j).sup' (SquareTasks.tasks_nonempty n c j)
        (fun v => (SquareTasks.system n).completion
          (fun i u => TaskClockBridge.delay (SquareTasks.system n) i u ω) j v) := by
      congr 1
      funext v
      simpa only [TaskClockBridge.positiveSystem_square] using
        TaskClockBridge.realCompletion_eq_pathCompletion (SquareTasks.system n) ω
          hcomplete hready j v
    _ = _ := rfl

theorem real_squareMaximum_eq (n : Nat) (c : Bool) (k : Nat)
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n))
    (hcomplete : ∀ i v, ClockReadiness.completion (SquareTasks.system n) i v ω ≠ ⊤)
    (hready : ∀ i v, ClockReadiness.ready (SquareTasks.system n) i v ω ≠ ⊤) :
    (squareMaximum n c k ω).untopD 0 = (SquareTasks.system n).prefixMaximum
      (SquareTasks.tasks n c) (SquareTasks.tasks_nonempty n c)
      (fun i v => TaskClockBridge.delay (SquareTasks.system n) i v ω) k := by
  calc
    _ = (Finset.range (k + 1)).sup' (by simp) (fun j => (squareLayer n c j ω).untopD 0) :=
      TaskClockBridge.representative_sup' _ _ _ (fun j _ =>
        ClockReadiness.finset_sup'_ne_top _ _ _ (fun v _ => hcomplete (j + 1) v))
    _ = _ := by
      simp only [real_squareLayer_eq n c _ ω hcomplete hready, TaskPaths.System.prefixMaximum]

theorem representative_lt_iff {a : WithTop ℝ} (ha : a ≠ ⊤) (t : ℝ) :
    (t : WithTop ℝ) < a ↔ t < a.untopD 0 := by
  lift a to ℝ using ha
  simp

theorem squareMaximum_exceeds_ae (n : Nat) (c : Bool) (k : Nat) (t : ℝ) :
    {ω | (t : WithTop ℝ) < squareMaximum n c k ω} =ᵐ[
      ExponentialClocks.clockMeasure (SquareTasks.Vertex n)]
      {ω | t < (SquareTasks.system n).prefixMaximum
        (SquareTasks.tasks n c) (SquareTasks.tasks_nonempty n c)
        (fun i v => TaskClockBridge.delay (SquareTasks.system n) i v ω) k} := by
  filter_upwards [ClockReadiness.all_times_finite_ae (SquareTasks.system n)] with ω hω
  apply propext
  rw [representative_lt_iff (squareMaximum_ne_top n c k ω hω.1),
    real_squareMaximum_eq n c k ω hω.1 hω.2]

@[expose] def origin (n : Nat) : SquareTasks.Vertex n := (⟨0, by omega⟩, ⟨0, by omega⟩)

/-- A tail for the constructed physical maximum, with no known-past input.
The law and independence of each actual stopped wait remain explicit. -/
theorem actual_square_eight_tail (n : Nat) (c : Bool) (k : Nat) (threshold : ℝ)
    (hlaw : ∀ p ∈ (SquareTasks.system n).terminalPaths (SquareTasks.tasks n c k) k,
      ∀ i < k + 1, HasLaw (TaskPathTail.pathWait
        (TaskClockBridge.delay (SquareTasks.system n)) p i) (expMeasure 1)
          (ExponentialClocks.clockMeasure (SquareTasks.Vertex n)))
    (hindep : ∀ p ∈ (SquareTasks.system n).terminalPaths (SquareTasks.tasks n c k) k,
      ∀ i < k + 1, Indep ((borel ℝ).comap (TaskPathTail.pathWait
        (TaskClockBridge.delay (SquareTasks.system n)) p i))
          (FixedClockPath.listFiltration (SquareTasks.system n) (origin n) p i)
            (ExponentialClocks.clockMeasure (SquareTasks.Vertex n))) :
    MeasurableSet {ω | (threshold : WithTop ℝ) < squareMaximum n c k ω} ∧
      (ExponentialClocks.clockMeasure (SquareTasks.Vertex n)).real
        {ω | (threshold : WithTop ℝ) < squareMaximum n c k ω} ≤
          (n + 2 : ℝ) ^ 2 * (8 : ℝ) ^ (k + 1) * Real.exp (-threshold / 2) := by
  have hknown : ∀ p ∈ (SquareTasks.system n).terminalPaths (SquareTasks.tasks n c k) k,
      ∀ i < k + 1, StronglyMeasurable[
        FixedClockPath.listFiltration (SquareTasks.system n) (origin n) p (i + 1)]
          (TaskPathTail.pathWait (TaskClockBridge.delay (SquareTasks.system n)) p i) := by
    intro p hp i hi
    obtain ⟨v, _, hv⟩ := ((SquareTasks.system n).mem_terminalPaths_iff
      (SquareTasks.tasks n c k) k p).mp hp
    have hlen := (SquareTasks.system n).path_length k v
      (((SquareTasks.system n).mem_paths_iff_legal k v p).mpr hv)
    apply FixedClockPath.pathWait_known_of_legal (SquareTasks.system n) (origin n) k v
    · simpa only [TaskClockBridge.positiveSystem_square] using hv
    · simpa only [hlen] using hi
  have htail := SquareTaskTail.square_prefix_eight_tail_of_law_indep n c k
    (TaskClockBridge.delay (SquareTasks.system n))
    (FixedClockPath.listFiltration (SquareTasks.system n) (origin n))
    (fun ω i v => TaskClockBridge.delay_nonnegative (SquareTasks.system n) i v ω)
    threshold hknown hlaw hindep
  refine ⟨(ArrivalFiltration.clockHistory (SquareTasks.Vertex n)).le threshold _
    ((squareMaximum_isStoppingTime n c k).measurableSet_gt threshold), ?_⟩
  rw [measureReal_congr (squareMaximum_exceeds_ae n c k threshold)]
  exact htail.2

end MathResearchAnalysis.ClockMaximum
