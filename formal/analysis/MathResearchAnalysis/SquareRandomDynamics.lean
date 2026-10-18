module

public import MathResearchAnalysis.SquareBatch
public import MathResearchAnalysis.SquareScanKernel
public import MathResearchAnalysis.ClockEndpointMean

set_option autoImplicit false

/-!
# Actual independent-mark finite-square random dynamics

Both trajectories use the same genuine infinite product of fair site/time
marks. Positive slot `j + 1` uses only identities `(v, j + 1)`. The complete
checkerboard event word executes the actual alternating trajectory, and its
independent-mark integral is the already constructed fixed scan kernel.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.SquareRandomDynamics

abbrev Site (n : ℕ) := SquareTasks.Vertex n
abbrev Event (n : ℕ) := SquareSpin.Event n
abbrev Config (n : ℕ) := SquareSpin.Config n
abbrev Sample (n : ℕ) := FairMarks.Sample (Event n)

def measure (n : ℕ) : Measure (Sample n) := FairMarks.markMeasure (Event n)

instance measure_probability (n : ℕ) : IsProbabilityMeasure (measure n) := by
  unfold measure
  infer_instance

def marks {n : ℕ} (η : Sample n) (j : ℕ) (v : Site n) : Bool := η (v, j)

def synchronous (n : ℕ) (initial : Config n) (t : ℕ) (η : Sample n) : Config n :=
  SquareDynamics.synchronous (marks η) initial t

def alternating (n : ℕ) (initial : Config n) (phase : Bool) (t : ℕ)
    (η : Sample n) : Config n :=
  SquareDynamics.alternating (marks η) initial phase t

def fixedWord (n : ℕ) (c : Bool) (count : ℕ) : List (Event n) :=
  (List.range count).flatMap (fun j =>
    (SquareTasks.tasks n c j).toList.map (fun v => (v, j + 1)))

theorem marks_measurable (n : ℕ) (j : ℕ) :
    Measurable (fun η : Sample n => marks η j) :=
  measurable_pi_iff.mpr (fun v => measurable_pi_apply (v, j))

theorem synchronous_measurable (n : ℕ) (initial : Config n) (t : ℕ) :
    Measurable (synchronous n initial t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hs : Measurable (fun z : Config n × SquareDynamics.Mark n =>
        SquareSpin.synchronousStep z.1 z.2) := measurable_of_countable _
    exact hs.comp (ih.prodMk (marks_measurable n (t + 1)))

theorem alternating_measurable (n : ℕ) (initial : Config n) (phase : Bool) (t : ℕ) :
    Measurable (alternating n initial phase t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hs : Measurable (fun z : Config n × SquareDynamics.Mark n =>
        SquareSpin.checkerboardStep z.1
          (BipartiteDynamics.activeColour phase (t + 1)) z.2) := measurable_of_countable _
    exact hs.comp (ih.prodMk (marks_measurable n (t + 1)))

@[simp] theorem fixedWord_zero (n : ℕ) (c : Bool) : fixedWord n c 0 = [] := by
  simp [fixedWord]

theorem fixedWord_succ (n : ℕ) (c : Bool) (count : ℕ) :
    fixedWord n c (count + 1) = fixedWord n c count ++
      (SquareTasks.tasks n c count).toList.map (fun v => (v, count + 1)) := by
  simp [fixedWord, List.range_succ, List.flatMap_append]

theorem fixedWord_nodup (n : ℕ) (c : Bool) (count : ℕ) :
    (fixedWord n c count).Nodup := by
  cases count with
  | zero => simp
  | succ k =>
    have h := (ClockSelectedWord.layerTasks_nodup n c k).map Prod.swap_injective
    simpa only [fixedWord, ClockSelectedWord.layerTasks, List.map_flatMap,
      List.map_map, Function.comp_def, Prod.swap_prod_mk] using h

theorem fixedWord_sites (n : ℕ) (c : Bool) (count : ℕ) :
    (fixedWord n c count).map Prod.fst = SquareScanKernel.scanWord n c 0 count := by
  simp [fixedWord, SquareScanKernel.scanWord, SquareScanKernel.taskWord,
    List.map_flatMap, List.map_map, Function.comp_def]

theorem fixedWord_positive (n : ℕ) (c : Bool) (count : ℕ) (e : Event n)
    (he : e ∈ fixedWord n c count) : 0 < e.2 := by
  rcases List.mem_flatMap.mp he with ⟨j, _, he⟩
  rcases List.mem_map.mp he with ⟨v, _, rfl⟩
  exact Nat.zero_lt_succ j

theorem execute_taskLayer_eq_checkerboard (n : ℕ) (c : Bool) (j : ℕ)
    (η : Sample n) (initial : Config n) :
    MarkedEventTrace.execute η
      ((SquareTasks.tasks n c j).toList.map (fun v => (v, j + 1))) initial =
      SquareSpin.checkerboardStep initial
        (BipartiteDynamics.activeColour (!c) (j + 1)) (marks η (j + 1)) := by
  rw [← SquareBatch.taskBatch_eq_checkerboard n c j (marks η (j + 1)) initial]
  unfold MarkedEventTrace.execute SquareBatch.batch EventTrace.execute
  rw [List.foldl_map]
  rfl

/-- The deterministic chronological word uses distinct actual positive-slot identities. -/
theorem execute_fixedWord_eq_alternating (n : ℕ) (c : Bool) (count : ℕ)
    (η : Sample n) (initial : Config n) :
    MarkedEventTrace.execute η (fixedWord n c count) initial =
      alternating n initial (!c) count η := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [fixedWord_succ]
    change EventTrace.execute (SquareSpin.updateEvent η) (_ ++ _) initial = _
    rw [EventTrace.execute_append]
    change MarkedEventTrace.execute η
      ((SquareTasks.tasks n c count).toList.map (fun v => (v, count + 1)))
      (MarkedEventTrace.execute η (fixedWord n c count) initial) = _
    rw [ih, execute_taskLayer_eq_checkerboard]
    exact (SquareDynamics.alternating_succ (marks η) initial (!c) count).symm

/-- This expectation is under the constructed infinite independent fair-mark measure. -/
theorem integral_alternating_eq_scanMean (n : ℕ) (initial : Config n)
    (phase : Bool) (count : ℕ) (φ : Config n → ℝ) :
    (∫ η, φ (alternating n initial phase count η) ∂measure n) =
      SquareScanKernel.scanMean n (!phase) 0 count φ initial := by
  have h := ClockEndpointMean.integral_marked_execute_eq_coldWord
    (fixedWord n (!phase) count) (fixedWord_nodup n (!phase) count) φ initial
  simp only [execute_fixedWord_eq_alternating, Bool.not_not, fixedWord_sites] at h
  exact h

/-- In particular, all time-zero marks are absent from the actual trajectory. -/
theorem synchronous_eq_of_agree_positive (n : ℕ) (initial : Config n) (t : ℕ)
    (η ξ : Sample n) (h : ∀ j, 0 < j → ∀ v, η (v, j) = ξ (v, j)) :
    synchronous n initial t η = synchronous n initial t ξ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change SquareSpin.synchronousStep (synchronous n initial t η) (marks η (t + 1)) =
      SquareSpin.synchronousStep (synchronous n initial t ξ) (marks ξ (t + 1))
    rw [ih]
    congr 1
    funext v
    exact h (t + 1) (Nat.zero_lt_succ t) v

theorem alternating_eq_of_agree_positive (n : ℕ) (initial : Config n)
    (phase : Bool) (t : ℕ) (η ξ : Sample n)
    (h : ∀ j, 0 < j → ∀ v, η (v, j) = ξ (v, j)) :
    alternating n initial phase t η = alternating n initial phase t ξ := by
  have hword := MarkedEventTrace.execute_eq_of_marks_agree η ξ (fixedWord n (!phase) t)
    (fun e he => h e.2 (fixedWord_positive n (!phase) t e he) e.1) initial
  simpa only [execute_fixedWord_eq_alternating, Bool.not_not] using hword

end MathResearchAnalysis.SquareRandomDynamics
