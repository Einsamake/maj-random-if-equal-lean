module

public import MathResearchAnalysis.ClockWordMarks
public import MathResearchAnalysis.MarkedEventTrace

set_option autoImplicit false

/-!
# Actual asynchronous endpoint law on each clock-word fiber

The endpoint uses the genuine clock word, in chronological order, and its
actual identity-indexed independent fair marks. On each fixed clock-word
fiber its joint law with any additional measurable clock event factors into
the clock-event probability and the execution law of a fresh finite fair
vector. This conclusion is derived from the constructed product measure;
no conditional mark law or independence conclusion is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace MathResearchAnalysis.ClockExecutionLaw

abbrev Event (n : ℕ) := SquareSpin.Event n
abbrev Config (n : ℕ) := SquareSpin.Config n
abbrev Sample (n : ℕ) := ClockWordMarks.Sample n

/-- Read a finite vector by event identity, with false outside the listed events. -/
def freshMarks {n : ℕ} (events : List (Event n)) (ξ : Fin events.length → Bool)
    (e : Event n) : Bool :=
  if h : e ∈ events then ξ ⟨events.idxOf e, List.idxOf_lt_length_of_mem h⟩ else false

/-- The vector is listed newest first, and execution reverses it chronologically. -/
def freshRun {n : ℕ} (events : List (Event n)) (ξ : Fin events.length → Bool)
    (initial : Config n) : Config n :=
  MarkedEventTrace.execute (freshMarks events ξ) events.reverse initial

/-- Restrict a mark field to the positions of a fixed identity word. -/
def fixedVector {n : ℕ} (events : List (Event n)) (η : Event n → Bool) :
    Fin events.length → Bool := fun k => η (events.get k)

theorem freshMarks_fixedVector {n : ℕ} (events : List (Event n))
    (η : Event n → Bool) (e : Event n) (he : e ∈ events) :
    freshMarks events (fixedVector events η) e = η e := by
  simp only [freshMarks, dite_eq_left he, fixedVector, List.get_eq_getElem,
    List.getElem_idxOf]

/-- Reconstruction preserves every used mark, including in a list with repetitions. -/
theorem freshRun_fixedVector {n : ℕ} (events : List (Event n))
    (η : Event n → Bool) (initial : Config n) :
    freshRun events (fixedVector events η) initial =
      MarkedEventTrace.execute η events.reverse initial := by
  exact MarkedEventTrace.execute_eq_of_marks_agree _ _ events.reverse
    (fun e he => freshMarks_fixedVector events η e (List.mem_reverse.mp he)) initial

theorem freshRun_measurable {n : ℕ} (events : List (Event n)) (initial : Config n) :
    Measurable (fun ξ => freshRun events ξ initial) := measurable_of_countable _

theorem fixedVector_measurable {n : ℕ} (events : List (Event n)) :
    Measurable (fixedVector events) :=
  measurable_pi_iff.mpr fun k => measurable_pi_apply (events.get k)

theorem fixedRun_measurable {n : ℕ} (events : List (Event n)) (initial : Config n) :
    Measurable (fun η => MarkedEventTrace.execute η events.reverse initial) := by
  have h := (freshRun_measurable events initial).comp (fixedVector_measurable events)
  simpa only [Function.comp_def, freshRun_fixedVector] using h

/-- The actual asynchronous endpoint at time `t`, including the total word fallback. -/
def endpoint (n : ℕ) (t : ℝ) (initial : Config n) (z : Sample n) : Config n :=
  MarkedEventTrace.executeClockWord z.2 z.1 t initial

theorem endpoint_measurable (n : ℕ) (t : ℝ) (initial : Config n) :
    Measurable (endpoint n t initial) := by
  have hrun : Measurable (fun z : List (Event n) × FairMarks.Sample (Event n) =>
      MarkedEventTrace.execute z.2 z.1.reverse initial) :=
    measurable_from_prod_countable_right fun events => fixedRun_measurable events initial
  exact hrun.comp (((ClockEventWord.word_measurable t).comp measurable_fst).prodMk
    measurable_snd)

def wordFiber (n : ℕ) (t : ℝ) (events : List (Event n)) :
    Set (ExponentialClocks.Sample (SquareTasks.Vertex n)) :=
  {ω | ClockEventWord.word ω t = events}

theorem wordFiber_measurable (n : ℕ) (t : ℝ) (events : List (Event n)) :
    MeasurableSet (wordFiber n t events) := ClockEventWord.measurableSet_word_eq t events

theorem wordFiber_eq_empty_of_not_nodup (n : ℕ) (t : ℝ) (events : List (Event n))
    (h : ¬ events.Nodup) : wordFiber n t events = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ω hω
  exact h (hω ▸ ClockEventWord.word_nodup ω t)

theorem wordFiber_subset_enough (n : ℕ) (t : ℝ) (events : List (Event n)) :
    wordFiber n t events ⊆ ClockWordMarks.enough n t events.length := by
  intro ω hω
  change events.length ≤ (ClockEventWord.word ω t).length
  rw [hω]

/-- The actual selected vector equals the restriction of the actual mark field. -/
theorem prefixMarks_eq_fixedVector (n : ℕ) (t : ℝ) (events : List (Event n))
    (z : Sample n) (hword : ClockEventWord.word z.1 t = events) :
    ClockWordMarks.prefixMarks n t events.length z = fixedVector events z.2 := by
  funext k
  simp only [ClockWordMarks.prefixMarks, FairMarks.selected, FairMarks.fixedSelection,
    ClockWordMarks.prefixSelection, fixedVector, hword,
    List.getD_eq_getElem _ _ k.isLt, List.get_eq_getElem]

/-- Pointwise execution identification on a genuine clock-word fiber. -/
theorem endpoint_eq_freshRun (n : ℕ) (t : ℝ) (events : List (Event n))
    (initial : Config n) (z : Sample n) (hword : ClockEventWord.word z.1 t = events) :
    endpoint n t initial z =
      freshRun events (ClockWordMarks.prefixMarks n t events.length z) initial := by
  rw [prefixMarks_eq_fixedVector n t events z hword, freshRun_fixedVector]
  simp only [endpoint, MarkedEventTrace.executeClockWord, hword]

/-- The finite fair-vector execution measure for a fixed newest-first identity word. -/
def freshExecutionLaw {n : ℕ} (events : List (Event n)) (initial : Config n) :
    Measure (Config n) :=
  Measure.map (fun ξ => freshRun events ξ initial) (FairMarks.vectorMeasure events.length)

instance freshExecutionLaw_probability {n : ℕ} (events : List (Event n))
    (initial : Config n) : IsProbabilityMeasure (freshExecutionLaw events initial) := by
  unfold freshExecutionLaw
  infer_instance

theorem freshExecutionLaw_apply {n : ℕ} (events : List (Event n))
    (initial : Config n) (B : Set (Config n)) (hB : MeasurableSet B) :
    freshExecutionLaw events initial B = FairMarks.vectorMeasure events.length
      {ξ | freshRun events ξ initial ∈ B} := by
  exact Measure.map_apply (freshRun_measurable events initial) hB

/-- Joint endpoint law on any fixed word fiber, retaining any further clock event.
No distinctness premise is needed: impossible words simply have empty fibers. -/
theorem endpoint_joint_measure (n : ℕ) (t : ℝ) (events : List (Event n))
    (initial : Config n)
    (E : Set (ExponentialClocks.Sample (SquareTasks.Vertex n))) (hE : MeasurableSet E)
    (B : Set (Config n)) (hB : MeasurableSet B) :
    ClockWordMarks.measure n {z | z.1 ∈ E ∩ wordFiber n t events ∧
      endpoint n t initial z ∈ B} =
      ExponentialClocks.clockMeasure (SquareTasks.Vertex n) (E ∩ wordFiber n t events) *
        freshExecutionLaw events initial B := by
  let F := E ∩ wordFiber n t events
  have hF : MeasurableSet F := hE.inter (wordFiber_measurable n t events)
  have henough : F ∩ ClockWordMarks.enough n t events.length = F :=
    Set.inter_eq_left.mpr fun _ h => wordFiber_subset_enough n t events h.2
  have hset : {z : Sample n | z.1 ∈ E ∩ wordFiber n t events ∧
      endpoint n t initial z ∈ B} =
      {z : Sample n | z.1 ∈ F ∩ ClockWordMarks.enough n t events.length ∧
        ClockWordMarks.prefixMarks n t events.length z ∈
          {ξ | freshRun events ξ initial ∈ B}} := by
    ext z
    rw [henough]
    change (z.1 ∈ F ∧ endpoint n t initial z ∈ B) ↔
      (z.1 ∈ F ∧ freshRun events
        (ClockWordMarks.prefixMarks n t events.length z) initial ∈ B)
    constructor
    · rintro ⟨hclock, hout⟩
      exact ⟨hclock, (endpoint_eq_freshRun n t events initial z hclock.2) ▸ hout⟩
    · rintro ⟨hclock, hout⟩
      exact ⟨hclock, (endpoint_eq_freshRun n t events initial z hclock.2).symm ▸ hout⟩
  rw [hset, henough, freshExecutionLaw_apply events initial B hB]
  have h := ClockWordMarks.prefixMarks_joint_measure n t events.length F hF
    {ξ | freshRun events ξ initial ∈ B} ((freshRun_measurable events initial) hB)
  rw [henough] at h
  exact h

theorem endpoint_word_fiber_measure (n : ℕ) (t : ℝ) (events : List (Event n))
    (initial : Config n) (B : Set (Config n)) (hB : MeasurableSet B) :
    ClockWordMarks.measure n {z | z.1 ∈ wordFiber n t events ∧
      endpoint n t initial z ∈ B} =
      ExponentialClocks.clockMeasure (SquareTasks.Vertex n) (wordFiber n t events) *
        freshExecutionLaw events initial B := by
  simpa only [Set.univ_inter] using endpoint_joint_measure n t events initial
    Set.univ MeasurableSet.univ B hB

end MathResearchAnalysis.ClockExecutionLaw
