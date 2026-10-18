module

public import MathResearchAnalysis.ClockEventOrder
public import MathResearchAnalysis.ClockWordMarks

set_option autoImplicit false

/-!
# Fresh fair marks for the actual selected tasks

The finite task family contains every site selected in positive layers
`1, ..., k + 1`, with the alternating color convention of `SquareTasks`.
Its event identities are the actual next-ring indices computed from clock
readiness. Their measurability and almost-sure injectivity are proved here.
The selected finite mark vector consequently has the constructed fair product
law and is independent of the entire clock sample, hence of clock history.
No selected-mark law or independence assertion is supplied as a hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace MathResearchAnalysis.ClockSelectedMarks

section SelectedIndex

variable {Ω : Type*}

/-- A total next-ring index includes a zero default precisely when no future ring exists. -/
theorem selectedIndex_eq_iff (arrival : ℕ → Ω → ℝ) (ready : Ω → WithTop ℝ)
    (ω : Ω) (k : ℕ) :
    ExtendedNextRing.selectedIndex arrival ready ω = k ↔
      ((¬ ∃ j, ready ω < (arrival j ω : WithTop ℝ)) ∧ k = 0) ∨
      (ready ω < (arrival k ω : WithTop ℝ) ∧
        ∀ j, j < k → ¬ ready ω < (arrival j ω : WithTop ℝ)) := by
  classical
  by_cases hex : ∃ j, ready ω < (arrival j ω : WithTop ℝ)
  · rw [ExtendedNextRing.selectedIndex, dite_eq_left hex]
    simpa only [hex, not_true_eq_false, false_and, false_or] using Nat.find_eq_iff hex
  · have hk : ¬ ready ω < (arrival k ω : WithTop ℝ) := fun h => hex ⟨k, h⟩
    rw [ExtendedNextRing.selectedIndex, dite_eq_right hex]
    simp only [hex, not_false_eq_true, true_and, hk, false_and, or_false, eq_comm]

variable [MeasurableSpace Ω]

/-- Measurability is proved from the actual readiness/arrival comparisons, including defaults. -/
theorem selectedIndex_measurable (arrival : ℕ → Ω → ℝ) (ready : Ω → WithTop ℝ)
    (hcompare : ∀ j, MeasurableSet {ω | ready ω < (arrival j ω : WithTop ℝ)}) :
    Measurable (ExtendedNextRing.selectedIndex arrival ready) := by
  have hfuture : MeasurableSet {ω | ∃ j, ready ω < (arrival j ω : WithTop ℝ)} := by
    have heq : {ω | ∃ j, ready ω < (arrival j ω : WithTop ℝ)} =
        ⋃ j : ℕ, {ω | ready ω < (arrival j ω : WithTop ℝ)} := by ext ω; simp
    rw [heq]
    exact MeasurableSet.iUnion hcompare
  apply measurable_to_countable'
  intro k
  have hbefore : MeasurableSet {ω | ∀ j, j < k →
      ¬ ready ω < (arrival j ω : WithTop ℝ)} := by
    have heq : {ω | ∀ j, j < k → ¬ ready ω < (arrival j ω : WithTop ℝ)} =
        ⋂ j : ℕ, {ω | j < k → ¬ ready ω < (arrival j ω : WithTop ℝ)} := by
      ext ω
      simp
    rw [heq]
    exact MeasurableSet.iInter fun j =>
      (MeasurableSet.const (j < k)).imp (hcompare j).compl
  have heq : {ω | ExtendedNextRing.selectedIndex arrival ready ω = k} =
      {ω | (¬ ∃ j, ready ω < (arrival j ω : WithTop ℝ)) ∧ k = 0} ∪
        {ω | ready ω < (arrival k ω : WithTop ℝ) ∧
          ∀ j, j < k → ¬ ready ω < (arrival j ω : WithTop ℝ)} := by
    ext ω
    exact selectedIndex_eq_iff arrival ready ω k
  change MeasurableSet {ω | ExtendedNextRing.selectedIndex arrival ready ω = k}
  rw [heq]
  exact (hfuture.compl.inter (MeasurableSet.const (k = 0))).union
    ((hcompare k).inter hbefore)

end SelectedIndex

abbrev Site (n : ℕ) := SquareTasks.Vertex n
abbrev Event (n : ℕ) := ClockWordMarks.Event n
abbrev Task (n : ℕ) := ℕ × Site n
abbrev ClockSample (n : ℕ) := ExponentialClocks.Sample (Site n)
abbrev Sample (n : ℕ) := ClockWordMarks.Sample n

theorem eventIndex_measurable (n : ℕ) (j : ℕ) (v : Site n) :
    Measurable (ClockEventOrder.eventIndex n j v) := by
  apply selectedIndex_measurable
  intro a
  have hr := ClockReadiness.ready_isStoppingTime (SquareTasks.system n) (j - 1) v
  have ha := ArrivalFiltration.clock_arrival_isStoppingTime v a
  exact measurableSet_lt (hr.measurable.mono hr.measurableSpace_le le_rfl)
    (ha.measurable.mono ha.measurableSpace_le le_rfl)

theorem eventId_measurable (n : ℕ) (j : ℕ) (v : Site n) :
    Measurable (ClockEventOrder.eventId n j v) :=
  measurable_const.prodMk (eventIndex_measurable n j v)

/-- An order-preserving adapter for any predetermined finite enumeration of selected tasks. -/
def listIdentity (n : ℕ) (tasks : List (Task n)) (ω : ClockSample n) :
    Fin tasks.length → Event n :=
  fun i => ClockEventOrder.eventId n (tasks.get i).1 (tasks.get i).2 ω

theorem listIdentity_measurable (n : ℕ) (tasks : List (Task n)) :
    Measurable (listIdentity n tasks) :=
  measurable_pi_iff.mpr fun i => eventId_measurable n (tasks.get i).1 (tasks.get i).2

theorem listIdentity_injective_ae (n : ℕ) (c : Bool) (tasks : List (Task n))
    (unique : tasks.Nodup)
    (selected : ∀ p ∈ tasks, ClockEventOrder.Selected n c p.1 p.2) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (Site n),
      Function.Injective (listIdentity n tasks ω) := by
  filter_upwards [ClockEventOrder.distinct_selected_eventId_ae n c] with ω hω
  intro a b hab
  apply unique.injective_get
  by_contra htask
  exact (hω _ _ _ _ (selected _ (List.get_mem _ _))
    (selected _ (List.get_mem _ _)) htask) hab

def listMarks (n : ℕ) (tasks : List (Task n)) (z : Sample n) : Fin tasks.length → Bool :=
  FairMarks.selected (listIdentity n tasks) z

theorem listMarks_measurable (n : ℕ) (tasks : List (Task n)) :
    Measurable (listMarks n tasks) :=
  FairMarks.selected_measurable _ (listIdentity_measurable n tasks)

theorem listMarks_hasLaw (n : ℕ) (c : Bool) (tasks : List (Task n))
    (unique : tasks.Nodup)
    (selected : ∀ p ∈ tasks, ClockEventOrder.Selected n c p.1 p.2) :
    HasLaw (listMarks n tasks) (FairMarks.vectorMeasure tasks.length)
      (ClockWordMarks.measure n) :=
  FairMarks.selected_hasLaw (ExponentialClocks.clockMeasure (Site n))
    (listIdentity n tasks) (listIdentity_measurable n tasks)
    (listIdentity_injective_ae n c tasks unique selected)

theorem listMarks_indep_clock (n : ℕ) (c : Bool) (tasks : List (Task n))
    (unique : tasks.Nodup)
    (selected : ∀ p ∈ tasks, ClockEventOrder.Selected n c p.1 p.2) :
    IndepFun (fun z : Sample n => z.1) (listMarks n tasks) (ClockWordMarks.measure n) :=
  FairMarks.selected_indep_clock (ExponentialClocks.clockMeasure (Site n))
    (listIdentity n tasks) (listIdentity_measurable n tasks)
    (listIdentity_injective_ae n c tasks unique selected)

/-- Every actual selected task from the first `k + 1` positive layers. -/
def taskSet (n : ℕ) (c : Bool) (k : ℕ) : Finset (Task n) :=
  (Finset.range (k + 1)).biUnion fun j =>
    (SquareTasks.tasks n c j).image fun v => (j + 1, v)

theorem mem_taskSet_iff (n : ℕ) (c : Bool) (k j : ℕ) (v : Site n) :
    (j, v) ∈ taskSet n c k ↔ ClockEventOrder.Selected n c j v ∧ j ≤ k + 1 := by
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨a, ha, hm⟩
    rcases Finset.mem_image.mp hm with ⟨u, hu, heq⟩
    cases heq
    exact ⟨⟨by omega, by simpa using hu⟩, by simpa using Finset.mem_range.mp ha⟩
  · rintro ⟨hj, hbound⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j - 1, Finset.mem_range.mpr (by have := hj.1; omega), ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨v, hj.2, ?_⟩
    have hjpos := hj.1
    congr 1
    omega

/-- A deterministic enumeration of the actual finite task family. -/
def taskList (n : ℕ) (c : Bool) (k : ℕ) : List (Task n) := (taskSet n c k).toList

theorem taskList_length (n : ℕ) (c : Bool) (k : ℕ) :
    (taskList n c k).length = (taskSet n c k).card := Finset.length_toList _

theorem taskList_nodup (n : ℕ) (c : Bool) (k : ℕ) :
    (taskList n c k).Nodup := Finset.nodup_toList _

def taskAt (n : ℕ) (c : Bool) (k : ℕ) (i : Fin (taskSet n c k).card) : Task n :=
  (taskList n c k).get ⟨i.val, by simpa only [taskList_length] using i.isLt⟩

theorem taskAt_mem (n : ℕ) (c : Bool) (k : ℕ) (i : Fin (taskSet n c k).card) :
    taskAt n c k i ∈ taskSet n c k :=
  Finset.mem_toList.mp (List.get_mem _ _)

theorem taskAt_selected (n : ℕ) (c : Bool) (k : ℕ) (i : Fin (taskSet n c k).card) :
    ClockEventOrder.Selected n c (taskAt n c k i).1 (taskAt n c k i).2 :=
  ((mem_taskSet_iff n c k _ _).mp (taskAt_mem n c k i)).1

theorem taskAt_injective (n : ℕ) (c : Bool) (k : ℕ) :
    Function.Injective (taskAt n c k) := by
  intro a b hab
  have hi := (taskList_nodup n c k).injective_get hab
  apply Fin.ext
  exact congrArg (fun i : Fin (taskList n c k).length => i.val) hi

/-- Clock-only selection of actual site/ring event identities. -/
def selectedIdentity (n : ℕ) (c : Bool) (k : ℕ) (ω : ClockSample n) :
    Fin (taskSet n c k).card → Event n :=
  fun i => ClockEventOrder.eventId n (taskAt n c k i).1 (taskAt n c k i).2 ω

theorem selectedIdentity_measurable (n : ℕ) (c : Bool) (k : ℕ) :
    Measurable (selectedIdentity n c k) :=
  measurable_pi_iff.mpr fun i =>
    eventId_measurable n (taskAt n c k i).1 (taskAt n c k i).2

theorem selectedIdentity_injective_ae (n : ℕ) (c : Bool) (k : ℕ) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (Site n),
      Function.Injective (selectedIdentity n c k ω) := by
  filter_upwards [ClockEventOrder.distinct_selected_eventId_ae n c] with ω hω
  intro a b hab
  apply taskAt_injective n c k
  by_contra htask
  exact (hω _ _ _ _ (taskAt_selected n c k a) (taskAt_selected n c k b) htask) hab

def selectedMarks (n : ℕ) (c : Bool) (k : ℕ) (z : Sample n) :
    Fin (taskSet n c k).card → Bool := FairMarks.selected (selectedIdentity n c k) z

theorem selectedMarks_measurable (n : ℕ) (c : Bool) (k : ℕ) :
    Measurable (selectedMarks n c k) :=
  FairMarks.selected_measurable _ (selectedIdentity_measurable n c k)

/-- The complete selected vector has its actual finite fair product law. -/
theorem selectedMarks_hasLaw (n : ℕ) (c : Bool) (k : ℕ) :
    HasLaw (selectedMarks n c k) (FairMarks.vectorMeasure (taskSet n c k).card)
      (ClockWordMarks.measure n) :=
  FairMarks.selected_hasLaw (ExponentialClocks.clockMeasure (Site n))
    (selectedIdentity n c k) (selectedIdentity_measurable n c k)
    (selectedIdentity_injective_ae n c k)

/-- Independence holds from the full clock sample, and therefore every clock history. -/
theorem selectedMarks_indep_clock (n : ℕ) (c : Bool) (k : ℕ) :
    IndepFun (fun z : Sample n => z.1) (selectedMarks n c k)
      (ClockWordMarks.measure n) :=
  FairMarks.selected_indep_clock (ExponentialClocks.clockMeasure (Site n))
    (selectedIdentity n c k) (selectedIdentity_measurable n c k)
    (selectedIdentity_injective_ae n c k)

/-- Explicit factorization against any measurable event in the complete clock sample. -/
theorem selectedMarks_joint_measure (n : ℕ) (c : Bool) (k : ℕ)
    (E : Set (ClockSample n)) (hE : MeasurableSet E)
    (B : Set (Fin (taskSet n c k).card → Bool)) (hB : MeasurableSet B) :
    ClockWordMarks.measure n {z | z.1 ∈ E ∧ selectedMarks n c k z ∈ B} =
      ExponentialClocks.clockMeasure (Site n) E *
        FairMarks.vectorMeasure (taskSet n c k).card B :=
  FairMarks.selected_joint_measure (ExponentialClocks.clockMeasure (Site n))
    (selectedIdentity n c k) (selectedIdentity_measurable n c k) E hE
    ((selectedIdentity_injective_ae n c k).mono fun _ hi _ => hi) B hB

/-- In particular, every event observable in physical clock history has this factorization. -/
theorem selectedMarks_clockHistory_joint_measure (n : ℕ) (c : Bool) (k : ℕ) (s : ℝ)
    (E : Set (ClockSample n))
    (hE : MeasurableSet[ArrivalFiltration.clockHistory (Site n) s] E)
    (B : Set (Fin (taskSet n c k).card → Bool)) (hB : MeasurableSet B) :
    ClockWordMarks.measure n {z | z.1 ∈ E ∧ selectedMarks n c k z ∈ B} =
      ExponentialClocks.clockMeasure (Site n) E *
        FairMarks.vectorMeasure (taskSet n c k).card B :=
  selectedMarks_joint_measure n c k E
    ((ArrivalFiltration.clockHistory (Site n)).le s E hE) B hB

end MathResearchAnalysis.ClockSelectedMarks
