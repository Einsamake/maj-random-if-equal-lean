module

public import MathResearchAnalysis.FiniteObservedClockState
public import MathResearchAnalysis.PredictableClockSigma
public import MathResearchAnalysis.StrictClockPrefix
public import MathResearchAnalysis.ClockTimeNullGraph
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false

/-!
# Predictable strict-past state of an arbitrary finite marked-clock machine

The representative uses only rational observations strictly before time.
On one common set of original samples it agrees at every nonnegative time,
including random ringing times, with execution of the genuine strict word.
The current state and this predictable state agree away from actual rings.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.FiniteMachinePreState

open MeasureTheory Set
open DropletClockLaw (Sample Event Vertex)

universe u
variable {A : Type u}

def graph (L : Nat) (step : Vertex L → Bool → A → A) (initial a : A) :
    Set (NNReal × Sample L) :=
  {p | ∃ q : Rat, 0 ≤ q ∧ (q : Real) < (p.1 : Real) ∧
    ∀ r : Rat, q < r → (r : Real) < (p.1 : Real) →
      FiniteObservedClockState.state L step initial (r : Real) p.2 = a}

theorem rational_future_eq (L : Nat) (q : Rat) (hq : 0 ≤ q) (E : Set (Sample L)) :
    {p : NNReal × Sample L | (q : Real) < (p.1 : Real) ∧ p.2 ∈ E} =
      Ioi (Real.toNNReal (q : Real)) ×ˢ E := by
  ext p
  simp only [mem_ofPred_eq,mem_prod,mem_Ioi]
  rw [←NNReal.coe_lt_coe,Real.coe_toNNReal _ (by exact_mod_cast hq)]

theorem rational_future_measurable [Fintype A] (L : Nat) (step : Vertex L → Bool → A → A)
    (initial a : A) (r : Rat) (hr : 0 ≤ r) :
    MeasurableSet[(RationalProtectedExit.nnHistory L).predictable]
      {p : NNReal × Sample L | (r : Real) < (p.1 : Real) ∧
        FiniteObservedClockState.state L step initial (r : Real) p.2 ≠ a} := by
  change MeasurableSet[(RationalProtectedExit.nnHistory L).predictable]
    {p : NNReal × Sample L | (r : Real) < (p.1 : Real) ∧
      p.2 ∈ {z : Sample L | FiniteObservedClockState.state L step initial (r : Real) z ≠ a}}
  rw [rational_future_eq L r hr]
  apply measurableSet_predictable_Ioi_prod
  change MeasurableSet[MarkedClockFiltration.history L (Real.toNNReal (r : Real) : Real)]
    {z : Sample L | FiniteObservedClockState.state L step initial (r : Real) z ≠ a}
  rw [Real.coe_toNNReal _ (by exact_mod_cast hr)]
  exact (FiniteObservedClockState.state_fiber_measurable L step initial (r : Real) a).compl

theorem graph_measurable [Fintype A] (L : Nat) (step : Vertex L → Bool → A → A) (initial a : A) :
    MeasurableSet[(RationalProtectedExit.nnHistory L).predictable] (graph L step initial a) := by
  classical
  let : MeasurableSpace (NNReal × Sample L) := (RationalProtectedExit.nnHistory L).predictable
  have heq : graph L step initial a = ⋃ q : Rat, ⋃ hq : 0 ≤ q,
      (Ioi (Real.toNNReal (q : Real)) ×ˢ (univ : Set (Sample L))) ∩
      ⋂ r : Rat, if q < r then
        {p : NNReal × Sample L | (r : Real) < (p.1 : Real) ∧
          FiniteObservedClockState.state L step initial (r : Real) p.2 ≠ a}ᶜ else univ := by
    ext p
    simp only [graph,mem_ofPred_eq,mem_iUnion,mem_inter_iff,mem_prod,mem_univ,and_true,mem_Ioi,mem_iInter]
    constructor
    · rintro ⟨q,hq,hqt,hstate⟩
      refine ⟨q,hq,?_,?_⟩
      · rw [←NNReal.coe_lt_coe,Real.coe_toNNReal _ (by exact_mod_cast hq)]
        exact hqt
      · intro r
        by_cases hqr : q < r
        · simp only [hqr,ite_true,mem_compl_iff,mem_ofPred_eq]
          rintro ⟨hrt,hne⟩
          exact hne (hstate r hqr hrt)
        · simp only [hqr,ite_false,mem_univ]
    · rintro ⟨q,hq,hqt,hstate⟩
      refine ⟨q,hq,?_,?_⟩
      · rw [←NNReal.coe_lt_coe,Real.coe_toNNReal _ (by exact_mod_cast hq)] at hqt
        exact hqt
      · intro r hqr hrt
        have hs := hstate r
        simp only [hqr,ite_true,mem_compl_iff,mem_ofPred_eq] at hs
        by_contra hne
        exact hs ⟨hrt,hne⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro hq
  apply (measurableSet_predictable_Ioi_prod (𝓕 := RationalProtectedExit.nnHistory L)
    (i := Real.toNNReal (q : Real)) MeasurableSet.univ).inter
  apply MeasurableSet.iInter
  intro r
  split_ifs with hqr
  · exact (rational_future_measurable L step initial a r (le_trans hq (le_of_lt hqr))).compl
  · exact MeasurableSet.univ

theorem graph_unique (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (t : NNReal) (z : Sample L) (a b : A)
    (ha : (t,z) ∈ graph L step initial a) (hb : (t,z) ∈ graph L step initial b) : a = b := by
  rcases ha with ⟨q,hq,hqt,ha⟩
  rcases hb with ⟨s,hs,hst,hb⟩
  obtain ⟨r,hr,hrt⟩ := exists_rat_btwn (max_lt hqt hst)
  have hqr : q < r := by exact_mod_cast lt_of_le_of_lt (le_max_left (q : Real) (s : Real)) hr
  have hsr : s < r := by exact_mod_cast lt_of_le_of_lt (le_max_right (q : Real) (s : Real)) hr
  exact (ha r hqr hrt).symm.trans (hb r hsr hrt)

def beforeState (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (t : NNReal) (z : Sample L) : A := by
  classical
  exact if h : ∃ a, (t,z) ∈ graph L step initial a then h.choose else initial

theorem state_eq_of_graph (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (t : NNReal) (z : Sample L) (a : A) (ha : (t,z) ∈ graph L step initial a) :
    beforeState L step initial t z = a := by
  classical
  have hex : ∃ b, (t,z) ∈ graph L step initial b := ⟨a,ha⟩
  simp only [beforeState,dite_eq_left hex]
  exact graph_unique L step initial t z _ a hex.choose_spec ha

theorem state_eq_iff (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (t : NNReal) (z : Sample L) (a : A) :
    beforeState L step initial t z = a ↔ (t,z) ∈ graph L step initial a ∨
      (¬ (∃ b, (t,z) ∈ graph L step initial b)) ∧ initial = a := by
  classical
  by_cases hex : ∃ b, (t,z) ∈ graph L step initial b
  · have hg : (t,z) ∈ graph L step initial (beforeState L step initial t z) := by
      simpa only [beforeState,dite_eq_left hex] using hex.choose_spec
    exact ⟨fun h => Or.inl (h ▸ hg),fun h => h.elim
      (state_eq_of_graph L step initial t z a) (fun h => False.elim (h.1 hex))⟩
  · simp only [beforeState,dite_eq_right hex]
    constructor
    · exact fun h => Or.inr ⟨hex,h⟩
    · rintro (h | h)
      · exact False.elim (hex ⟨a,h⟩)
      · exact h.2

theorem state_fiber_measurable [Fintype A] (L : Nat) (step : Vertex L → Bool → A → A) (initial a : A) :
    MeasurableSet[(RationalProtectedExit.nnHistory L).predictable]
      {p : NNReal × Sample L | beforeState L step initial p.1 p.2 = a} := by
  let : MeasurableSpace (NNReal × Sample L) := (RationalProtectedExit.nnHistory L).predictable
  have heq : {p : NNReal × Sample L | beforeState L step initial p.1 p.2 = a} = graph L step initial a ∪
      (⋃ b : A, graph L step initial b)ᶜ ∩ {p : NNReal × Sample L | initial = a} := by
    ext p
    simp only [mem_ofPred_eq,state_eq_iff,mem_union,mem_inter_iff,mem_compl_iff,mem_iUnion]
  rw [heq]
  exact (graph_measurable L step initial a).union
    ((MeasurableSet.iUnion fun b => graph_measurable L step initial b).compl.inter (MeasurableSet.const _))

theorem state_measurable [Fintype A] (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) :
    @Measurable (NNReal × Sample L) A (RationalProtectedExit.nnHistory L).predictable
      (FiniteObservedClockState.stateSpace A) (fun p => beforeState L step initial p.1 p.2) := by
  let : MeasurableSpace (NNReal × Sample L) := (RationalProtectedExit.nnHistory L).predictable
  let : MeasurableSpace A := FiniteObservedClockState.stateSpace A
  exact measurable_to_countable' fun a => state_fiber_measurable L step initial a

theorem observable_measurable [Fintype A] (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    {B : Type*} [MeasurableSpace B] (F : A → B) :
    @Measurable (NNReal × Sample L) B (RationalProtectedExit.nnHistory L).predictable
      inferInstance (fun p => F (beforeState L step initial p.1 p.2)) := by
  let : MeasurableSpace A := FiniteObservedClockState.stateSpace A
  have hF : Measurable F := fun _ _ => trivial
  exact hF.comp (state_measurable L step initial)

theorem state_measurable_ambient [Fintype A] (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) :
    @Measurable (NNReal × Sample L) A inferInstance
      (FiniteObservedClockState.stateSpace A) (fun p => beforeState L step initial p.1 p.2) :=
  (state_measurable L step initial).mono (PredictableClockSigma.predictable_le_ambient L) le_rfl

theorem state_zero (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) (z : Sample L) :
    beforeState L step initial 0 z = initial := by
  classical
  have hnone : ¬ ∃ a, ((0 : NNReal),z) ∈ graph L step initial a := by
    rintro ⟨a,q,hq,hlt,hstate⟩
    have hqreal : (0 : Real) ≤ (q : Real) := by exact_mod_cast hq
    exact (not_lt_of_ge hqreal) hlt
  simp only [beforeState,dite_eq_right hnone]

def strictStateAt (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (t : Real) (z : Sample L) : A :=
  EventTrace.execute (fun e : Event L => step e.1 (z.2 e))
    (StrictClockPrefix.strictWord z.1 t).reverse initial

theorem marked_all_events_positive_ae (L : Nat) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e :=
  (Measure.quasiMeasurePreserving_fst
    (μ := ExponentialClocks.clockMeasure (Vertex L))
    (ν := FairMarks.markMeasure (Event L))).ae
      (ClockEventWord.eventTime_positive_ae (V := Vertex L))

theorem strictStateAt_zero (L : Nat) (step : Vertex L → Bool → A → A)
    (initial : A) (z : Sample L) (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) :
    strictStateAt L step initial 0 z = initial := by
  simp only [strictStateAt,StrictClockPrefix.strictWord_zero_of_positive z.1 hp,
    List.reverse_nil,EventTrace.execute_nil]

theorem beforeState_eq_strictStateAt_pos (L : Nat) (step : Vertex L → Bool → A → A)
    (initial : A) (z : Sample L) (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (t : NNReal) (ht : 0 < t) :
    beforeState L step initial t z = strictStateAt L step initial (t : Real) z := by
  obtain ⟨a,ha0,hat,hgap⟩ := StrictClockPrefix.word_left_locally_strict z.1 (t : Real)
    (hg (t : Real)) (by exact_mod_cast ht)
  obtain ⟨q,haq,hqt⟩ := exists_rat_btwn hat
  apply state_eq_of_graph L step initial t z _
  refine ⟨q,?_,hqt,?_⟩
  · exact_mod_cast (ha0.trans haq.le)
  · intro r hqr hrt
    rw [FiniteObservedClockState.state_eq_endpoint L step initial (r : Real) z (hg _)]
    unfold FiniteObservedClockState.endpoint strictStateAt
    rw [hgap (r : Real) (haq.trans (by exact_mod_cast hqr)) hrt]

theorem beforeState_eq_strictStateAt (L : Nat) (step : Vertex L → Bool → A → A)
    (initial : A) (z : Sample L) (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) (t : NNReal) :
    beforeState L step initial t z = strictStateAt L step initial (t : Real) z := by
  by_cases ht : t = 0
  · subst t
    rw [state_zero]
    exact (strictStateAt_zero L step initial z hp).symm
  · exact beforeState_eq_strictStateAt_pos L step initial z hg t (lt_of_le_of_ne bot_le (Ne.symm ht))

/-- One original-law exceptional set works at all times, including random rings. -/
theorem beforeState_all_times_ae (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ t : NNReal,
      beforeState L step initial t z = strictStateAt L step initial (t : Real) z := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L,
    marked_all_events_positive_ae L] with z hg hp
  exact fun t => beforeState_eq_strictStateAt L step initial z hg hp t

theorem strictStateAt_event_update (L : Nat) (step : Vertex L → Bool → A → A)
    (initial : A) (z : Sample L) (e : Event L)
    (hg : ClockEventWord.Good z.1 (ClockEventWord.eventTime z.1 e)) :
    FiniteObservedClockState.endpoint L step initial (ClockEventWord.eventTime z.1 e) z =
      step e.1 (z.2 e) (strictStateAt L step initial (ClockEventWord.eventTime z.1 e) z) := by
  unfold FiniteObservedClockState.endpoint strictStateAt
  rw [StrictClockPrefix.word_at_event_eq_cons_strict z.1 e hg]
  simp only [List.reverse_cons,EventTrace.execute_append,EventTrace.execute_cons,EventTrace.execute_nil]

theorem stateAt_event_update (L : Nat) (step : Vertex L → Bool → A → A)
    (initial : A) (z : Sample L) (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) (e : Event L) :
    FiniteObservedClockState.endpoint L step initial (ClockEventWord.eventTime z.1 e) z =
      step e.1 (z.2 e)
        (beforeState L step initial (ClockEventWord.eventTime z.1 e).toNNReal z) := by
  rw [beforeState_eq_strictStateAt L step initial z hg hp,Real.coe_toNNReal _ (hp e).le]
  exact strictStateAt_event_update L step initial z e (hg _)

theorem stateAt_all_events_update_ae (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ e : Event L,
      FiniteObservedClockState.endpoint L step initial (ClockEventWord.eventTime z.1 e) z =
        step e.1 (z.2 e)
          (beforeState L step initial (ClockEventWord.eventTime z.1 e).toNNReal z) := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L,
    marked_all_events_positive_ae L] with z hg hp
  exact fun e => stateAt_event_update L step initial z hg hp e

theorem observedState_all_events_update_ae (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ e : Event L,
      FiniteObservedClockState.state L step initial (ClockEventWord.eventTime z.1 e) z =
        step e.1 (z.2 e)
          (beforeState L step initial (ClockEventWord.eventTime z.1 e).toNNReal z) := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L,
    stateAt_all_events_update_ae L step initial] with z hg he
  intro e
  rw [FiniteObservedClockState.state_eq_endpoint L step initial _ z (hg _)]
  exact he e

/-- At a non-ringing time, strict and current actual words coincide. -/
theorem strictWord_eq_word_of_no_event {V : Type*} (ω : ExponentialClocks.Sample V)
    (t : Real) (hg : ClockEventWord.Good ω t)
    (hne : ∀ e : ClockEventWord.Event V, ClockEventWord.eventTime ω e ≠ t) :
    StrictClockPrefix.strictWord ω t = ClockEventWord.word ω t := by
  unfold StrictClockPrefix.strictWord
  apply List.filter_eq_self.mpr
  intro e he
  simp only [decide_eq_true_eq]
  have hle := (ClockEventWord.word_mem_iff ω t hg e).mp he
  exact lt_of_le_of_ne hle (hne e)

theorem beforeState_eq_endpoint_of_no_event (L : Nat) (step : Vertex L → Bool → A → A)
    (initial : A) (z : Sample L) (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) (t : NNReal)
    (hne : ∀ e : Event L, ClockEventWord.eventTime z.1 e ≠ (t : Real)) :
    beforeState L step initial t z = FiniteObservedClockState.endpoint L step initial (t : Real) z := by
  rw [beforeState_eq_strictStateAt L step initial z hg hp]
  unfold strictStateAt FiniteObservedClockState.endpoint
  rw [strictWord_eq_word_of_no_event z.1 (t : Real) (hg _) hne]

theorem beforeState_current_eq_of_no_event (L : Nat) (step : Vertex L → Bool → A → A)
    (initial : A) (z : Sample L) (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) (t : NNReal)
    (hne : ∀ e : Event L, ClockEventWord.eventTime z.1 e ≠ (t : Real)) :
    beforeState L step initial t z = FiniteObservedClockState.state L step initial (t : Real) z := by
  rw [beforeState_eq_strictStateAt L step initial z hg hp,
    FiniteObservedClockState.state_eq_endpoint L step initial (t : Real) z (hg _)]
  unfold strictStateAt FiniteObservedClockState.endpoint
  rw [strictWord_eq_word_of_no_event z.1 (t : Real) (hg _) hne]

/-- For each original regular path, only its countable actual event times can differ.
This is an iterated AE statement, without assuming joint current-state measurability. -/
theorem beforeState_current_ae_time (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      ∀ᵐ t : Real ∂volume, 0 ≤ t → beforeState L step initial t.toNNReal z =
        FiniteObservedClockState.state L step initial t z := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L,
    marked_all_events_positive_ae L] with z hg hp
  filter_upwards [(Set.countable_range (ClockEventWord.eventTime z.1)).ae_notMem (volume : Measure Real)] with t ht
  intro ht0
  have hne : ∀ e : Event L, ClockEventWord.eventTime z.1 e ≠ (t.toNNReal : Real) := by
    intro e he
    apply ht
    refine ⟨e,?_⟩
    simpa only [Real.coe_toNNReal _ ht0] using he
  simpa only [Real.coe_toNNReal _ ht0] using
    beforeState_current_eq_of_no_event L step initial z hg hp t.toNNReal hne

/-- True Lebesgue-time then original-law AE equality, with no assumed stochastic
compensation or joint-current-state identity. Actual event graphs are null. -/
theorem beforeState_eq_endpoint_time_ae (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) :
    ∀ᵐ t : Real ∂volume, ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      0 ≤ t → beforeState L step initial t.toNNReal z =
        FiniteObservedClockState.endpoint L step initial t z := by
  filter_upwards [ClockTimeNullGraph.clock_time_sample_ae_no_event
    (ClippedSquareCoordinates.parameter L)] with t ht
  filter_upwards [ht,ClockWordConsistency.marked_sample_good_ae L,
    marked_all_events_positive_ae L] with z hne hg hp
  intro ht0
  have hne' : ∀ e : Event L, ClockEventWord.eventTime z.1 e ≠ (t.toNNReal : Real) := by
    intro e he
    apply hne e
    simpa only [Real.coe_toNNReal _ ht0] using he
  simpa only [Real.coe_toNNReal _ ht0] using
    beforeState_eq_endpoint_of_no_event L step initial z hg hp t.toNNReal hne'

end MathResearchAnalysis.FiniteMachinePreState



