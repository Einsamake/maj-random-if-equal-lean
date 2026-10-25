module

public import MathResearchAnalysis.ObservedProgressive
public import MathResearchAnalysis.EventTrace

set_option autoImplicit false

/-!
# Genuine observed histories of an arbitrary finite marked-clock machine

The actual joint clock and identity-mark law is unchanged. States are
reconstructed from finite past fibers on every sample; the guarded total word
is used only for the actual endpoint and for its common almost-sure equality.
No recentering, cleanup, freezing, generator, or probability bound is assumed.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.FiniteObservedClockState

open MeasureTheory
open DropletClockLaw (Sample Event Vertex)
open MarkedHistoryWords (fiber)

universe u
variable {A : Type u}

/-- The discrete measurable structure of the finite machine state. -/
abbrev stateSpace (A : Type u) : MeasurableSpace A := ⊤

/-- Execute a chronological identity list with its prescribed finite marks.
The identity outside the list is never consulted, and the list is not reversed. -/
def runMarked (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (l : List (Event L)) (ξ : Fin l.length → Bool) : A :=
  EventTrace.execute (fun e a => step e.1 (ClockExecutionLaw.freshMarks l ξ e) a) l initial

/-- The actual original marked endpoint, executing the newest-first word in
chronological order exactly once. -/
def endpoint (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (t : Real) (z : Sample L) : A :=
  EventTrace.execute (fun e a => step e.1 (z.2 e) a)
    (ClockEventWord.word z.1 t).reverse initial

theorem execute_eq_of_marks_agree (L : Nat) (step : Vertex L → Bool → A → A)
    (η ξ : Event L → Bool) (l : List (Event L))
    (h : ∀ e ∈ l, η e = ξ e) (initial : A) :
    EventTrace.execute (fun e a => step e.1 (η e) a) l initial =
      EventTrace.execute (fun e a => step e.1 (ξ e) a) l initial := by
  induction l generalizing initial with
  | nil => rfl
  | cons e l ih =>
    simp only [EventTrace.execute_cons,h e List.mem_cons_self]
    exact ih (fun a ha => h a (List.mem_cons_of_mem _ ha)) _

/-- Finite marks from a genuine identity field reconstruct its true execution. -/
theorem runMarked_eq_execute (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (l : List (Event L)) (ξ : Fin l.length → Bool) (η : Event L → Bool)
    (hmark : ∀ i : Fin l.length, η l[i] = ξ i) :
    runMarked L step initial l ξ = EventTrace.execute (fun e a => step e.1 (η e) a) l initial := by
  have hξ : ξ = ClockExecutionLaw.fixedVector l η := funext (fun i => (hmark i).symm)
  rw [hξ]
  exact execute_eq_of_marks_agree L step _ _ l
    (fun e he => ClockExecutionLaw.freshMarks_fixedVector l η e he) initial

theorem runMarked_measurable (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (l : List (Event L)) :
    @Measurable (Fin l.length → Bool) A inferInstance (stateSpace A)
      (runMarked L step initial l) := by
  let : MeasurableSpace A := stateSpace A
  exact measurable_of_countable _

theorem fixedRun_measurable (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (l : List (Event L)) :
    @Measurable (Event L → Bool) A inferInstance (stateSpace A)
      (fun η => EventTrace.execute (fun e a => step e.1 (η e) a) l initial) := by
  let : MeasurableSpace A := stateSpace A
  have h := (runMarked_measurable L step initial l).comp
    (ClockExecutionLaw.fixedVector_measurable l)
  have he : (fun η : Event L → Bool => runMarked L step initial l
      (ClockExecutionLaw.fixedVector l η)) =
      (fun η => EventTrace.execute (fun e a => step e.1 (η e) a) l initial) := by
    funext η
    exact runMarked_eq_execute L step initial l _ η (fun _ => rfl)
  change Measurable (fun η => runMarked L step initial l (ClockExecutionLaw.fixedVector l η)) at h
  rw [he] at h
  exact h

theorem endpoint_measurable (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (t : Real) : @Measurable (Sample L) A inferInstance (stateSpace A)
      (endpoint L step initial t) := by
  let : MeasurableSpace A := stateSpace A
  have hrun : Measurable (fun p : List (Event L) × FairMarks.Sample (Event L) =>
      EventTrace.execute (fun e a => step e.1 (p.2 e) a) p.1.reverse initial) :=
    measurable_from_prod_countable_right (fun l => fixedRun_measurable L step initial l.reverse)
  exact hrun.comp (((ClockEventWord.word_measurable t).comp measurable_fst).prodMk measurable_snd)

/-- A true finite observed history determines its machine state. -/
def graph (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) (t : Real) (a : A) :
    Set (Sample L) :=
  {z | ∃ l : List (Event L), ∃ ξ : Fin l.length → Bool,
    fiber L t l ξ z ∧ runMarked L step initial l ξ = a}

theorem graph_measurable (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (t : Real) (a : A) :
    MeasurableSet[MarkedClockFiltration.history L t] (graph L step initial t a) := by
  let : MeasurableSpace (Sample L) := MarkedClockFiltration.history L t
  have heq : graph L step initial t a = ⋃ l : List (Event L), ⋃ ξ : Fin l.length → Bool,
      {z | fiber L t l ξ z} ∩ {z : Sample L | runMarked L step initial l ξ = a} := by
    ext z
    simp only [graph,Set.mem_iUnion,Set.mem_inter_iff,Set.mem_ofPred_eq]
  rw [heq]
  exact MeasurableSet.iUnion fun l => MeasurableSet.iUnion fun ξ =>
    (MarkedHistoryWords.fiber_measurable L t l ξ).inter (MeasurableSet.const _)

theorem fiber_runs_eq (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (t : Real) (z : Sample L) (l k : List (Event L))
    (ξ : Fin l.length → Bool) (η : Fin k.length → Bool)
    (hl : fiber L t l ξ z) (hk : fiber L t k η z) :
    runMarked L step initial l ξ = runMarked L step initial k η := by
  rw [runMarked_eq_execute L step initial l ξ z.2 (fun i => (hl.2.2 i).2),
    runMarked_eq_execute L step initial k η z.2 (fun i => (hk.2.2 i).2),
    ObservedFrozenProcess.fiber_lists_eq L t z l k ξ η hl hk]

theorem graph_unique (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (t : Real) (z : Sample L) (a b : A)
    (ha : z ∈ graph L step initial t a) (hb : z ∈ graph L step initial t b) : a = b := by
  rcases ha with ⟨l,ξ,hl,ha⟩
  rcases hb with ⟨k,η,hk,hb⟩
  rw [←ha,←hb]
  exact fiber_runs_eq L step initial t z l k ξ η hl hk

/-- A total, genuinely history-measurable representative. Invalid observed
histories return the specified initial state rather than querying global Good. -/
def state (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (t : Real) (z : Sample L) : A := by
  classical
  exact if h : ∃ a : A, z ∈ graph L step initial t a then h.choose else initial

theorem state_eq_of_graph (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (t : Real) (z : Sample L) (a : A) (ha : z ∈ graph L step initial t a) :
    state L step initial t z = a := by
  classical
  have hex : ∃ b : A, z ∈ graph L step initial t b := ⟨a,ha⟩
  simp only [state,dite_eq_left hex]
  exact graph_unique L step initial t z _ a hex.choose_spec ha

theorem state_eq_iff (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (t : Real) (z : Sample L) (a : A) :
    state L step initial t z = a ↔ z ∈ graph L step initial t a ∨
      (¬ (∃ b : A, z ∈ graph L step initial t b)) ∧ initial = a := by
  classical
  by_cases hex : ∃ b : A, z ∈ graph L step initial t b
  · have hg : z ∈ graph L step initial t (state L step initial t z) := by
      simpa only [state,dite_eq_left hex] using hex.choose_spec
    exact ⟨fun h => Or.inl (h ▸ hg),fun h => h.elim
      (state_eq_of_graph L step initial t z a) (fun h => False.elim (h.1 hex))⟩
  · simp only [state,dite_eq_right hex]
    constructor
    · exact fun h => Or.inr ⟨hex,h⟩
    · rintro (h | h)
      · exact False.elim (hex ⟨a,h⟩)
      · exact h.2

theorem graph_endpoint (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (t : Real) (z : Sample L) (hg : ClockEventWord.Good z.1 t) :
    z ∈ graph L step initial t (endpoint L step initial t z) := by
  let l := (ClockEventWord.word z.1 t).reverse
  let ξ : Fin l.length → Bool := fun i => z.2 l[i]
  have hcov : ∀ e : Event L, e ∈ l ↔ ClockEventWord.eventTime z.1 e ≤ t := by
    intro e
    exact List.mem_reverse.trans (ClockEventWord.word_mem_iff z.1 t hg e)
  have hf : fiber L t l ξ z := ⟨hcov,MarkedHistoryWords.chronological_ordered L t z hg,
    fun i => ⟨(hcov l[i]).mp (List.getElem_mem _),rfl⟩⟩
  refine ⟨l,ξ,hf,?_⟩
  exact runMarked_eq_execute L step initial l ξ z.2 (fun _ => rfl)

theorem state_eq_endpoint (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (t : Real) (z : Sample L) (hg : ClockEventWord.Good z.1 t) :
    state L step initial t z = endpoint L step initial t z :=
  state_eq_of_graph L step initial t z _ (graph_endpoint L step initial t z hg)

/-- One original-law full-probability set works simultaneously at all times. -/
theorem state_all_times_ae (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ t : Real,
      state L step initial t z = endpoint L step initial t z := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L] with z hz
  exact fun t => state_eq_endpoint L step initial t z (hz t)

theorem variable_graph_measurable (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (t : Real) (a : A) :
    MeasurableSet[ObservedProgressive.pastProduct L t]
      {p : Set.Iic t × Sample L | p.2 ∈ graph L step initial (p.1 : Real) a} := by
  let : MeasurableSpace (Sample L) := MarkedClockFiltration.history L t
  have heq : {p : Set.Iic t × Sample L | p.2 ∈ graph L step initial (p.1 : Real) a} =
      ⋃ l : List (Event L), ⋃ ξ : Fin l.length → Bool,
      {p : Set.Iic t × Sample L | fiber L (p.1 : Real) l ξ p.2} ∩
      {p : Set.Iic t × Sample L | runMarked L step initial l ξ = a} := by
    ext p
    simp only [graph,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff]
  rw [heq]
  exact MeasurableSet.iUnion fun l => MeasurableSet.iUnion fun ξ =>
    (ObservedProgressive.variable_fiber_measurable L t l ξ).inter (MeasurableSet.const _)

/-- Ambient joint measurability of chronological ordering at a variable time. -/
theorem ordered_joint_measurable (L : Nat) (l : List (Event L)) :
    MeasurableSet {p : Real × Sample L | MarkedHistoryWords.ordered L p.1 l p.2} := by
  have hc (e : Event L) : Measurable (fun p : Real × Sample L =>
      MarkedHistoryWords.censoredArrival L p.1 e p.2) :=
    ((MarkedClockFiltration.arrival_measurable L e).comp measurable_snd).min measurable_fst
  induction l with
  | nil =>
    have heq : {p : Real × Sample L | MarkedHistoryWords.ordered L p.1 [] p.2} = Set.univ := by
      ext p
      exact ⟨fun _ => Set.mem_univ p,fun _ => List.Pairwise.nil⟩
    rw [heq]
    exact MeasurableSet.univ
  | cons e l ih =>
    have heq : {p : Real × Sample L | MarkedHistoryWords.ordered L p.1 (e::l) p.2} =
        (⋂ b : Event L, ⋂ (_ : b ∈ l), {p : Real × Sample L |
          MarkedHistoryWords.censoredArrival L p.1 e p.2 <
            MarkedHistoryWords.censoredArrival L p.1 b p.2}) ∩
        {p : Real × Sample L | MarkedHistoryWords.ordered L p.1 l p.2} := by
      ext p
      simp only [MarkedHistoryWords.ordered,List.pairwise_cons,
        Set.mem_inter_iff,Set.mem_iInter,Set.mem_ofPred_eq]
    rw [heq]
    exact (MeasurableSet.iInter fun b => MeasurableSet.iInter fun _ =>
      measurableSet_lt (hc e) (hc b)).inter ih

/-- The genuine finite past fiber is also ambient-jointly measurable. -/
theorem fiber_joint_measurable (L : Nat) (l : List (Event L)) (ξ : Fin l.length → Bool) :
    MeasurableSet {p : Real × Sample L | fiber L p.1 l ξ p.2} := by
  have ha (e : Event L) : Measurable (fun p : Real × Sample L => ClockEventWord.eventTime p.2.1 e) :=
    (MarkedClockFiltration.arrival_measurable L e).comp measurable_snd
  have hm (e : Event L) : Measurable (fun p : Real × Sample L => p.2.2 e) :=
    (MarkedClockFiltration.mark_measurable L e).comp measurable_snd
  have heq : {p : Real × Sample L | fiber L p.1 l ξ p.2} =
      (⋂ e : Event L, {p : Real × Sample L | e ∈ l ↔ ClockEventWord.eventTime p.2.1 e ≤ p.1}) ∩
      ({p : Real × Sample L | MarkedHistoryWords.ordered L p.1 l p.2} ∩
        ⋂ i : Fin l.length, {p : Real × Sample L |
          ClockEventWord.eventTime p.2.1 l[i] ≤ p.1 ∧ p.2.2 l[i] = ξ i}) := by
    ext p
    simp only [fiber,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]
  rw [heq]
  exact (MeasurableSet.iInter fun e => (MeasurableSet.const (e ∈ l)).iff
    (measurableSet_le (ha e) measurable_fst)).inter
    ((ordered_joint_measurable L l).inter (MeasurableSet.iInter fun i =>
      (measurableSet_le (ha l[i]) measurable_fst).inter (measurableSet_eq_fun (hm l[i]) measurable_const)))

theorem graph_joint_measurable (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) (a : A) :
    MeasurableSet {p : Real × Sample L | p.2 ∈ graph L step initial p.1 a} := by
  have heq : {p : Real × Sample L | p.2 ∈ graph L step initial p.1 a} =
      ⋃ l : List (Event L), ⋃ ξ : Fin l.length → Bool,
        {p : Real × Sample L | fiber L p.1 l ξ p.2} ∩
          {p : Real × Sample L | runMarked L step initial l ξ = a} := by
    ext p
    simp only [graph,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff]
  rw [heq]
  exact MeasurableSet.iUnion fun l => MeasurableSet.iUnion fun ξ =>
    (fiber_joint_measurable L l ξ).inter (MeasurableSet.const _)
section Finite
variable [Fintype A]

theorem state_fiber_measurable (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (t : Real) (a : A) :
    MeasurableSet[MarkedClockFiltration.history L t] {z | state L step initial t z = a} := by
  let : MeasurableSpace (Sample L) := MarkedClockFiltration.history L t
  have heq : {z : Sample L | state L step initial t z = a} = graph L step initial t a ∪
      (⋃ b : A, graph L step initial t b)ᶜ ∩ {z : Sample L | initial = a} := by
    ext z
    simp only [Set.mem_ofPred_eq,state_eq_iff,Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff,
      Set.mem_iUnion]
  rw [heq]
  exact (graph_measurable L step initial t a).union
    ((MeasurableSet.iUnion (fun b => graph_measurable L step initial t b)).compl.inter (MeasurableSet.const _))

theorem state_measurable (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) (t : Real) :
    @Measurable (Sample L) A (MarkedClockFiltration.history L t) (stateSpace A)
      (state L step initial t) := by
  let : MeasurableSpace (Sample L) := MarkedClockFiltration.history L t
  let : MeasurableSpace A := stateSpace A
  exact measurable_to_countable' fun a => state_fiber_measurable L step initial t a

theorem observable_measurable (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) (t : Real)
    {B : Type*} [MeasurableSpace B] (F : A → B) :
    @Measurable (Sample L) B (MarkedClockFiltration.history L t) inferInstance
      (fun z => F (state L step initial t z)) := by
  let : MeasurableSpace A := stateSpace A
  have hF : Measurable F := fun _ _ => trivial
  exact hF.comp (state_measurable L step initial t)

theorem state_isProgressive (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) :
    letI : MeasurableSpace A := stateSpace A
    IsProgressive (MarkedClockFiltration.history L) (state L step initial) := by
  let : MeasurableSpace A := stateSpace A
  intro t
  let : MeasurableSpace (Sample L) := MarkedClockFiltration.history L t
  apply measurable_to_countable'
  intro a
  have heq : (fun p : Set.Iic t × Sample L => state L step initial (p.1 : Real) p.2) ⁻¹' {a} =
      {p : Set.Iic t × Sample L | p.2 ∈ graph L step initial (p.1 : Real) a} ∪
      (⋃ b : A, {p : Set.Iic t × Sample L | p.2 ∈ graph L step initial (p.1 : Real) b})ᶜ ∩
        {p : Set.Iic t × Sample L | initial = a} := by
    ext p
    simp only [Set.mem_preimage,Set.mem_singleton_iff,state_eq_iff,
      Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_iUnion,Set.mem_ofPred_eq]
  rw [heq]
  exact (variable_graph_measurable L step initial t a).union
    ((MeasurableSet.iUnion (fun b => variable_graph_measurable L step initial t b)).compl.inter
      (MeasurableSet.const _))

theorem state_isProgressive_nn (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) :
    letI : MeasurableSpace A := stateSpace A
    IsProgressive (RationalProtectedExit.nnHistory L)
      (fun t : NNReal => state L step initial (t : Real)) := by
  let : MeasurableSpace A := stateSpace A
  intro t
  let : MeasurableSpace (Sample L) := MarkedClockFiltration.history L (t : Real)
  have hm : Measurable (fun p : Set.Iic t × Sample L =>
      ((⟨((p.1 : NNReal) : Real),by exact_mod_cast p.1.prop⟩ : Set.Iic (t : Real)),p.2)) := by
    exact (((measurable_coe_nnreal_real.comp measurable_subtype_coe).comp measurable_fst).subtype_mk).prodMk
      measurable_snd
  exact (state_isProgressive L step initial (t : Real)).comp hm

/-- All-sample ambient joint measurability, without claiming the guarded total
endpoint itself is history adapted. -/
theorem state_joint_measurable (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) :
    @Measurable (Real × Sample L) A inferInstance (stateSpace A)
      (fun p => state L step initial p.1 p.2) := by
  let : MeasurableSpace A := stateSpace A
  apply measurable_to_countable'
  intro a
  have heq : (fun p : Real × Sample L => state L step initial p.1 p.2) ⁻¹' {a} =
      {p : Real × Sample L | p.2 ∈ graph L step initial p.1 a} ∪
      (⋃ b : A, {p : Real × Sample L | p.2 ∈ graph L step initial p.1 b})ᶜ ∩
        {p : Real × Sample L | initial = a} := by
    ext p
    simp only [Set.mem_preimage,Set.mem_singleton_iff,state_eq_iff,
      Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_iUnion,Set.mem_ofPred_eq]
  rw [heq]
  exact (graph_joint_measurable L step initial a).union
    ((MeasurableSet.iUnion (fun b => graph_joint_measurable L step initial b)).compl.inter
      (MeasurableSet.const _))
end Finite
end MathResearchAnalysis.FiniteObservedClockState

