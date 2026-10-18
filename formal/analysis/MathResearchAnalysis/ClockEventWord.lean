module

public import MathResearchAnalysis.ClockNoTies
public import Mathlib.Data.List.Sort
public import Mathlib.Logic.Equiv.List

set_option autoImplicit false

/-!
# The finite word of genuine clock events

Events retain their `(site, arrival-index)` identity. On the common almost-sure
set supplied by the actual exponential clocks, the word contains exactly all
arrivals by a real time bound, newest first. The construction is total: it uses
the empty word if the bounded event set is infinite or the sample has ties.
Neither local finiteness nor absence of ties is an input to the probabilistic
conclusions below. The chronological representatives equal the raw exponential
partial sums almost surely, and their positivity is proved from positive gaps.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace MathResearchAnalysis.ClockEventWord

variable {V : Type*}

/-- A clock ring, retaining both its site and its zero-based arrival index. -/
abbrev Event (V : Type*) := V × Nat

/-- Event words carry the discrete measurable structure. -/
instance eventListMeasurableSpace (V : Type*) : MeasurableSpace (List (Event V)) := ⊤

instance eventListMeasurableSingletonClass (V : Type*) :
    MeasurableSingletonClass (List (Event V)) := ⟨fun _ => trivial⟩

/-- The total chronological representative of the genuine ring time. -/
def eventTime (ω : ExponentialClocks.Sample V) (e : Event V) : ℝ :=
  ArrivalFiltration.chronologicalArrival e.1 e.2 ω

/-- All actual event identities whose chronological time is at most `t`. -/
def eventSet (ω : ExponentialClocks.Sample V) (t : ℝ) : Set (Event V) :=
  {e | eventTime ω e ≤ t}

/-- The exceptional fallback is used only outside this explicitly defined set. -/
def Good (ω : ExponentialClocks.Sample V) (t : ℝ) : Prop :=
  (eventSet ω t).Finite ∧ Function.Injective (eventTime ω)

/-- The complete bounded-time event word, with the newest event first. -/
def word (ω : ExponentialClocks.Sample V) (t : ℝ) : List (Event V) := by
  classical
  exact if h : Good ω t then
    h.1.toFinset.toList.mergeSort (fun a b => decide (eventTime ω b ≤ eventTime ω a))
  else []

theorem word_eq_empty_of_not_good (ω : ExponentialClocks.Sample V) (t : ℝ)
    (h : ¬ Good ω t) : word ω t = [] := by
  simp only [word, dite_eq_right h]

theorem word_perm (ω : ExponentialClocks.Sample V) (t : ℝ) (h : Good ω t) :
    (word ω t).Perm h.1.toFinset.toList := by
  simp only [word, dite_eq_left h]
  exact List.mergeSort_perm _ _

theorem word_mem_iff (ω : ExponentialClocks.Sample V) (t : ℝ) (h : Good ω t)
    (e : Event V) : e ∈ word ω t ↔ e ∈ eventSet ω t := by
  classical
  rw [(word_perm ω t h).mem_iff, Finset.mem_toList, Set.Finite.mem_toFinset]

theorem word_nodup (ω : ExponentialClocks.Sample V) (t : ℝ) :
    (word ω t).Nodup := by
  classical
  by_cases h : Good ω t
  · exact (word_perm ω t h).nodup_iff.mpr h.1.toFinset.nodup_toList
  · rw [word_eq_empty_of_not_good ω t h]
    exact List.nodup_nil

theorem word_decreasing (ω : ExponentialClocks.Sample V) (t : ℝ) :
    (word ω t).Pairwise (fun a b => eventTime ω b ≤ eventTime ω a) := by
  classical
  by_cases h : Good ω t
  · simp only [word, dite_eq_left h]
    have hs := List.pairwise_mergeSort
      (le := fun a b : Event V => decide (eventTime ω b ≤ eventTime ω a))
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact hbc.trans hab)
      (fun a b => by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact le_total _ _) h.1.toFinset.toList
    simpa only [decide_eq_true_eq] using hs
  · rw [word_eq_empty_of_not_good ω t h]
    exact List.Pairwise.nil

/-- Strict chronological ordering holds even on exceptional samples, whose word is empty. -/
theorem word_strictly_decreasing (ω : ExponentialClocks.Sample V) (t : ℝ) :
    (word ω t).Pairwise (fun a b => eventTime ω b < eventTime ω a) := by
  classical
  by_cases h : Good ω t
  · exact (word_decreasing ω t).imp₂
      (fun a b hab hne => lt_of_le_of_ne hab (fun heq => hne (h.2 heq.symm)))
      (word_nodup ω t)
  · rw [word_eq_empty_of_not_good ω t h]
    exact List.Pairwise.nil

theorem word_reverse_strictly_increasing (ω : ExponentialClocks.Sample V) (t : ℝ) :
    (word ω t).reverse.Pairwise (fun a b => eventTime ω a < eventTime ω b) :=
  (word_strictly_decreasing ω t).reverse

theorem sublist_reverse_strictly_increasing (ω : ExponentialClocks.Sample V) (t : ℝ)
    {l : List (Event V)} (hl : l.Sublist (word ω t).reverse) :
    l.Pairwise (fun a b => eventTime ω a < eventTime ω b) :=
  (word_reverse_strictly_increasing ω t).sublist hl

theorem eventTime_measurable (e : Event V) : Measurable (fun ω => eventTime ω e) :=
  ArrivalFiltration.chronologicalArrival_measurable e.1 e.2

theorem eventTime_eq_raw_ae [Countable V] :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ e : Event V,
      eventTime ω e = ExponentialClocks.arrival e.1 e.2 ω := by
  filter_upwards [ArrivalFiltration.chronologicalArrival_eq_raw_ae (V := V)] with ω hω
  exact fun e => hω e.1 e.2

theorem eventTime_positive_ae [Countable V] :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ e : Event V, 0 < eventTime ω e := by
  filter_upwards [ExponentialClocks.all_gaps_positive_ae (V := V),
    eventTime_eq_raw_ae (V := V)] with ω hp heq
  intro e
  rw [heq e]
  apply Finset.sum_pos
  · intro k _
    exact hp e.1 k
  · exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩

theorem eventSet_finite_ae [Fintype V] :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ t : ℝ, (eventSet ω t).Finite :=
  ArrivalFiltration.finite_clock_events_ae

/-- Both requirements are established from the actual exponential product measure. -/
theorem good_ae [Fintype V] :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ t : ℝ, Good ω t := by
  filter_upwards [eventSet_finite_ae (V := V),
    ClockNoTies.all_chronological_arrivals_injective_ae (V := V)] with ω hf hi
  exact fun t => ⟨hf t, hi⟩

theorem word_mem_iff_ae [Fintype V] :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ (t : ℝ) (e : Event V),
      e ∈ word ω t ↔ eventTime ω e ≤ t := by
  filter_upwards [good_ae (V := V)] with ω hω
  exact fun t e => word_mem_iff ω t (hω t) e

theorem word_positive_bounded_ae [Fintype V] :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ (t : ℝ) (e : Event V),
      e ∈ word ω t → 0 < eventTime ω e ∧ eventTime ω e ≤ t := by
  filter_upwards [word_mem_iff_ae (V := V), eventTime_positive_ae (V := V)] with ω hm hp
  exact fun t e he => ⟨hp e, (hm t e).mp he⟩

/-- Exact coverage is also stated using the original, unclipped exponential partial sums. -/
theorem word_mem_iff_raw_ae [Fintype V] :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ (t : ℝ) (e : Event V),
      e ∈ word ω t ↔ ExponentialClocks.arrival e.1 e.2 ω ≤ t := by
  filter_upwards [word_mem_iff_ae (V := V), eventTime_eq_raw_ae (V := V)] with ω hm heq
  intro t e
  rw [hm t e, heq e]

/-- One common probability-one statement valid for every real time bound. -/
theorem word_spec_ae [Fintype V] :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ t : ℝ,
      (∀ e : Event V, e ∈ word ω t ↔ eventTime ω e ≤ t) ∧
      (word ω t).Nodup ∧
      (word ω t).Pairwise (fun a b => eventTime ω b < eventTime ω a) ∧
      (∀ e ∈ word ω t, 0 < eventTime ω e ∧ eventTime ω e ≤ t) := by
  filter_upwards [word_mem_iff_ae (V := V), word_positive_bounded_ae (V := V)] with ω hm hp
  exact fun t => ⟨hm t, word_nodup ω t, word_strictly_decreasing ω t, hp t⟩

/-! The total word is measurable, including its explicitly defined fallback.
Countability makes exact coverage a countable intersection; strict ordering
makes the finite word unique, so its fibers have a measurable description. -/

theorem measurableSet_coverage [Countable V] (t : ℝ) (l : List (Event V)) :
    MeasurableSet {ω : ExponentialClocks.Sample V |
      ∀ e : Event V, e ∈ l ↔ eventTime ω e ≤ t} := by
  have heq : {ω : ExponentialClocks.Sample V | ∀ e : Event V, e ∈ l ↔ eventTime ω e ≤ t} =
      ⋂ e : Event V, {ω : ExponentialClocks.Sample V | e ∈ l ↔ eventTime ω e ≤ t} := by
    ext ω
    simp
  rw [heq]
  exact MeasurableSet.iInter fun e =>
    (MeasurableSet.const (e ∈ l)).iff
      (measurableSet_le (eventTime_measurable e) measurable_const)

theorem measurableSet_eventSet_finite [Countable V] (t : ℝ) :
    MeasurableSet {ω : ExponentialClocks.Sample V | (eventSet ω t).Finite} := by
  classical
  have heq : {ω : ExponentialClocks.Sample V | (eventSet ω t).Finite} =
      ⋃ l : List (Event V), {ω : ExponentialClocks.Sample V |
        ∀ e : Event V, e ∈ l ↔ eventTime ω e ≤ t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hf
      refine ⟨hf.toFinset.toList, ?_⟩
      intro e
      simp only [Finset.mem_toList, Set.Finite.mem_toFinset, eventSet, Set.mem_ofPred_eq]
    · rintro ⟨l, hl⟩
      apply l.finite_toSet.subset
      exact fun e he => (hl e).mpr he
  rw [heq]
  exact MeasurableSet.iUnion (measurableSet_coverage t)

theorem measurableSet_eventTime_injective [Countable V] :
    MeasurableSet {ω : ExponentialClocks.Sample V | Function.Injective (eventTime ω)} := by
  have heq : {ω : ExponentialClocks.Sample V | Function.Injective (eventTime ω)} =
      ⋂ e : Event V, ⋂ f : Event V,
        {ω : ExponentialClocks.Sample V | eventTime ω e = eventTime ω f → e = f} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Function.Injective]
  rw [heq]
  exact MeasurableSet.iInter fun e => MeasurableSet.iInter fun f =>
    (measurableSet_eq_fun (eventTime_measurable e) (eventTime_measurable f)).imp
      (MeasurableSet.const (e = f))

theorem measurableSet_good [Countable V] (t : ℝ) :
    MeasurableSet {ω : ExponentialClocks.Sample V | Good ω t} :=
  (measurableSet_eventSet_finite t).inter measurableSet_eventTime_injective

theorem measurableSet_strictly_decreasing [Countable V] (l : List (Event V)) :
    MeasurableSet {ω : ExponentialClocks.Sample V |
      l.Pairwise (fun a b => eventTime ω b < eventTime ω a)} := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hhead : MeasurableSet {ω : ExponentialClocks.Sample V |
        ∀ b : Event V, b ∈ l → eventTime ω b < eventTime ω a} := by
      have heq : {ω : ExponentialClocks.Sample V |
          ∀ b : Event V, b ∈ l → eventTime ω b < eventTime ω a} =
          ⋂ b : Event V, {ω : ExponentialClocks.Sample V |
            b ∈ l → eventTime ω b < eventTime ω a} := by ext ω; simp
      rw [heq]
      exact MeasurableSet.iInter fun b => (MeasurableSet.const (b ∈ l)).imp
        (measurableSet_lt (eventTime_measurable b) (eventTime_measurable a))
    simpa only [List.pairwise_cons, Set.ofPred_and] using hhead.inter ih

theorem word_eq_iff (ω : ExponentialClocks.Sample V) (t : ℝ) (l : List (Event V)) :
    word ω t = l ↔
      (¬ Good ω t ∧ l = []) ∨
      (Good ω t ∧ l.Pairwise (fun a b => eventTime ω b < eventTime ω a) ∧
        ∀ e : Event V, e ∈ l ↔ eventTime ω e ≤ t) := by
  classical
  constructor
  · intro hword
    by_cases h : Good ω t
    · right
      subst l
      exact ⟨h, word_strictly_decreasing ω t, fun e => word_mem_iff ω t h e⟩
    · left
      exact ⟨h, hword.symm.trans (word_eq_empty_of_not_good ω t h)⟩
  · rintro (⟨h, rfl⟩ | ⟨h, hs, hc⟩)
    · exact word_eq_empty_of_not_good ω t h
    · let r : Event V → Event V → Prop := fun a b => eventTime ω b < eventTime ω a
      let : Std.Irrefl r := ⟨fun _ => lt_irrefl _⟩
      let : Std.Antisymm r := ⟨fun _ _ hab hba => False.elim ((not_lt_of_ge hab.le) hba)⟩
      exact List.Pairwise.eq_of_mem_iff (r := r) (word_strictly_decreasing ω t) hs
        (fun e => (word_mem_iff ω t h e).trans (hc e).symm)

theorem measurableSet_word_eq [Countable V] (t : ℝ) (l : List (Event V)) :
    MeasurableSet {ω : ExponentialClocks.Sample V | word ω t = l} := by
  have heq : {ω : ExponentialClocks.Sample V | word ω t = l} =
      {ω | ¬ Good ω t ∧ l = []} ∪
      {ω | Good ω t ∧ l.Pairwise (fun a b => eventTime ω b < eventTime ω a) ∧
        ∀ e : Event V, e ∈ l ↔ eventTime ω e ≤ t} := by
    ext ω
    exact word_eq_iff ω t l
  rw [heq]
  exact ((measurableSet_good t).compl.inter (MeasurableSet.const (l = []))).union
    ((measurableSet_good t).inter
      ((measurableSet_strictly_decreasing l).inter (measurableSet_coverage t l)))

/-- Valid for any measurable structure on the countable event-list codomain. -/
theorem word_measurable [Countable V] [MeasurableSpace (List (Event V))] (t : ℝ) :
    Measurable (fun ω : ExponentialClocks.Sample V => word ω t) :=
  measurable_to_countable' (fun l => measurableSet_word_eq t l)

/-- Every prefix or fixed-position selection is measurable in the discrete event space. -/
theorem word_getD_measurable [Countable V] [MeasurableSpace (Event V)]
    [MeasurableSpace (List (Event V))] [MeasurableSingletonClass (List (Event V))]
    (t : ℝ) (i : Nat) (fallback : Event V) :
    Measurable (fun ω : ExponentialClocks.Sample V => (word ω t).getD i fallback) :=
  (measurable_of_countable (fun l : List (Event V) => l.getD i fallback)).comp
    (word_measurable t)

theorem word_length_measurable [Countable V] (t : ℝ) :
    Measurable (fun ω : ExponentialClocks.Sample V => (word ω t).length) :=
  (measurable_of_countable (fun l : List (Event V) => l.length)).comp
    (word_measurable t)

theorem measurableSet_word_length_ge [Countable V] (t : ℝ) (r : Nat) :
    MeasurableSet {ω : ExponentialClocks.Sample V | r ≤ (word ω t).length} :=
  measurableSet_le measurable_const (word_length_measurable t)

end MathResearchAnalysis.ClockEventWord
