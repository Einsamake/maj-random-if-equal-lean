module

public import MathResearchAnalysis.EventTrace
public import MathResearchAnalysis.SquareSpin
public import MathResearchAnalysis.ClockRankTail

set_option autoImplicit false

/-!
# Concrete marked square-spin event traces

A finite marked execution is a list of distinct `(vertex, arrival-index)`
identities together with an identity-indexed mark map. Its updates are the
actual zero-boundary four-input rule of `SquareSpin`. Same-site and adjacent-
site events are exactly the conflicts used by the actual clock rank module.

The final-state theorem needs only equality of event sets, retained marks,
and retention of the relative order of conflicting events. Commutation is
proved from the actual local rule and is not an additional theorem input.
The chronological clock-word corollary uses the reverse of the newest-first
word. No rank-slot ordering or deletion/insertion comparison is asserted here.
-/

public section

namespace MathResearchAnalysis.MarkedEventTrace

abbrev Event (n : ℕ) := SquareSpin.Event n
abbrev Config (n : ℕ) := SquareSpin.Config n

/-- Execute in the listed order, retaining every ring's own mark. -/
@[expose] def execute {n : ℕ} (η : Event n → Bool) (events : List (Event n))
    (initial : Config n) : Config n :=
  EventTrace.execute (SquareSpin.updateEvent η) events initial

/-- The concrete conflict order, phrased directly using the square geometry. -/
@[expose] def PreservesConflictOrder {n : ℕ}
    (first second : List (Event n)) : Prop :=
  ∀ a b, SquareSpin.Conflict a b →
    EventTrace.Before a b first → EventTrace.Before a b second

/-- Both words retain each conflicting pair's relative order. -/
@[expose] def SameConflictOrder {n : ℕ} (first second : List (Event n)) : Prop :=
  ∀ a b, SquareSpin.Conflict a b →
    (EventTrace.Before a b first ↔ EventTrace.Before a b second)

theorem eventConflict_iff {n : ℕ} (a b : Event n) :
    ClockRankTail.eventConflict a b = true ↔ SquareSpin.Conflict a b := by
  simp only [ClockRankTail.eventConflict, decide_eq_true_eq, SquareSpin.Conflict]

/-- The actual local rule supplies the generic adjacent-swap hypothesis. -/
theorem independent_updates_commute {n : ℕ} (η : Event n → Bool)
    (a b : Event n) (h : ¬ SquareSpin.Conflict a b) :
    EventTrace.Commutes (SquareSpin.updateEvent η) a b :=
  SquareSpin.updateEvent_commute η h

theorem adjacent_swap {n : ℕ} (η : Event n → Bool)
    (pre suffix : List (Event n)) (a b : Event n)
    (h : ¬ SquareSpin.Conflict a b) (initial : Config n) :
    execute η (pre ++ a :: b :: suffix) initial =
      execute η (pre ++ b :: a :: suffix) initial :=
  EventTrace.execute_adjacent_swap (SquareSpin.updateEvent η) pre suffix a b
    (independent_updates_commute η a b h) initial

theorem swapEquivalent_of_perm_preserving_conflicts {n : ℕ}
    {first second : List (Event n)} (unique : first.Nodup)
    (permutation : first.Perm second) (order : PreservesConflictOrder first second) :
    EventTrace.SwapEquivalent (fun a b => ¬ SquareSpin.Conflict a b) first second := by
  classical
  apply EventTrace.swapEquivalent_of_perm_preserving_conflicts
    (fun a b => ¬ SquareSpin.Conflict a b) first second unique permutation
  intro a b conflict before
  exact order a b (Classical.byContradiction conflict) before

/-- Concrete finite execution equality; commutation is discharged internally. -/
theorem execute_eq_of_perm_preserving_conflicts {n : ℕ}
    (η : Event n → Bool) {first second : List (Event n)} (unique : first.Nodup)
    (permutation : first.Perm second) (order : PreservesConflictOrder first second)
    (initial : Config n) : execute η first initial = execute η second initial :=
  EventTrace.execute_eq_of_swapEquivalent (SquareSpin.updateEvent η)
    (fun a b => ¬ SquareSpin.Conflict a b)
    (independent_updates_commute η)
    (swapEquivalent_of_perm_preserving_conflicts unique permutation order) initial

/-- Same event identities and same conflict order give the same final state. -/
theorem execute_eq_of_same_events_and_conflict_order {n : ℕ}
    (η : Event n → Bool) {first second : List (Event n)}
    (first_unique : first.Nodup) (second_unique : second.Nodup)
    (same_events : ∀ e, e ∈ first ↔ e ∈ second)
    (same_order : SameConflictOrder first second) (initial : Config n) :
    execute η first initial = execute η second initial :=
  execute_eq_of_perm_preserving_conflicts η first_unique
    ((List.perm_ext_iff_of_nodup first_unique second_unique).mpr same_events)
    (fun a b h => (same_order a b h).mp) initial

/-- Marks at identities not present in a word cannot affect its execution. -/
theorem execute_eq_of_marks_agree {n : ℕ} (η θ : Event n → Bool)
    (events : List (Event n)) (agree : ∀ e ∈ events, η e = θ e) (initial : Config n) :
    execute η events initial = execute θ events initial := by
  induction events generalizing initial with
  | nil => rfl
  | cons e rest ih =>
    have he : SquareSpin.updateEvent η e initial =
        SquareSpin.updateEvent θ e initial := by
      simp only [SquareSpin.updateEvent, agree e (List.mem_cons_self)]
    change execute η rest (SquareSpin.updateEvent η e initial) =
      execute θ rest (SquareSpin.updateEvent θ e initial)
    rw [he]
    exact ih (fun a ha => agree a (List.mem_cons_of_mem e ha)) _

/-- A formulation allowing distinct mark maps that agree on the retained identities. -/
theorem marked_final_state_eq {n : ℕ} (η θ : Event n → Bool)
    {first second : List (Event n)}
    (first_unique : first.Nodup) (second_unique : second.Nodup)
    (same_events : ∀ e, e ∈ first ↔ e ∈ second)
    (same_marks : ∀ e ∈ first, η e = θ e)
    (same_order : SameConflictOrder first second) (initial : Config n) :
    execute η first initial = execute θ second initial := by
  exact (execute_eq_of_same_events_and_conflict_order η first_unique second_unique
    same_events same_order initial).trans
      (execute_eq_of_marks_agree η θ second
        (fun e he => same_marks e ((same_events e).mpr he)) initial)

/-- Chronological execution of all clock arrivals bounded by `t`. -/
@[expose] noncomputable def executeClockWord {n : ℕ} (η : Event n → Bool)
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) (t : ℝ)
    (initial : Config n) : Config n :=
  execute η (ClockEventWord.word ω t).reverse initial

/-- A comparison word with the same identities and conflict order executes identically. -/
theorem executeClockWord_eq_of_same_events {n : ℕ} (η : Event n → Bool)
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) (t : ℝ)
    (other : List (Event n)) (other_unique : other.Nodup)
    (same_events : ∀ e, e ∈ ClockEventWord.word ω t ↔ e ∈ other)
    (same_order : SameConflictOrder (ClockEventWord.word ω t).reverse other)
    (initial : Config n) : executeClockWord η ω t initial = execute η other initial := by
  apply execute_eq_of_same_events_and_conflict_order η
    (List.nodup_reverse.mpr (ClockEventWord.word_nodup ω t)) other_unique
    (fun e => (List.mem_reverse.trans (same_events e))) same_order initial

/-- On a good clock sample, event-set coverage is the exact needed identity condition. -/
theorem executeClockWord_eq_of_eventSet_coverage {n : ℕ} (η : Event n → Bool)
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) (t : ℝ)
    (good : ClockEventWord.Good ω t) (other : List (Event n))
    (other_unique : other.Nodup)
    (coverage : ∀ e, e ∈ other ↔ e ∈ ClockEventWord.eventSet ω t)
    (same_order : SameConflictOrder (ClockEventWord.word ω t).reverse other)
    (initial : Config n) : executeClockWord η ω t initial = execute η other initial := by
  apply executeClockWord_eq_of_same_events η ω t other other_unique
    (fun e => (ClockEventWord.word_mem_iff ω t good e).trans (coverage e).symm)
    same_order initial

end MathResearchAnalysis.MarkedEventTrace
