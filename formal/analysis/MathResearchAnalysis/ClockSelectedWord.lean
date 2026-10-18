module

public import MathResearchAnalysis.ClockEventOrder
public import MathResearchAnalysis.ClockEventWord
public import MathResearchAnalysis.ClockMaximum
public import MathResearchAnalysis.MarkedEventTrace
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Pairwise

set_option autoImplicit false

/-!
# Genuine selected-clock words and their chronological rearrangement

Tasks are enumerated by increasing positive layer, retaining their true
site/ring event identities. A single explicitly constructed probability-one
regularity event supplies finite readiness and the genuine bounded clock word.
The only additional condition in the final pathwise comparison is that the
actual selected-task maximum has occurred by the time bound. Neither an event
permutation, a conflict-order premise, nor a local-rule assumption is supplied.
The same identity-indexed marks are retained in both executions.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.ClockSelectedWord

abbrev Task (n : ℕ) := ℕ × SquareTasks.Vertex n
abbrev Event (n : ℕ) := SquareSpin.Event n
abbrev Sample (n : ℕ) := ClockEventOrder.Sample n

/-- Layer `j` is positive slot `j + 1`; sites within one color may be in any order. -/
def layerTasks (n : ℕ) (c : Bool) (k : ℕ) : List (Task n) :=
  (List.range (k + 1)).flatMap fun j =>
    (SquareTasks.tasks n c j).toList.map fun v => (j + 1, v)

theorem mem_layerTasks_iff (n : ℕ) (c : Bool) (k : ℕ) (p : Task n) :
    p ∈ layerTasks n c k ↔
      0 < p.1 ∧ p.1 ≤ k + 1 ∧ p.2 ∈ SquareTasks.tasks n c (p.1 - 1) := by
  rcases p with ⟨a, u⟩
  simp only [layerTasks, List.mem_flatMap, List.mem_range, List.mem_map, Finset.mem_toList]
  constructor
  · rintro ⟨j, hj, v, hv, he⟩
    have ha : j + 1 = a := congrArg Prod.fst he
    have hu : v = u := congrArg Prod.snd he
    subst a
    subst v
    exact ⟨by omega, by omega, by simpa using hv⟩
  · rintro ⟨ha, hk, hu⟩
    refine ⟨a - 1, by omega, u, hu, ?_⟩
    exact Prod.ext (by omega) rfl

theorem layerTasks_selected (n : ℕ) (c : Bool) (k : ℕ) (p : Task n)
    (hp : p ∈ layerTasks n c k) : ClockEventOrder.Selected n c p.1 p.2 :=
  ⟨((mem_layerTasks_iff n c k p).mp hp).1, ((mem_layerTasks_iff n c k p).mp hp).2.2⟩

/-- Increasing layers, and different sites within a single layer. -/
def TaskOrder {n : ℕ} (p q : Task n) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≠ q.2)

theorem layerTasks_ordered (n : ℕ) (c : Bool) (k : ℕ) :
    (layerTasks n c k).Pairwise TaskOrder := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro j _
    apply List.pairwise_map.mpr
    exact (SquareTasks.tasks n c j).nodup_toList.imp fun h => Or.inr ⟨rfl, h⟩
  · apply List.pairwise_lt_range.imp
    intro a b hab p hp q hq
    rcases List.mem_map.mp hp with ⟨v, _, rfl⟩
    rcases List.mem_map.mp hq with ⟨u, _, rfl⟩
    exact Or.inl (Nat.succ_lt_succ hab)

theorem layerTasks_nodup (n : ℕ) (c : Bool) (k : ℕ) : (layerTasks n c k).Nodup := by
  apply (layerTasks_ordered n c k).imp
  intro p q h he
  subst q
  rcases h with h | ⟨_, h⟩
  · exact (Nat.lt_irrefl _) h
  · exact h rfl

/-- The genuine site/ring identities of the layer-ordered task enumeration. -/
def layerWord (n : ℕ) (c : Bool) (k : ℕ) (ω : Sample n) : List (Event n) :=
  (layerTasks n c k).map fun p => ClockEventOrder.eventId n p.1 p.2 ω

/-- A common full-measure event supplying both selected tasks and the full real clock word. -/
def Regular (n : ℕ) (ω : Sample n) : Prop :=
  ClockEventOrder.Regular n ω ∧ ∀ t : ℝ, ClockEventWord.Good ω t

theorem regular_ae (n : ℕ) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (SquareTasks.Vertex n), Regular n ω := by
  filter_upwards [ClockEventOrder.regular_ae n,
    ClockEventWord.good_ae (V := SquareTasks.Vertex n)] with ω ht hw
  exact ⟨ht, hw⟩

theorem layerWord_nodup (n : ℕ) (c : Bool) (k : ℕ) (ω : Sample n)
    (hω : ClockEventOrder.Regular n ω) : (layerWord n c k ω).Nodup := by
  apply (layerTasks_nodup n c k).map_on
  intro p hp q hq he
  by_contra hpq
  exact ClockEventOrder.distinct_selected_eventId n ω hω c
    (layerTasks_selected n c k p hp) (layerTasks_selected n c k q hq) hpq he

theorem layerWord_nodup_ae (n : ℕ) (c : Bool) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (SquareTasks.Vertex n),
      ∀ k : ℕ, (layerWord n c k ω).Nodup :=
  (ClockEventOrder.regular_ae n).mono fun ω hω k => layerWord_nodup n c k ω hω

theorem selected_completion_le_maximum (n : ℕ) (c : Bool) (k : ℕ) (ω : Sample n)
    (p : Task n) (hp : p ∈ layerTasks n c k) :
    ClockEventOrder.completion n p.1 p.2 ω ≤ ClockMaximum.squareMaximum n c k ω := by
  obtain ⟨hpos, hbound, hmem⟩ := (mem_layerTasks_iff n c k p).mp hp
  have heq : p.1 - 1 + 1 = p.1 := by omega
  have hlocal : ClockEventOrder.completion n p.1 p.2 ω ≤
      ClockMaximum.squareLayer n c (p.1 - 1) ω := by
    simpa only [ClockMaximum.squareLayer, heq] using
      (Finset.le_sup' (fun v => ClockReadiness.completion (SquareTasks.system n)
        (p.1 - 1 + 1) v ω) hmem)
  exact hlocal.trans (Finset.le_sup' (fun j => ClockMaximum.squareLayer n c j ω)
    (Finset.mem_range.mpr (by omega)))

theorem layerWord_mem_fullWord (n : ℕ) (c : Bool) (k : ℕ) (ω : Sample n)
    (hω : Regular n ω) (t : ℝ)
    (hmax : ClockMaximum.squareMaximum n c k ω ≤ (t : WithTop ℝ))
    (e : Event n) (he : e ∈ layerWord n c k ω) : e ∈ ClockEventWord.word ω t := by
  rcases List.mem_map.mp he with ⟨p, hp, rfl⟩
  apply (ClockEventWord.word_mem_iff ω t (hω.2 t) _).mpr
  have hbound := (selected_completion_le_maximum n c k ω p hp).trans hmax
  rw [ClockEventOrder.completion_eq_selected_arrival n ω hω.1 p.1 p.2
    (layerTasks_selected n c k p hp).1] at hbound
  exact WithTop.coe_le_coe.mp hbound

/-- Delete exactly the unselected identities from the chronological real clock word. -/
def selectedChrono (n : ℕ) (c : Bool) (k : ℕ) (ω : Sample n) (t : ℝ) : List (Event n) :=
  (ClockEventWord.word ω t).reverse.filter fun e => decide (e ∈ layerWord n c k ω)

theorem selectedChrono_sublist (n : ℕ) (c : Bool) (k : ℕ) (ω : Sample n) (t : ℝ) :
    (selectedChrono n c k ω t).Sublist (ClockEventWord.word ω t).reverse :=
  List.filter_sublist

theorem selectedChrono_nodup (n : ℕ) (c : Bool) (k : ℕ) (ω : Sample n) (t : ℝ) :
    (selectedChrono n c k ω t).Nodup :=
  (List.nodup_reverse.mpr (ClockEventWord.word_nodup ω t)).filter _

theorem mem_selectedChrono_iff (n : ℕ) (c : Bool) (k : ℕ) (ω : Sample n)
    (hω : Regular n ω) (t : ℝ)
    (hmax : ClockMaximum.squareMaximum n c k ω ≤ (t : WithTop ℝ)) (e : Event n) :
    e ∈ selectedChrono n c k ω t ↔ e ∈ layerWord n c k ω := by
  simp only [selectedChrono, List.mem_filter, List.mem_reverse, decide_eq_true_eq]
  exact ⟨And.right, fun he => ⟨layerWord_mem_fullWord n c k ω hω t hmax e he, he⟩⟩

theorem layerWord_conflict_increasing (n : ℕ) (c : Bool) (k : ℕ) (ω : Sample n)
    (hω : ClockEventOrder.Regular n ω) :
    (layerWord n c k ω).Pairwise (fun a b => SquareSpin.Conflict a b →
      ClockEventWord.eventTime ω a < ClockEventWord.eventTime ω b) := by
  apply List.pairwise_map.mpr
  apply (layerTasks_ordered n c k).imp_of_mem
  intro p q hp hq horder hconf
  have hpSel := layerTasks_selected n c k p hp
  have hqSel := layerTasks_selected n c k q hq
  change p.2 = q.2 ∨ SquareTasks.Adjacent p.2 q.2 at hconf
  have hconf' : p.2 = q.2 ∨ p.2 ∈ SquareTasks.neighbors n q.2 := by
    rcases hconf with h | h
    · exact Or.inl h
    · exact Or.inr ((SquareTasks.mem_neighbors_iff n q.2 p.2).mpr
        (SquareTasks.adjacent_symmetric h))
  have hlt : p.1 < q.1 := by
    rcases horder with h | ⟨heq, hne⟩
    · exact h
    · rw [← heq] at hqSel
      rcases hconf' with hsame | hadj
      · exact False.elim (hne hsame)
      · exact False.elim (ClockEventOrder.selected_same_layer_no_neighbor n c hpSel hqSel hadj)
  have ht := ClockEventOrder.selected_conflict_order n ω hω c hpSel hqSel hlt hconf'
  rw [ClockEventOrder.completion_eq_selected_arrival n ω hω p.1 p.2 hpSel.1,
    ClockEventOrder.completion_eq_selected_arrival n ω hω q.1 q.2 hqSel.1] at ht
  exact WithTop.coe_lt_coe.mp ht

theorem selectedChrono_strictly_increasing (n : ℕ) (c : Bool) (k : ℕ)
    (ω : Sample n) (t : ℝ) :
    (selectedChrono n c k ω t).Pairwise (fun a b =>
      ClockEventWord.eventTime ω a < ClockEventWord.eventTime ω b) :=
  (ClockEventWord.word_reverse_strictly_increasing ω t).sublist List.filter_sublist

private theorem before_or_before_of_mem_ne {α : Type*} {a b : α} {l : List α}
    (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    EventTrace.Before a b l ∨ EventTrace.Before b a l := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with haEq | haTail
    · subst x
      rcases List.mem_cons.mp hb with heq | hbTail
      · exact False.elim (hne heq.symm)
      · exact Or.inl ((List.singleton_sublist.mpr hbTail).cons_cons a)
    · rcases List.mem_cons.mp hb with hbEq | hbTail
      · subst x
        exact Or.inr ((List.singleton_sublist.mpr haTail).cons_cons b)
      · rcases ih haTail hbTail with h | h
        · exact Or.inl (h.cons x)
        · exact Or.inr (h.cons x)

private theorem before_iff_conflict_time {n : ℕ} (ω : Sample n) (l : List (Event n))
    (hsorted : l.Pairwise (fun a b => SquareSpin.Conflict a b →
      ClockEventWord.eventTime ω a < ClockEventWord.eventTime ω b))
    (a b : Event n) (hc : SquareSpin.Conflict a b) :
    EventTrace.Before a b l ↔ a ∈ l ∧ b ∈ l ∧
      ClockEventWord.eventTime ω a < ClockEventWord.eventTime ω b := by
  constructor
  · intro h
    exact ⟨h.subset (by simp), h.subset (by simp), hsorted.forall_sublist h hc⟩
  · rintro ⟨ha, hb, ht⟩
    have hne : a ≠ b := by intro he; subst b; exact (lt_irrefl _) ht
    rcases before_or_before_of_mem_ne ha hb hne with h | h
    · exact h
    · have hrev := hsorted.forall_sublist h (SquareSpin.conflict_symmetric hc)
      exact False.elim ((not_lt_of_ge hrev.le) ht)

/-- Conflict order is derived from the actual selected completions and the actual clock sort. -/
theorem sameConflictOrder (n : ℕ) (c : Bool) (k : ℕ) (ω : Sample n)
    (hω : Regular n ω) (t : ℝ)
    (hmax : ClockMaximum.squareMaximum n c k ω ≤ (t : WithTop ℝ)) :
    MarkedEventTrace.SameConflictOrder (selectedChrono n c k ω t) (layerWord n c k ω) := by
  intro a b hc
  rw [before_iff_conflict_time ω _
    ((selectedChrono_strictly_increasing n c k ω t).imp
      (fun {a b} h (_ : SquareSpin.Conflict a b) => h)) a b hc,
    before_iff_conflict_time ω _ (layerWord_conflict_increasing n c k ω hω.1) a b hc,
    mem_selectedChrono_iff n c k ω hω t hmax a,
    mem_selectedChrono_iff n c k ω hω t hmax b]

theorem selectedChrono_perm_layerWord (n : ℕ) (c : Bool) (k : ℕ) (ω : Sample n)
    (hω : Regular n ω) (t : ℝ)
    (hmax : ClockMaximum.squareMaximum n c k ω ≤ (t : WithTop ℝ)) :
    (selectedChrono n c k ω t).Perm (layerWord n c k ω) :=
  (List.perm_ext_iff_of_nodup (selectedChrono_nodup n c k ω t)
    (layerWord_nodup n c k ω hω.1)).mpr (mem_selectedChrono_iff n c k ω hω t hmax)

/-- The actual zero-boundary majority executions agree, using every retained event's own mark. -/
theorem execute_selectedChrono_eq_layerWord (n : ℕ) (c : Bool) (k : ℕ) (ω : Sample n)
    (hω : Regular n ω) (t : ℝ)
    (hmax : ClockMaximum.squareMaximum n c k ω ≤ (t : WithTop ℝ))
    (η : Event n → Bool) (initial : SquareSpin.Config n) :
    MarkedEventTrace.execute η (selectedChrono n c k ω t) initial =
      MarkedEventTrace.execute η (layerWord n c k ω) initial :=
  MarkedEventTrace.execute_eq_of_same_events_and_conflict_order η
    (selectedChrono_nodup n c k ω t) (layerWord_nodup n c k ω hω.1)
    (mem_selectedChrono_iff n c k ω hω t hmax)
    (sameConflictOrder n c k ω hω t hmax) initial

/-- One probability-one event supports every finite layer, time bound, mark map and initial state. -/
theorem execute_selectedChrono_eq_layerWord_ae (n : ℕ) (c : Bool) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (SquareTasks.Vertex n),
      ∀ (k : ℕ) (t : ℝ), ClockMaximum.squareMaximum n c k ω ≤ (t : WithTop ℝ) →
        ∀ (η : Event n → Bool) (initial : SquareSpin.Config n),
          MarkedEventTrace.execute η (selectedChrono n c k ω t) initial =
            MarkedEventTrace.execute η (layerWord n c k ω) initial := by
  filter_upwards [regular_ae n] with ω hω
  exact fun k t hmax η initial => execute_selectedChrono_eq_layerWord n c k ω hω t hmax η initial

end MathResearchAnalysis.ClockSelectedWord
