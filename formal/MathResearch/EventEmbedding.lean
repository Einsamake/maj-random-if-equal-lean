import MathResearch.Trace
import MathResearch.Scheduling

set_option autoImplicit false

/-!
Finite labeled-event embedding into rank/color slots.

The target word is constructed by `List.mergeSort`, rather than assumed to
exist.  All update functions are fixed per event ID.  No probability law or
infinite-execution assertion is part of this module.
-/

namespace MathResearch.EventEmbedding

universe v w

variable {Event : Type} {Site : Type v} {State : Type w}

/-- Updating the same site or neighboring sites is declared a conflict. -/
def Conflict (site : Event → Site) (adjacent : Site → Site → Prop)
    (a b : Event) : Prop :=
  site a = site b ∨ adjacent (site a) (site b)

/-- Only distinct, non-neighboring sites are declared independent. -/
def Independent (site : Event → Site) (adjacent : Site → Site → Prop)
    (a b : Event) : Prop :=
  ¬ Conflict site adjacent a b

/-- Every earlier conflicting event has smaller rank. -/
def ConflictRanksIncrease (site : Event → Site)
    (adjacent : Site → Site → Prop) (rank : Event → Nat)
    (source : List Event) : Prop :=
  ∀ a b, Trace.Before a b source → Conflict site adjacent a b → rank a < rank b

/-- Assign the rank/color slot defined in the scheduling module. -/
def eventSlot (color : Event → Bool) (rank : Event → Nat) (event : Event) : Nat :=
  Scheduling.slot (color event) (rank event)

theorem conflicting_slots_increase
    (site : Event → Site) (adjacent : Site → Site → Prop)
    (color : Event → Bool) (rank : Event → Nat) (source : List Event)
    (increasing : ConflictRanksIncrease site adjacent rank source)
    {a b : Event} (before : Trace.Before a b source)
    (conflict : Conflict site adjacent a b) :
    eventSlot color rank a < eventSlot color rank b :=
  Scheduling.slot_strict_of_rank_strict (color a) (color b)
    (increasing a b before conflict)

/-- A decidable, total comparison suitable for the executable merge sort. -/
def slotLE (color : Event → Bool) (rank : Event → Nat) (a b : Event) : Bool :=
  decide (eventSlot color rank a ≤ eventSlot color rank b)

theorem slotLE_trans (color : Event → Bool) (rank : Event → Nat)
    (a b c : Event) (hab : slotLE color rank a b) (hbc : slotLE color rank b c) :
    slotLE color rank a c := by
  have hab' : eventSlot color rank a ≤ eventSlot color rank b := by
    simpa only [slotLE, decide_eq_true_eq] using hab
  have hbc' : eventSlot color rank b ≤ eventSlot color rank c := by
    simpa only [slotLE, decide_eq_true_eq] using hbc
  simpa only [slotLE, decide_eq_true_eq] using Nat.le_trans hab' hbc'

theorem slotLE_total (color : Event → Bool) (rank : Event → Nat) (a b : Event) :
    slotLE color rank a b || slotLE color rank b a := by
  simp only [slotLE, Bool.or_eq_true, decide_eq_true_eq]
  exact Nat.le_total _ _

/-- The actual finite target word, sorted by nondecreasing slot. -/
def sortBySlot (color : Event → Bool) (rank : Event → Nat)
    (source : List Event) : List Event :=
  source.mergeSort (slotLE color rank)

theorem sortBySlot_perm (color : Event → Bool) (rank : Event → Nat)
    (source : List Event) : source.Perm (sortBySlot color rank source) :=
  (List.mergeSort_perm source (slotLE color rank)).symm

theorem sortBySlot_sorted (color : Event → Bool) (rank : Event → Nat)
    (source : List Event) :
    (sortBySlot color rank source).Pairwise
      (fun a b => eventSlot color rank a ≤ eventSlot color rank b) := by
  simpa only [sortBySlot, slotLE, decide_eq_true_eq] using
    List.pairwise_mergeSort (slotLE_trans color rank) (slotLE_total color rank) source

/-- Conflict rank growth really implies conflict-order preservation by sorting. -/
theorem sortBySlot_preserves_conflicts
    (site : Event → Site) (adjacent : Site → Site → Prop)
    (color : Event → Bool) (rank : Event → Nat) (source : List Event)
    (increasing : ConflictRanksIncrease site adjacent rank source) :
    Trace.PreservesConflictOrder (Independent site adjacent) source
      (sortBySlot color rank source) := by
  intro a b not_independent before
  have conflict : Conflict site adjacent a b := by
    exact Classical.byContradiction not_independent
  have hslot := conflicting_slots_increase site adjacent color rank source
    increasing before conflict
  have comparison : slotLE color rank a b := by
    simpa only [slotLE, decide_eq_true_eq] using Nat.le_of_lt hslot
  exact List.pair_sublist_mergeSort
    (slotLE_trans color rank) (slotLE_total color rank) comparison before

theorem sortBySlot_swapEquivalent
    (site : Event → Site) (adjacent : Site → Site → Prop)
    (color : Event → Bool) (rank : Event → Nat) (source : List Event)
    (unique : source.Nodup)
    (increasing : ConflictRanksIncrease site adjacent rank source) :
    Trace.SwapEquivalent (Independent site adjacent) source
      (sortBySlot color rank source) :=
  Trace.swapEquivalent_of_perm_preserving_conflicts (Independent site adjacent)
    source (sortBySlot color rank source) unique (sortBySlot_perm color rank source)
    (sortBySlot_preserves_conflicts site adjacent color rank source increasing)

/-- The same labeled deterministic updates have the same finite final state. -/
theorem execute_eq_sortBySlot
    (site : Event → Site) (adjacent : Site → Site → Prop)
    (color : Event → Bool) (rank : Event → Nat)
    (update : Event → State → State) (source : List Event)
    (unique : source.Nodup)
    (increasing : ConflictRanksIncrease site adjacent rank source)
    (sound : ∀ a b, Independent site adjacent a b → Trace.Commutes update a b)
    (initial : State) :
    Trace.execute update source initial =
      Trace.execute update (sortBySlot color rank source) initial :=
  Trace.execute_eq_of_swapEquivalent update (Independent site adjacent) sound
    (sortBySlot_swapEquivalent site adjacent color rank source unique increasing) initial

/-! Finite same-slot batches. -/

/-- Select one slot, preserving the source order among selected event IDs. -/
def slotBatch (color : Event → Bool) (rank : Event → Nat)
    (source : List Event) (slot : Nat) : List Event :=
  source.filter (fun event => decide (eventSlot color rank event = slot))

theorem mem_slotBatch_iff (color : Event → Bool) (rank : Event → Nat)
    (source : List Event) (slot : Nat) (event : Event) :
    event ∈ slotBatch color rank source slot ↔
      event ∈ source ∧ eventSlot color rank event = slot := by
  simp only [slotBatch, List.mem_filter, decide_eq_true_eq]

/-- Positive ranks imply that all events assigned the same slot have one color. -/
theorem slotBatch_same_color (color : Event → Bool) (rank : Event → Nat)
    (source : List Event) (slot : Nat)
    (positive : ∀ event, event ∈ source → 0 < rank event)
    {a b : Event} (ha : a ∈ slotBatch color rank source slot)
    (hb : b ∈ slotBatch color rank source slot) : color a = color b := by
  rcases (mem_slotBatch_iff color rank source slot a).mp ha with ⟨ha', sa⟩
  rcases (mem_slotBatch_iff color rank source slot b).mp hb with ⟨hb', sb⟩
  exact (Scheduling.slot_injective_positive (positive a ha') (positive b hb')
    (sa.trans sb.symm)).2

/-- Events in one slot are pairwise independent. -/
theorem slotBatch_pairwise_independent
    (site : Event → Site) (adjacent : Site → Site → Prop)
    (color : Event → Bool) (rank : Event → Nat) (source : List Event) (slot : Nat)
    (increasing : ConflictRanksIncrease site adjacent rank source) :
    (slotBatch color rank source slot).Pairwise (Independent site adjacent) := by
  apply List.pairwise_of_forall_sublist
  intro a b before_batch conflict
  have before_source : Trace.Before a b source :=
    before_batch.trans List.filter_sublist
  have hslot := conflicting_slots_increase site adjacent color rank source
    increasing before_source conflict
  have ha : a ∈ slotBatch color rank source slot := before_batch.subset (by simp)
  have hb : b ∈ slotBatch color rank source slot := before_batch.subset (by simp)
  have sa := ((mem_slotBatch_iff color rank source slot a).mp ha).2
  have sb := ((mem_slotBatch_iff color rank source slot b).mp hb).2
  omega

/-- There cannot be two writes to the same site within a slot. -/
theorem slotBatch_sites_nodup
    (site : Event → Site) (adjacent : Site → Site → Prop)
    (color : Event → Bool) (rank : Event → Nat) (source : List Event) (slot : Nat)
    (increasing : ConflictRanksIncrease site adjacent rank source) :
    ((slotBatch color rank source slot).map site).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  apply List.pairwise_map.mpr
  exact (slotBatch_pairwise_independent site adjacent color rank source slot increasing).imp
    (fun independent equal => independent (Or.inl equal))

/-! Connect the actual finite rank-generation algorithm to the embedding. -/

private theorem annotate_pairwise (conflict : Event → Event → Bool) :
    ∀ newest : List Event,
      (Scheduling.annotate conflict newest).Pairwise
        (fun new old => conflict new.1 old.1 → old.2 < new.2) := by
  intro newest
  induction newest with
  | nil => exact List.Pairwise.nil
  | cons event past ih =>
      change ((event, Scheduling.nextRank (Scheduling.conflictingRanks conflict event
        (Scheduling.annotate conflict past))) :: Scheduling.annotate conflict past).Pairwise _
      apply List.pairwise_cons.mpr
      constructor
      · intro old member conflicting
        exact Scheduling.earlier_conflict_rank_lt conflict event old.1 old.2 past
          member conflicting
      · exact ih

section GeneratedRanks

variable [DecidableEq Site]

/-- Executable Boolean conflict test for a decidable neighborhood. -/
def conflictBool (site : Event → Site) (adjacent : Site → Site → Prop)
    [DecidableRel adjacent] (a b : Event) : Bool :=
  decide (site a = site b ∨ adjacent (site a) (site b))

/-- Rank an earliest-first event word using the actual predecessor maximum. -/
def rankChronological (site : Event → Site) (adjacent : Site → Site → Prop)
    [DecidableRel adjacent] (source : List Event) : List (Event × Nat) :=
  (Scheduling.annotate (conflictBool site adjacent) source.reverse).reverse

theorem rankChronological_preserves_ids
    (site : Event → Site) (adjacent : Site → Site → Prop) [DecidableRel adjacent]
    (source : List Event) :
    (rankChronological site adjacent source).map Prod.fst = source := by
  simp only [rankChronological, List.map_reverse, Scheduling.annotate_preserves_events,
    List.reverse_reverse]

theorem rankChronological_unique
    (site : Event → Site) (adjacent : Site → Site → Prop) [DecidableRel adjacent]
    (source : List Event) (unique : source.Nodup) :
    (rankChronological site adjacent source).Nodup := by
  have mapped_unique : ((rankChronological site adjacent source).map Prod.fst).Nodup := by
    rw [rankChronological_preserves_ids]
    exact unique
  exact (List.pairwise_map.mp mapped_unique).imp
    (fun unequal equal => unequal (congrArg Prod.fst equal))

theorem rankChronological_positive
    (site : Event → Site) (adjacent : Site → Site → Prop) [DecidableRel adjacent]
    (source : List Event) (event : Event × Nat)
    (member : event ∈ rankChronological site adjacent source) : 0 < event.2 :=
  Scheduling.annotated_rank_positive (conflictBool site adjacent) event.1 event.2
    (List.mem_reverse.mp member)

/-- Rank growth is proved from the algorithm, rather than assumed here. -/
theorem rankChronological_conflicts_increase
    (site : Event → Site) (adjacent : Site → Site → Prop) [DecidableRel adjacent]
    (symmetric : ∀ i j, adjacent i j → adjacent j i) (source : List Event) :
    ConflictRanksIncrease (fun (event : Event × Nat) => site event.1) adjacent Prod.snd
      (rankChronological site adjacent source) := by
  have pairwise : (rankChronological site adjacent source).Pairwise
      (fun old new => conflictBool site adjacent new.1 old.1 → old.2 < new.2) :=
    List.pairwise_reverse.mpr (annotate_pairwise (conflictBool site adjacent) source.reverse)
  intro a b before conflict
  apply pairwise.forall_sublist before
  have reversed : Conflict site adjacent b.1 a.1 := by
    rcases conflict with same | neighbor
    · exact Or.inl same.symm
    · exact Or.inr (symmetric _ _ neighbor)
  simpa only [conflictBool, Conflict, decide_eq_true_eq] using reversed

private theorem execute_projected_word (update : Event → State → State)
    (word : List (Event × Nat)) (initial : State) :
    Trace.execute update (word.map Prod.fst) initial =
      Trace.execute (fun event => update event.1) word initial := by
  induction word generalizing initial with
  | nil => rfl
  | cons event rest ih =>
      simpa only [List.map_cons, Trace.execute_cons] using ih (update event.1 initial)

/-- Complete finite rank generation and actual slot-sort embedding. -/
theorem execute_eq_generated_slot_sort
    (site : Event → Site) (adjacent : Site → Site → Prop) [DecidableRel adjacent]
    (symmetric : ∀ i j, adjacent i j → adjacent j i)
    (color : Event → Bool) (update : Event → State → State)
    (source : List Event) (unique : source.Nodup)
    (sound : ∀ a b, Independent site adjacent a b → Trace.Commutes update a b)
    (initial : State) :
    Trace.execute update source initial =
      Trace.execute (fun event => update event.1)
        (sortBySlot (fun event => color event.1) Prod.snd
          (rankChronological site adjacent source)) initial := by
  have projected := execute_projected_word update
    (rankChronological site adjacent source) initial
  rw [rankChronological_preserves_ids] at projected
  exact projected.trans
    (execute_eq_sortBySlot (fun (event : Event × Nat) => site event.1) adjacent
      (fun event => color event.1) Prod.snd (fun event => update event.1)
      (rankChronological site adjacent source)
      (rankChronological_unique site adjacent source unique)
      (rankChronological_conflicts_increase site adjacent symmetric source)
      (fun a b independent => sound a.1 b.1 independent) initial)

end GeneratedRanks

/-! Fixed event-specific marks represented by deterministic local rules. -/

section MarkedLocalUpdates

variable {Value : Type w} [DecidableEq Site]

/-- Each fixed event ID has its own rule, reading its site's closed neighborhood. -/
def MarkedReadsOnly (site : Event → Site) (adjacent : Site → Site → Prop)
    (rule : Event → (Site → Value) → Value) : Prop :=
  ∀ event before after,
    (∀ k, Trace.ClosedNeighborhood adjacent (site event) k → before k = after k) →
      rule event before = rule event after

/-- Reuse the same event-specific rule and write only that event's site. -/
def markedCellUpdate (site : Event → Site)
    (rule : Event → (Site → Value) → Value)
    (event : Event) (configuration : Site → Value) : Site → Value :=
  fun k => if k = site event then rule event configuration else configuration k

omit [DecidableEq Site] in
theorem independent_symm (site : Event → Site) (adjacent : Site → Site → Prop)
    (symmetric : ∀ i j, adjacent i j → adjacent j i)
    {a b : Event} (independent : Independent site adjacent a b) :
    Independent site adjacent b a := by
  intro conflict
  rcases conflict with same | neighbor
  · exact independent (Or.inl same.symm)
  · exact independent (Or.inr (symmetric _ _ neighbor))

theorem marked_rule_eq_after_independent_update
    (site : Event → Site) (adjacent : Site → Site → Prop)
    (rule : Event → (Site → Value) → Value)
    (locality : MarkedReadsOnly site adjacent rule)
    {a b : Event} (independent : Independent site adjacent a b)
    (configuration : Site → Value) :
    rule a (markedCellUpdate site rule b configuration) = rule a configuration := by
  apply locality a
  intro k read
  have different : k ≠ site b := by
    intro equal
    subst k
    rcases read with same | neighbor
    · exact independent (Or.inl same.symm)
    · exact independent (Or.inr neighbor)
  simp only [markedCellUpdate, ite_eq_right different]

/-- Nonconflicting marked single-cell updates really commute as functions. -/
theorem marked_updates_commute
    (site : Event → Site) (adjacent : Site → Site → Prop)
    (symmetric : ∀ i j, adjacent i j → adjacent j i)
    (rule : Event → (Site → Value) → Value)
    (locality : MarkedReadsOnly site adjacent rule)
    {a b : Event} (independent : Independent site adjacent a b) :
    Trace.Commutes (markedCellUpdate site rule) a b := by
  intro configuration
  have different : site a ≠ site b := fun equal => independent (Or.inl equal)
  have different' : site b ≠ site a := Ne.symm different
  have hi := marked_rule_eq_after_independent_update site adjacent rule locality
    independent configuration
  have hj := marked_rule_eq_after_independent_update site adjacent rule locality
    (independent_symm site adjacent symmetric independent) configuration
  funext k
  by_cases ka : k = site a
  · subst k
    simp only [markedCellUpdate, ite_eq_right different]
    exact hi.symm
  · by_cases kb : k = site b
    · subst k
      simp only [markedCellUpdate, ite_eq_right different']
      exact hj
    · simp only [markedCellUpdate, ite_eq_right ka, ite_eq_right kb]

/-- Complete finite embedding result for fixed marked neighborhood rules. -/
theorem execute_marked_eq_sortBySlot
    (site : Event → Site) (adjacent : Site → Site → Prop)
    (symmetric : ∀ i j, adjacent i j → adjacent j i)
    (color : Event → Bool) (rank : Event → Nat)
    (rule : Event → (Site → Value) → Value)
    (locality : MarkedReadsOnly site adjacent rule)
    (source : List Event) (unique : source.Nodup)
    (increasing : ConflictRanksIncrease site adjacent rank source)
    (initial : Site → Value) :
    Trace.execute (markedCellUpdate site rule) source initial =
      Trace.execute (markedCellUpdate site rule) (sortBySlot color rank source) initial :=
  execute_eq_sortBySlot site adjacent color rank (markedCellUpdate site rule) source
    unique increasing (fun _ _ h => marked_updates_commute site adjacent symmetric
      rule locality h) initial

/-- The configurations agree at every site after both finite event words finish. -/
theorem execute_marked_eq_sortBySlot_at
    (site : Event → Site) (adjacent : Site → Site → Prop)
    (symmetric : ∀ i j, adjacent i j → adjacent j i)
    (color : Event → Bool) (rank : Event → Nat)
    (rule : Event → (Site → Value) → Value)
    (locality : MarkedReadsOnly site adjacent rule)
    (source : List Event) (unique : source.Nodup)
    (increasing : ConflictRanksIncrease site adjacent rank source)
    (initial : Site → Value) (k : Site) :
    Trace.execute (markedCellUpdate site rule) source initial k =
      Trace.execute (markedCellUpdate site rule) (sortBySlot color rank source) initial k :=
  congrFun (execute_marked_eq_sortBySlot site adjacent symmetric color rank rule
    locality source unique increasing initial) k

/-- The rank algorithm and real slot sort preserve a fixed marked local execution. -/
theorem execute_marked_eq_generated_slot_sort
    (site : Event → Site) (adjacent : Site → Site → Prop) [DecidableRel adjacent]
    (symmetric : ∀ i j, adjacent i j → adjacent j i)
    (color : Event → Bool) (rule : Event → (Site → Value) → Value)
    (locality : MarkedReadsOnly site adjacent rule)
    (source : List Event) (unique : source.Nodup) (initial : Site → Value) :
    Trace.execute (markedCellUpdate site rule) source initial =
      Trace.execute (fun event => markedCellUpdate site rule event.1)
        (sortBySlot (fun event => color event.1) Prod.snd
          (rankChronological site adjacent source)) initial :=
  execute_eq_generated_slot_sort site adjacent symmetric color (markedCellUpdate site rule)
    source unique (fun _ _ h => marked_updates_commute site adjacent symmetric rule locality h)
    initial

end MarkedLocalUpdates

end MathResearch.EventEmbedding
