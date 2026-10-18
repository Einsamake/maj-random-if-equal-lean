module

public import MathResearchAnalysis.MarkedEventTrace

set_option autoImplicit false

/-!
# Actual clock ranks embedded in color slots

The source is the genuine annotated chronological clock word. The target is
constructed by merge sort. Rank growth and the concrete marked update supply
all conflict-order and commutation facts internally. Only finite execution
is asserted here, without a deletion comparison or a probability-law claim.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.RankSlotEmbedding

abbrev Event (n : Nat) := SquareSpin.Event n
abbrev Label (n : Nat) := Event n × Nat

/-- The first color uses the odd slot and the second the following even slot. -/
def slot (colour : Bool) (rank : Nat) : Nat :=
  if colour then 2 * rank - 1 else 2 * rank

theorem slot_strict_of_rank_strict (first second : Bool) {a b : Nat}
    (h : a < b) : slot first a < slot second b := by
  cases first <;> cases second <;> simp [slot] <;> omega

theorem slot_injective_positive {first second : Bool} {a b : Nat}
    (ha : 0 < a) (hb : 0 < b) (h : slot first a = slot second b) :
    a = b ∧ first = second := by
  cases first <;> cases second <;> simp [slot] at h <;>
    constructor <;> first | omega | rfl

def labelSlot {n : Nat} (label : Label n) : Nat :=
  slot (SquareTasks.colour label.1.1) label.2

def source {n : Nat} (ω : ExponentialClocks.Sample (SquareTasks.Vertex n))
    (t : ℝ) : List (Label n) :=
  (FiniteRankWitness.annotate ClockRankTail.eventConflict (ClockEventWord.word ω t)).reverse

def slotLE {n : Nat} (a b : Label n) : Bool := decide (labelSlot a ≤ labelSlot b)

def targetLabels {n : Nat} (ω : ExponentialClocks.Sample (SquareTasks.Vertex n))
    (t : ℝ) : List (Label n) :=
  (source ω t).mergeSort slotLE

/-- Actual event identities after sorting their computed rank/color labels. -/
def target {n : Nat} (ω : ExponentialClocks.Sample (SquareTasks.Vertex n))
    (t : ℝ) : List (Event n) := (targetLabels ω t).map Prod.fst

theorem source_ids {n : Nat} (ω : ExponentialClocks.Sample (SquareTasks.Vertex n))
    (t : ℝ) : (source ω t).map Prod.fst = (ClockEventWord.word ω t).reverse := by
  simp only [source, List.map_reverse, FiniteRankWitness.annotate_preserves_events]

theorem source_positive {n : Nat} (ω : ExponentialClocks.Sample (SquareTasks.Vertex n))
    (t : ℝ) {a : Label n} (ha : a ∈ source ω t) : 0 < a.2 :=
  FiniteRankWitness.annotated_rank_positive ClockRankTail.eventConflict a.1 a.2
    (List.mem_reverse.mp ha)

theorem source_nodup {n : Nat} (ω : ExponentialClocks.Sample (SquareTasks.Vertex n))
    (t : ℝ) : (source ω t).Nodup := by
  have hm : ((source ω t).map Prod.fst).Nodup := by
    rw [source_ids]
    exact List.nodup_reverse.mpr (ClockEventWord.word_nodup ω t)
  exact (List.pairwise_map.mp hm).imp
    (fun hne heq => hne (congrArg Prod.fst heq))

private theorem annotate_pairwise {n : Nat} (events : List (Event n)) :
    (FiniteRankWitness.annotate ClockRankTail.eventConflict events).Pairwise
      (fun later earlier => ClockRankTail.eventConflict later.1 earlier.1 = true →
        earlier.2 < later.2) := by
  induction events with
  | nil => exact List.Pairwise.nil
  | cons event past ih =>
    change ((event, FiniteRankWitness.nextRank (FiniteRankWitness.conflictingRanks
      ClockRankTail.eventConflict event (FiniteRankWitness.annotate
        ClockRankTail.eventConflict past))) :: _).Pairwise _
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih⟩
    intro old hmem hconflict
    have hr := FiniteRankWitness.member_le_maximum
      ((FiniteRankWitness.mem_conflictingRanks_iff ClockRankTail.eventConflict
        event old.2 _).mpr ⟨old.1, hmem, hconflict⟩)
    change old.2 < FiniteRankWitness.maximum _ + 1
    omega

/-- The actual recurrence supplies strict growth for every chronological conflict. -/
theorem source_conflicts_increase {n : Nat}
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) (t : ℝ)
    {a b : Label n} (hbefore : EventTrace.Before a b (source ω t))
    (hconflict : SquareSpin.Conflict a.1 b.1) : a.2 < b.2 := by
  have hp := List.pairwise_reverse.mpr (annotate_pairwise (ClockEventWord.word ω t))
  apply hp.forall_sublist hbefore
  exact (MarkedEventTrace.eventConflict_iff b.1 a.1).mpr
    (SquareSpin.conflict_symmetric hconflict)

theorem source_conflicting_slots_increase {n : Nat}
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) (t : ℝ)
    {a b : Label n} (hbefore : EventTrace.Before a b (source ω t))
    (hconflict : SquareSpin.Conflict a.1 b.1) : labelSlot a < labelSlot b :=
  slot_strict_of_rank_strict _ _ (source_conflicts_increase ω t hbefore hconflict)

private theorem slotLE_trans {n : Nat} (a b c : Label n)
    (hab : slotLE a b) (hbc : slotLE b c) : slotLE a c := by
  simp only [slotLE, decide_eq_true_eq] at hab hbc ⊢
  exact hab.trans hbc

private theorem slotLE_total {n : Nat} (a b : Label n) : slotLE a b || slotLE b a := by
  simp only [slotLE, Bool.or_eq_true, decide_eq_true_eq]
  exact Nat.le_total _ _

theorem targetLabels_perm {n : Nat}
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) (t : ℝ) :
    (source ω t).Perm (targetLabels ω t) :=
  (List.mergeSort_perm (source ω t) slotLE).symm

theorem targetLabels_sorted {n : Nat}
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) (t : ℝ) :
    (targetLabels ω t).Pairwise (fun a b => labelSlot a ≤ labelSlot b) := by
  simpa only [targetLabels, slotLE, decide_eq_true_eq] using
    List.pairwise_mergeSort slotLE_trans slotLE_total (source ω t)

theorem target_perm {n : Nat}
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) (t : ℝ) :
    (ClockEventWord.word ω t).reverse.Perm (target ω t) := by
  rw [← source_ids]
  exact (targetLabels_perm ω t).map Prod.fst

theorem target_nodup {n : Nat}
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) (t : ℝ) :
    (target ω t).Nodup :=
  (target_perm ω t).nodup (List.nodup_reverse.mpr (ClockEventWord.word_nodup ω t))

theorem target_same_events {n : Nat}
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) (t : ℝ) (e : Event n) :
    e ∈ ClockEventWord.word ω t ↔ e ∈ target ω t :=
  List.mem_reverse.symm.trans (target_perm ω t).mem_iff

theorem targetLabels_preserve_conflicts {n : Nat}
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) (t : ℝ)
    {a b : Label n} (hbefore : EventTrace.Before a b (source ω t))
    (hconflict : SquareSpin.Conflict a.1 b.1) :
    EventTrace.Before a b (targetLabels ω t) := by
  have hslot : slotLE a b := by
    simp only [slotLE, decide_eq_true_eq]
    exact (source_conflicting_slots_increase ω t hbefore hconflict).le
  exact List.pair_sublist_mergeSort slotLE_trans slotLE_total hslot hbefore

private theorem before_map_lift {A B : Type*} (f : A → B) (events : List A)
    {a b : B} (h : EventTrace.Before a b (events.map f)) :
    ∃ x y, f x = a ∧ f y = b ∧ EventTrace.Before x y events := by
  obtain ⟨selected, hsub, heq⟩ := List.sublist_map_iff.mp h
  cases selected with
  | nil => simp at heq
  | cons x rest =>
    cases rest with
    | nil => simp at heq
    | cons y tail =>
      cases tail with
      | nil =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq] at heq
        exact ⟨x, y, heq.1.symm, heq.2.1.symm, hsub⟩
      | cons z tail => simp at heq

/-- Every pair of actual conflicting event identities retains its order. -/
theorem target_preserves_conflicts {n : Nat}
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) (t : ℝ) :
    MarkedEventTrace.PreservesConflictOrder (ClockEventWord.word ω t).reverse
      (target ω t) := by
  intro a b hconflict hbefore
  rw [← source_ids] at hbefore
  obtain ⟨x, y, hx, hy, hxy⟩ := before_map_lift Prod.fst (source ω t) hbefore
  have hc : SquareSpin.Conflict x.1 y.1 := by rwa [hx, hy]
  have hs := (targetLabels_preserve_conflicts ω t hxy hc).map Prod.fst
  simpa only [EventTrace.Before, target, List.map_cons, List.map_nil, hx, hy] using hs

private theorem before_total {A : Type*} {events : List A} {a b : A}
    (ha : a ∈ events) (hb : b ∈ events) (hne : a ≠ b) :
    EventTrace.Before a b events ∨ EventTrace.Before b a events := by
  induction events with
  | nil => cases ha
  | cons head rest ih =>
    rcases List.mem_cons.mp ha with haHead | haRest <;>
      rcases List.mem_cons.mp hb with hbHead | hbRest
    · exact False.elim (hne (haHead.trans hbHead.symm))
    · subst head
      exact Or.inl (List.Sublist.cons_cons a (List.singleton_sublist.mpr hbRest))
    · subst head
      exact Or.inr (List.Sublist.cons_cons b (List.singleton_sublist.mpr haRest))
    · rcases ih haRest hbRest with hab | hba
      · exact Or.inl (hab.cons head)
      · exact Or.inr (hba.cons head)

private theorem before_asymmetric {A : Type*} {events : List A} {a b : A}
    (hu : events.Nodup) (hab : EventTrace.Before a b events)
    (hba : EventTrace.Before b a events) : False := by
  induction events with
  | nil => cases hab
  | cons head rest ih =>
    rcases List.nodup_cons.mp hu with ⟨hnot, hu⟩
    cases hab with
    | cons _ hab =>
      cases hba with
      | cons _ hba => exact ih hu hab hba
      | cons_cons _ hba => exact hnot (hab.subset (by simp))
    | cons_cons _ hab =>
      cases hba with
      | cons _ hba => exact hnot (hba.subset (by simp))
      | cons_cons _ hba => exact hnot (List.singleton_sublist.mp hab)

/-- Sorting neither reverses nor creates an order for a conflicting pair. -/
theorem target_same_conflict_order {n : Nat}
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) (t : ℝ) :
    MarkedEventTrace.SameConflictOrder (ClockEventWord.word ω t).reverse
      (target ω t) := by
  intro a b hc
  refine ⟨target_preserves_conflicts ω t a b hc, ?_⟩
  intro hab
  have ha : a ∈ (ClockEventWord.word ω t).reverse :=
    (target_perm ω t).mem_iff.mpr (hab.subset (by simp))
  have hb : b ∈ (ClockEventWord.word ω t).reverse :=
    (target_perm ω t).mem_iff.mpr (hab.subset (by simp))
  have hne : a ≠ b := by
    intro heq
    subst b
    exact List.not_nodup_pair a ((target_nodup ω t).sublist hab)
  rcases before_total ha hb hne with hs | hs
  · exact hs
  · exact False.elim (before_asymmetric (target_nodup ω t) hab
      (target_preserves_conflicts ω t b a (SquareSpin.conflict_symmetric hc) hs))

/-- The actual marked update has the same final state under the constructed slot sort. -/
theorem executeClockWord_eq_target {n : Nat} (η : Event n → Bool)
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) (t : ℝ)
    (initial : SquareSpin.Config n) :
    MarkedEventTrace.executeClockWord η ω t initial =
      MarkedEventTrace.execute η (target ω t) initial :=
  MarkedEventTrace.executeClockWord_eq_of_same_events η ω t (target ω t)
    (target_nodup ω t) (target_same_events ω t) (target_same_conflict_order ω t) initial

/-- The actual ranked events assigned to a fixed slot, in target order. -/
def slotBatch {n : Nat} (ω : ExponentialClocks.Sample (SquareTasks.Vertex n))
    (t : ℝ) (s : Nat) : List (Label n) :=
  (targetLabels ω t).filter (fun a => decide (labelSlot a = s))

theorem mem_slotBatch_iff {n : Nat}
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) (t : ℝ) (s : Nat) (a : Label n) :
    a ∈ slotBatch ω t s ↔ a ∈ targetLabels ω t ∧ labelSlot a = s := by
  simp only [slotBatch, List.mem_filter, decide_eq_true_eq]

theorem slotBatch_same_colour {n : Nat}
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) (t : ℝ) (s : Nat)
    {a b : Label n} (ha : a ∈ slotBatch ω t s) (hb : b ∈ slotBatch ω t s) :
    SquareTasks.colour a.1.1 = SquareTasks.colour b.1.1 := by
  rcases (mem_slotBatch_iff ω t s a).mp ha with ⟨ha, hsa⟩
  rcases (mem_slotBatch_iff ω t s b).mp hb with ⟨hb, hsb⟩
  exact (slot_injective_positive
    (source_positive ω t ((targetLabels_perm ω t).mem_iff.mpr ha))
    (source_positive ω t ((targetLabels_perm ω t).mem_iff.mpr hb))
    (hsa.trans hsb.symm)).2

theorem slotBatch_pairwise_independent {n : Nat}
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) (t : ℝ) (s : Nat) :
    (slotBatch ω t s).Pairwise (fun a b => ¬ SquareSpin.Conflict a.1 b.1) := by
  apply List.pairwise_of_forall_sublist
  intro a b hab hc
  have ha := (mem_slotBatch_iff ω t s a).mp (hab.subset (by simp))
  have hb := (mem_slotBatch_iff ω t s b).mp (hab.subset (by simp))
  have hu : (targetLabels ω t).Nodup := (targetLabels_perm ω t).nodup (source_nodup ω t)
  have hne : a ≠ b := by
    intro heq
    subst b
    exact List.not_nodup_pair a (hu.sublist (hab.trans List.filter_sublist))
  rcases before_total ((targetLabels_perm ω t).mem_iff.mpr ha.1)
    ((targetLabels_perm ω t).mem_iff.mpr hb.1) hne with hs | hs
  · have hlt := source_conflicting_slots_increase ω t hs hc
    omega
  · have hlt := source_conflicting_slots_increase ω t hs (SquareSpin.conflict_symmetric hc)
    omega

theorem slotBatch_sites_nodup {n : Nat}
    (ω : ExponentialClocks.Sample (SquareTasks.Vertex n)) (t : ℝ) (s : Nat) :
    ((slotBatch ω t s).map (fun a => a.1.1)).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  apply List.pairwise_map.mpr
  exact (slotBatch_pairwise_independent ω t s).imp
    (fun hi heq => hi (Or.inl heq))

end MathResearchAnalysis.RankSlotEmbedding
