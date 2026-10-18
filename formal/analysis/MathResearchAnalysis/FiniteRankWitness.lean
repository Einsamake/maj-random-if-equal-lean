module

public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Range
public import Mathlib.Tactic

set_option autoImplicit false

/-!
# Finite newest-first ranks have actual causal-chain witnesses

The four defining recurrences below are identical to the deterministic
`MathResearch.Scheduling` recurrences, but live in the analysis toolchain.
An event's computed rank is witnessed by strictly earlier occurrences in
the original word, represented by `List.Sublist`, and not by a chain
existence assumption. The conflict relation need not be symmetric.
-/

public section

namespace MathResearchAnalysis.FiniteRankWitness

@[expose] def maximum : List Nat → Nat
  | [] => 0
  | value :: rest => max value (maximum rest)

theorem member_le_maximum {values : List Nat} {value : Nat}
    (h : value ∈ values) : value ≤ maximum values := by
  induction values with
  | nil => cases h
  | cons head rest ih =>
      rcases List.mem_cons.mp h with heq | hrest
      · subst value
        simp only [maximum]
        omega
      · have hle := ih hrest
        simp only [maximum]
        omega

theorem maximum_mem (head : Nat) (rest : List Nat) :
    maximum (head :: rest) ∈ head :: rest := by
  induction rest generalizing head with
  | nil => simp [maximum]
  | cons next tail ih =>
      by_cases h : head ≤ maximum (next :: tail)
      · rw [show maximum (head :: next :: tail) = maximum (next :: tail) by
          change max head (maximum (next :: tail)) = maximum (next :: tail)
          omega]
        exact List.mem_cons_of_mem head (ih next)
      · rw [show maximum (head :: next :: tail) = head by
          change max head (maximum (next :: tail)) = head
          omega]
        exact List.mem_cons_self

theorem maximum_mem_of_positive (values : List Nat) (h : 0 < maximum values) :
    maximum values ∈ values := by
  cases values with
  | nil => simp [maximum] at h
  | cons head rest => exact maximum_mem head rest

@[expose] def nextRank (predecessors : List Nat) : Nat := maximum predecessors + 1

theorem nextRank_positive (predecessors : List Nat) : 0 < nextRank predecessors := by
  simp [nextRank]

@[expose] def conflictingRanks {Event : Type*} (conflict : Event → Event → Bool)
    (event : Event) : List (Event × Nat) → List Nat
  | [] => []
  | (old, rank) :: past =>
      if conflict event old then rank :: conflictingRanks conflict event past
      else conflictingRanks conflict event past

theorem mem_conflictingRanks_iff {Event : Type*}
    (conflict : Event → Event → Bool) (event : Event) (rank : Nat)
    (past : List (Event × Nat)) :
    rank ∈ conflictingRanks conflict event past ↔
      ∃ old, (old, rank) ∈ past ∧ conflict event old = true := by
  induction past with
  | nil => simp [conflictingRanks]
  | cons previous rest ih =>
      rcases previous with ⟨old, oldRank⟩
      cases hc : conflict event old <;>
        simp only [conflictingRanks, hc, Bool.false_eq_true, ite_false, ite_true,
          List.mem_cons, ih]
      · constructor
        · rintro ⟨w, hw, hc⟩
          exact ⟨w, Or.inr hw, hc⟩
        · rintro ⟨w, hw, hwc⟩
          rcases hw with hw | hw
          · have he : w = old := congrArg Prod.fst hw
            subst w
            simp only [hc, Bool.false_eq_true] at hwc
          · exact ⟨w, hw, hwc⟩
      · constructor
        · rintro (hr | ⟨w, hw, hwc⟩)
          · subst rank
            exact ⟨old, Or.inl rfl, hc⟩
          · exact ⟨w, Or.inr hw, hwc⟩
        · rintro ⟨w, hw, hwc⟩
          rcases hw with hw | hw
          · cases hw
            exact Or.inl rfl
          · exact Or.inr ⟨w, hw, hwc⟩

@[expose] def annotate {Event : Type*} (conflict : Event → Event → Bool) :
    List Event → List (Event × Nat)
  | [] => []
  | event :: past =>
      let seen := annotate conflict past
      (event, nextRank (conflictingRanks conflict event seen)) :: seen

theorem annotate_preserves_events {Event : Type*}
    (conflict : Event → Event → Bool) (events : List Event) :
    (annotate conflict events).map Prod.fst = events := by
  induction events with
  | nil => rfl
  | cons event past ih => simp [annotate, ih]

theorem annotated_rank_positive {Event : Type*}
    (conflict : Event → Event → Bool) (event : Event) (rank : Nat)
    {events : List Event} (hmem : (event, rank) ∈ annotate conflict events) :
    0 < rank := by
  induction events with
  | nil => cases hmem
  | cons previous past ih =>
      change (event, rank) ∈
        (previous, nextRank (conflictingRanks conflict previous
          (annotate conflict past))) :: annotate conflict past at hmem
      rcases List.mem_cons.mp hmem with heq | hrest
      · cases heq
        exact nextRank_positive _
      · exact ih hrest

/-- Every positive maximum selects an actual strictly earlier conflicting occurrence. -/
theorem predecessor_attained {Event : Type*}
    (conflict : Event → Event → Bool) (event : Event) (past : List (Event × Nat))
    (h : 0 < maximum (conflictingRanks conflict event past)) :
    ∃ old, (old, maximum (conflictingRanks conflict event past)) ∈ past ∧
      conflict event old = true :=
  (mem_conflictingRanks_iff conflict event _ past).mp
    (maximum_mem_of_positive _ h)

/-- Newest-first chain: each adjacent rank decreases by exactly one and terminates at one. -/
inductive CausalChain {Event : Type*} (conflict : Event → Event → Bool) :
    List (Event × Nat) → Prop
  | singleton (event : Event) : CausalChain conflict [(event, 1)]
  | cons (event old : Event) (rank : Nat) (tail : List (Event × Nat))
      (hconflict : conflict event old = true)
      (hchain : CausalChain conflict ((old, rank) :: tail)) :
      CausalChain conflict ((event, rank + 1) :: (old, rank) :: tail)

@[expose] def firstRank {Event : Type*} : List (Event × Nat) → Nat
  | [] => 0
  | (_, rank) :: _ => rank

theorem causalChain_length {Event : Type*} {conflict : Event → Event → Bool}
    {chain : List (Event × Nat)} (h : CausalChain conflict chain) :
    chain.length = firstRank chain := by
  induction h with
  | singleton event => rfl
  | cons event old rank tail hconflict hchain ih =>
      simp only [List.length_cons, firstRank] at ih ⊢
      omega

theorem causalChain_isChain {Event : Type*} {conflict : Event → Event → Bool}
    {chain : List (Event × Nat)} (h : CausalChain conflict chain) :
    chain.IsChain (fun a b => conflict a.1 b.1 = true ∧ a.2 = b.2 + 1) := by
  induction h with
  | singleton event => exact List.IsChain.singleton _
  | cons event old rank tail hconflict hchain ih =>
      exact List.IsChain.cons_cons ⟨hconflict, rfl⟩ ih

@[expose] def descendingRanks : Nat → List Nat
  | 0 => []
  | n + 1 => (n + 1) :: descendingRanks n

theorem causalChain_ranks {Event : Type*} {conflict : Event → Event → Bool}
    {chain : List (Event × Nat)} (h : CausalChain conflict chain) :
    chain.map Prod.snd = descendingRanks chain.length := by
  induction h with
  | singleton event => rfl
  | cons event old rank tail hconflict hchain ih =>
      have hlen := causalChain_length hchain
      simp only [firstRank] at hlen
      rw [List.map_cons, ih]
      simp only [List.length_cons] at hlen ⊢
      rw [hlen]
      rfl

theorem descendingRanks_reverse (n : Nat) :
    (descendingRanks n).reverse = (List.range n).map Nat.succ := by
  induction n with
  | zero => rfl
  | succ n ih => simp [descendingRanks, ih, List.range_succ]

/-- The computed rank itself constructs a full chain in the original annotated word. -/
theorem annotated_causalChain {Event : Type*} (conflict : Event → Event → Bool)
    (event : Event) (rank : Nat) {events : List Event}
    (hmem : (event, rank) ∈ annotate conflict events) :
    ∃ tail, CausalChain conflict ((event, rank) :: tail) ∧
      ((event, rank) :: tail).Sublist (annotate conflict events) := by
  induction events generalizing event rank with
  | nil => cases hmem
  | cons previous past ih =>
      change (event, rank) ∈
        (previous, nextRank (conflictingRanks conflict previous
          (annotate conflict past))) :: annotate conflict past at hmem
      rcases List.mem_cons.mp hmem with heq | hrest
      · have he : event = previous := congrArg Prod.fst heq
        have hr : rank = nextRank (conflictingRanks conflict previous
          (annotate conflict past)) := congrArg Prod.snd heq
        subst event
        subst rank
        let depth := maximum (conflictingRanks conflict previous (annotate conflict past))
        by_cases hz : depth = 0
        · refine ⟨[], ?_, ?_⟩
          · change CausalChain conflict [(previous, depth + 1)]
            rw [hz]
            exact CausalChain.singleton previous
          · exact (List.nil_sublist _).cons_cons _
        · have hp : 0 < depth := Nat.pos_of_ne_zero hz
          obtain ⟨old, hold, hconflict⟩ := predecessor_attained conflict previous
            (annotate conflict past) hp
          obtain ⟨tail, hchain, hsub⟩ := ih old depth hold
          exact ⟨(old, depth) :: tail,
            CausalChain.cons previous old depth tail hconflict hchain,
            hsub.cons_cons _⟩
      · obtain ⟨tail, hchain, hsub⟩ := ih event rank hrest
        exact ⟨tail, hchain, hsub.cons _⟩

/-- Explicit length, adjacency and original-word order are all consequences of annotation. -/
theorem annotated_chain_witness {Event : Type*} (conflict : Event → Event → Bool)
    (event : Event) (rank : Nat) {events : List Event}
    (hmem : (event, rank) ∈ annotate conflict events) :
    ∃ tail : List Event, (event :: tail).length = rank ∧
      (event :: tail).Sublist events ∧
      (event :: tail).IsChain (fun later earlier => conflict later earlier = true) := by
  obtain ⟨tail, hchain, hsub⟩ := annotated_causalChain conflict event rank hmem
  refine ⟨tail.map Prod.fst, ?_, ?_, ?_⟩
  · simpa only [List.length_cons, List.length_map, firstRank] using causalChain_length hchain
  · simpa only [List.map_cons, annotate_preserves_events] using hsub.map Prod.fst
  · exact List.isChain_map_of_isChain Prod.fst (fun _ _ h => h.1)
      (causalChain_isChain hchain)

/-- Reversal gives chronological ranks exactly `1, 2, ..., rank`. -/
theorem annotated_chronological_rank_witness {Event : Type*}
    (conflict : Event → Event → Bool) (event : Event) (rank : Nat) {events : List Event}
    (hmem : (event, rank) ∈ annotate conflict events) :
    ∃ chain : List (Event × Nat), chain.Sublist (annotate conflict events).reverse ∧
      chain.length = rank ∧ chain.getLast? = some (event, rank) ∧
      chain.map Prod.snd = (List.range rank).map Nat.succ ∧
      chain.IsChain (fun earlier later => conflict later.1 earlier.1 = true ∧
        later.2 = earlier.2 + 1) := by
  obtain ⟨tail, hchain, hsub⟩ := annotated_causalChain conflict event rank hmem
  have hlen : ((event, rank) :: tail).length = rank := causalChain_length hchain
  refine ⟨((event, rank) :: tail).reverse, hsub.reverse, ?_, ?_, ?_, ?_⟩
  · simpa only [List.length_reverse] using hlen
  · simp
  · rw [List.map_reverse, causalChain_ranks hchain, hlen, descendingRanks_reverse]
  · exact List.isChain_reverse.mpr (causalChain_isChain hchain)

/-- A rank at least `q` supplies a chronological `q`-chain ending at the selected event. -/
theorem annotated_truncated_chain_witness {Event : Type*}
    (conflict : Event → Event → Bool) (event : Event) (rank q : Nat)
    {events : List Event} (hmem : (event, rank) ∈ annotate conflict events)
    (hq : 0 < q) (hqr : q ≤ rank) :
    ∃ chain : List Event, chain.Sublist events.reverse ∧ chain.length = q ∧
      chain.getLast? = some event ∧
      chain.IsChain (fun earlier later => conflict later earlier = true) := by
  obtain ⟨tail, hlen, hsub, hchain⟩ := annotated_chain_witness conflict event rank hmem
  refine ⟨((event :: tail).take q).reverse,
    ((List.take_sublist q _).trans hsub).reverse, ?_, ?_, ?_⟩
  · simp only [List.length_reverse, List.length_take, hlen, Nat.min_eq_left hqr]
  · cases q with
    | zero => omega
    | succ q => simp
  · exact List.isChain_reverse.mpr (hchain.take q)

end MathResearchAnalysis.FiniteRankWitness
