import Std

/-!
Deterministic scheduling facts used by the CA candidate proof.

This module uses only `Std`.  It proves rank-to-slot arithmetic and finite
max-plus identities over natural numbers.  It does not construct Poisson
clocks, prove a stochastic tail bound, or establish an expected recovery time.
-/

namespace MathResearch.Scheduling

/-- Maximum of a finite list, with the empty-list convention used in (6). -/
def maximum : List Nat → Nat
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

/-- The rank recurrence takes one plus the maximum predecessor rank. -/
def nextRank (predecessors : List Nat) : Nat := maximum predecessors + 1

theorem nextRank_positive (predecessors : List Nat) :
    0 < nextRank predecessors := by
  simp only [nextRank]
  omega

theorem predecessor_rank_lt {predecessors : List Nat} {rank : Nat}
    (h : rank ∈ predecessors) : rank < nextRank predecessors := by
  have hle := member_le_maximum h
  simp only [nextRank]
  omega

/-- Collect exactly the ranks of earlier conflicting events. -/
def conflictingRanks {Event : Type} (conflict : Event → Event → Bool)
    (event : Event) : List (Event × Nat) → List Nat
  | [] => []
  | (old, rank) :: past =>
      if conflict event old then
        rank :: conflictingRanks conflict event past
      else conflictingRanks conflict event past

theorem rank_mem_conflictingRanks {Event : Type}
    (conflict : Event → Event → Bool) (event old : Event) (rank : Nat)
    {past : List (Event × Nat)} (hmem : (old, rank) ∈ past)
    (hconflict : conflict event old = true) :
    rank ∈ conflictingRanks conflict event past := by
  induction past with
  | nil => cases hmem
  | cons previous rest ih =>
      rcases previous with ⟨previousEvent, previousRank⟩
      rcases List.mem_cons.mp hmem with heq | hrest
      · cases heq
        simp [conflictingRanks, hconflict]
      · have h := ih hrest
        cases hp : conflict event previousEvent <;>
          simp [conflictingRanks, hp, h]

/--
Annotate a finite word listed newest first.  Each rank is computed from the
already annotated strictly earlier suffix; no rank inequality is assumed.
-/
def annotate {Event : Type} (conflict : Event → Event → Bool) :
    List Event → List (Event × Nat)
  | [] => []
  | event :: past =>
      let seen := annotate conflict past
      (event, nextRank (conflictingRanks conflict event seen)) :: seen

theorem annotate_preserves_events {Event : Type}
    (conflict : Event → Event → Bool) (events : List Event) :
    (annotate conflict events).map Prod.fst = events := by
  induction events with
  | nil => rfl
  | cons event past ih => simp [annotate, ih]

theorem annotated_rank_positive {Event : Type}
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

theorem earlier_conflict_rank_lt {Event : Type}
    (conflict : Event → Event → Bool) (event old : Event) (rank : Nat)
    (past : List Event) (hmem : (old, rank) ∈ annotate conflict past)
    (hconflict : conflict event old = true) :
    rank < nextRank (conflictingRanks conflict event (annotate conflict past)) :=
  predecessor_rank_lt
    (rank_mem_conflictingRanks conflict event old rank hmem hconflict)

/-- `true` denotes the first (red) color, assigned slot `2 * rank - 1`. -/
def slot (firstColor : Bool) (rank : Nat) : Nat :=
  if firstColor then 2 * rank - 1 else 2 * rank

theorem slot_positive (color : Bool) {rank : Nat} (hrank : 0 < rank) :
    0 < slot color rank := by
  cases color <;> simp [slot] <;> omega

theorem slot_le_twice_rank (color : Bool) (rank : Nat) :
    slot color rank ≤ 2 * rank := by
  cases color <;> simp [slot] <;> omega

/-- Every conflict whose rank strictly increases also has increasing slots. -/
theorem slot_strict_of_rank_strict (first second : Bool) {a b : Nat}
    (h : a < b) : slot first a < slot second b := by
  cases first <;> cases second <;> simp [slot] <;> omega

/-- Thus predecessors selected by the actual finite maximum precede a task. -/
theorem predecessor_slot_lt (first second : Bool)
    {predecessors : List Nat} {rank : Nat} (h : rank ∈ predecessors) :
    slot first rank < slot second (nextRank predecessors) :=
  slot_strict_of_rank_strict first second (predecessor_rank_lt h)

/-- Earlier conflicting events precede the newly generated task in slots. -/
theorem earlier_conflict_slot_lt {Event : Type}
    (conflict : Event → Event → Bool) (event old : Event) (rank : Nat)
    (past : List Event) (first second : Bool)
    (hmem : (old, rank) ∈ annotate conflict past)
    (hconflict : conflict event old = true) :
    slot first rank <
      slot second (nextRank (conflictingRanks conflict event (annotate conflict past))) :=
  slot_strict_of_rank_strict first second
    (earlier_conflict_rank_lt conflict event old rank past hmem hconflict)

theorem slot_within_depth (color : Bool) {rank depth : Nat}
    (h : rank ≤ depth) : slot color rank ≤ 2 * depth := by
  have hle := slot_le_twice_rank color rank
  omega

/-- Positive ranks make the slot encode both rank and color injectively. -/
theorem slot_injective_positive {first second : Bool} {a b : Nat}
    (ha : 0 < a) (hb : 0 < b) (heq : slot first a = slot second b) :
    a = b ∧ first = second := by
  cases first <;> cases second <;> simp [slot] at heq <;>
    constructor <;> first | omega | rfl

/-- The maximum of a nonempty finite list is attained. -/
theorem maximum_mem (head : Nat) (rest : List Nat) :
    maximum (head :: rest) ∈ head :: rest := by
  induction rest generalizing head with
  | nil => simp [maximum]
  | cons next tail ih =>
      by_cases h : head ≤ maximum (next :: tail)
      · have heq : maximum (head :: next :: tail) = maximum (next :: tail) := by
          change max head (maximum (next :: tail)) = maximum (next :: tail)
          omega
        rw [heq]
        exact List.mem_cons_of_mem head (ih next)
      · have heq : maximum (head :: next :: tail) = head := by
          change max head (maximum (next :: tail)) = head
          omega
        rw [heq]
        exact List.mem_cons_self

/-- Addition commutes with the nonempty finite maximum. -/
theorem maximum_map_add (delay head : Nat) (rest : List Nat) :
    maximum ((head :: rest).map (fun value => delay + value)) =
      delay + maximum (head :: rest) := by
  induction rest generalizing head with
  | nil => simp [maximum]
  | cons next tail ih =>
      change max (delay + head)
        (maximum ((next :: tail).map (fun value => delay + value))) =
        delay + max head (maximum (next :: tail))
      rw [ih next]
      omega

/-- Deterministic max-plus step corresponding to the recurrence (14). -/
def completion (delay : Nat) (predecessors : List Nat) : Nat :=
  delay + maximum predecessors

theorem predecessor_completion_le (delay : Nat)
    {predecessors : List Nat} {value : Nat} (h : value ∈ predecessors) :
    delay + value ≤ completion delay predecessors := by
  have hle := member_le_maximum h
  simp only [completion]
  omega

/-- Each nonempty max-plus step equals an actual predecessor path weight. -/
theorem completion_attained (delay head : Nat) (rest : List Nat) :
    ∃ value ∈ head :: rest, completion delay (head :: rest) = delay + value := by
  exact ⟨maximum (head :: rest), maximum_mem head rest, rfl⟩

theorem completion_path_max (delay head : Nat) (rest : List Nat) :
    completion delay (head :: rest) =
      maximum ((head :: rest).map (fun value => delay + value)) :=
  (maximum_map_add delay head rest).symm

/-- A finite natural-number geometric sum, used to check dyadic arithmetic. -/
def dyadicSum : Nat → Nat
  | 0 => 0
  | n + 1 => dyadicSum n + 2 ^ n

theorem dyadicSum_add_one (n : Nat) : dyadicSum n + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [dyadicSum, Nat.pow_succ]
      omega

theorem dyadicSum_lt_pow (n : Nat) : dyadicSum n < 2 ^ n := by
  have h := dyadicSum_add_one n
  omega

end MathResearch.Scheduling
