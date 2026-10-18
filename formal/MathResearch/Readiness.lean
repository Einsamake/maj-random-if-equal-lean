import MathResearch.Scheduling
import MathResearch.Dynamics

/-!
# Deterministic local readiness order

Natural-number completion times express only a strict-order skeleton.  The
`nextRing` field is not a Poisson process and no probability or stopping-time
claim is made.  Completion is recursively defined at every vertex in every
layer.  A bipartite colour condition selects the actual alternating tasks;
unselected entries are virtual and are not asserted to be clock events.
-/

namespace MathResearch.Readiness

universe u

structure System (V : Type u) where
  neighbours : V → List V
  nonempty : ∀ v, neighbours v ≠ []
  symmetric : ∀ {a b}, a ∈ neighbours b → b ∈ neighbours a
  nextRing : V → Nat → Nat
  later : ∀ v r, r < nextRing v r

namespace System

variable {V : Type u} (M : System V)

/-- Layer zero is a common baseline; positive layers apply the local
    readiness maximum followed by a strictly later selected ring. -/
def completion : Nat → V → Nat
  | 0 => fun _ => 0
  | j + 1 => fun v => M.nextRing v
      (Scheduling.maximum ((M.neighbours v).map (completion j)))

def ready (j : Nat) (v : V) : Nat :=
  Scheduling.maximum ((M.neighbours v).map (M.completion j))

@[simp] theorem completion_zero (v : V) : M.completion 0 v = 0 := rfl

theorem completion_succ (j : Nat) (v : V) :
    M.completion (j + 1) v = M.nextRing v (M.ready j v) := rfl

private theorem maximum_zeros (vertices : List V) :
    Scheduling.maximum (vertices.map (fun _ => 0)) = 0 := by
  induction vertices with
  | nil => rfl
  | cons v rest ih => simp [Scheduling.maximum, ih]

theorem completion_one (v : V) : M.completion 1 v = M.nextRing v 0 := by
  change M.nextRing v
    (Scheduling.maximum ((M.neighbours v).map (fun _ => 0))) = M.nextRing v 0
  rw [maximum_zeros]

theorem ready_lt_completion (j : Nat) (v : V) :
    M.ready j v < M.completion (j + 1) v := M.later v (M.ready j v)

theorem predecessor_lt {a b : V} (hNeighbour : a ∈ M.neighbours b) (j : Nat) :
    M.completion j a < M.completion (j + 1) b := by
  have hmem : M.completion j a ∈ (M.neighbours b).map (M.completion j) :=
    List.mem_map.mpr ⟨a, hNeighbour, rfl⟩
  have hle := Scheduling.member_le_maximum hmem
  have hlt := M.ready_lt_completion j b
  change M.completion j a ≤ M.ready j b at hle
  omega

theorem exists_neighbour (v : V) : ∃ w, w ∈ M.neighbours v := by
  cases hs : M.neighbours v with
  | nil => exact False.elim (M.nonempty v hs)
  | cons w rest => exact ⟨w, by simp⟩

theorem same_site_two_steps (v : V) (j : Nat) :
    M.completion j v < M.completion (j + 2) v := by
  obtain ⟨w, hw⟩ := M.exists_neighbour v
  have hfirst := M.predecessor_lt (M.symmetric hw) j
  have hsecond := M.predecessor_lt hw (j + 1)
  simpa [Nat.add_assoc] using Nat.lt_trans hfirst hsecond

/-- Strict completion order along any predetermined finite neighbour path. -/
theorem along_fixed_path (path : Nat → V) (j : Nat) :
    ∀ k, 0 < k →
      (∀ i, i < k → path i ∈ M.neighbours (path (i + 1))) →
      M.completion j (path 0) < M.completion (j + k) (path k) := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk hPath
    have hlast := M.predecessor_lt (hPath k (by omega)) (j + k)
    have hlast' : M.completion (j + k) (path k) <
        M.completion (j + (k + 1)) (path (k + 1)) := by
      simpa [Nat.add_assoc] using hlast
    by_cases hk0 : k = 0
    · subst k
      simpa using hlast'
    · have hfirst := ih (by omega) (by
        intro i hi
        exact hPath i (by omega))
      exact Nat.lt_trans hfirst hlast'

theorem same_site_even_gap (v : V) (j k : Nat) :
    M.completion j v < M.completion (j + 2 * (k + 1)) v := by
  induction k with
  | zero => simpa using M.same_site_two_steps v j
  | succ k ih =>
    have hnext := M.same_site_two_steps v (j + 2 * (k + 1))
    have heq : j + 2 * ((k + 1) + 1) = (j + 2 * (k + 1)) + 2 := by omega
    rw [heq]
    exact Nat.lt_trans ih hnext

theorem same_site_even_order (v : V) {a b : Nat} (hab : a < b)
    (hEven : (b - a) % 2 = 0) : M.completion a v < M.completion b v := by
  have hb : b = a + 2 * (((b - a) / 2 - 1) + 1) := by omega
  rw [hb]
  exact M.same_site_even_gap v a ((b - a) / 2 - 1)

theorem neighbour_odd_gap {a b : V} (hNeighbour : a ∈ M.neighbours b)
    (j k : Nat) :
    M.completion j a < M.completion (j + 2 * k + 1) b := by
  cases k with
  | zero => simpa using M.predecessor_lt hNeighbour j
  | succ k =>
    have hfirst := M.predecessor_lt hNeighbour j
    have hsecond := M.same_site_even_gap b (j + 1) k
    have heq : j + 2 * (k + 1) + 1 = (j + 1) + 2 * (k + 1) := by omega
    rw [heq]
    exact Nat.lt_trans hfirst hsecond

theorem neighbour_odd_order {u v : V} (hNeighbour : u ∈ M.neighbours v)
    {a b : Nat} (hab : a < b) (hOdd : (b - a) % 2 = 1) :
    M.completion a u < M.completion b v := by
  have hb : b = a + 2 * ((b - a) / 2) + 1 := by omega
  rw [hb]
  exact M.neighbour_odd_gap hNeighbour a ((b - a) / 2)

theorem same_site_even_no_reuse (v : V) {a b : Nat} (hab : a < b)
    (hEven : (b - a) % 2 = 0) : M.completion a v ≠ M.completion b v := by
  have hlt := M.same_site_even_order v hab hEven
  omega

end System

/-- Colour at a logical layer; the first positive layer has colour `!phase`. -/
def layerColour (phase : Bool) (j : Nat) : Bool :=
  if j % 2 = 0 then phase else !phase

theorem layerColour_succ (phase : Bool) (j : Nat) :
    layerColour phase (j + 1) = !(layerColour phase j) := by
  by_cases h : j % 2 = 0
  · have hs : (j + 1) % 2 ≠ 0 := by omega
    simp [layerColour, h, hs]
  · have hs : (j + 1) % 2 = 0 := by omega
    simp [layerColour, h, hs]

theorem layerColour_eq_activeColour (phase : Bool) (j : Nat) :
    layerColour phase j = MathResearch.activeColour phase j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [layerColour_succ, MathResearch.activeColour_succ, ih]

theorem layerColour_eq_iff (phase : Bool) (a b : Nat) :
    layerColour phase a = layerColour phase b ↔ a % 2 = b % 2 := by
  by_cases ha : a % 2 = 0 <;> by_cases hb : b % 2 = 0 <;>
    cases phase <;> simp [layerColour, ha, hb] <;> omega

theorem layerColour_ne_iff (phase : Bool) (a b : Nat) :
    layerColour phase a ≠ layerColour phase b ↔ a % 2 ≠ b % 2 := by
  exact not_congr (layerColour_eq_iff phase a b)

/-- Actual alternating tasks are the positive-layer subset of the full
    recursive table. Layer zero is only the common initialization baseline. -/
def Selected {V : Type u} (colour : V → Bool) (phase : Bool) (j : Nat) (v : V) : Prop :=
  0 < j ∧ colour v = layerColour phase j

private theorem bool_eq_of_ne_not {a b : Bool} (h : a ≠ !b) : a = b := by
  cases a <;> cases b <;> simp_all

namespace System

variable {V : Type u} (M : System V)

/-- For a selected task past layer one, every recursive neighbour
    predecessor is also selected. Thus virtual entries do not contribute to
    the recursion for selected tasks. -/
theorem selected_predecessor (colour : V → Bool) (phase : Bool)
    (hBipartite : ∀ {u v}, u ∈ M.neighbours v → colour u ≠ colour v)
    {j : Nat} (hj : 0 < j) {u v : V} (hNeighbour : u ∈ M.neighbours v)
    (hSelected : Selected colour phase (j + 1) v) : Selected colour phase j u := by
  refine ⟨hj, ?_⟩
  have hv : colour v = !(layerColour phase j) := by
    simpa [layerColour_succ] using hSelected.2
  have hu : colour u ≠ !(layerColour phase j) := by
    rw [← hv]
    exact hBipartite hNeighbour
  exact bool_eq_of_ne_not hu

/-- Every pair of selected conflicting tasks retains its logical layer order.
    Here a conflict means the same site or neighbouring sites. -/
theorem selected_conflict_order (colour : V → Bool) (phase : Bool)
    (hBipartite : ∀ {u v}, u ∈ M.neighbours v → colour u ≠ colour v)
    {a b : Nat} {u v : V} (ha : Selected colour phase a u)
    (hb : Selected colour phase b v) (hab : a < b)
    (hConflict : u = v ∨ u ∈ M.neighbours v) :
    M.completion a u < M.completion b v := by
  rcases hConflict with hSame | hNeighbour
  · subst u
    have heq : layerColour phase a = layerColour phase b := ha.2.symm.trans hb.2
    have hParity := (layerColour_eq_iff phase a b).mp heq
    exact M.same_site_even_order v hab (by omega)
  · have hne : layerColour phase a ≠ layerColour phase b := by
      rw [← ha.2, ← hb.2]
      exact hBipartite hNeighbour
    have hParity := (layerColour_ne_iff phase a b).mp hne
    exact M.neighbour_odd_order hNeighbour hab (by omega)

/-- The relative order agrees in both directions for every selected conflict. -/
theorem selected_conflict_order_iff (colour : V → Bool) (phase : Bool)
    (hBipartite : ∀ {u v}, u ∈ M.neighbours v → colour u ≠ colour v)
    {a b : Nat} {u v : V} (ha : Selected colour phase a u)
    (hb : Selected colour phase b v) (hConflict : u = v ∨ u ∈ M.neighbours v) :
    M.completion a u < M.completion b v ↔ a < b := by
  constructor
  · intro hTime
    by_cases hab : a = b
    · subst b
      rcases hConflict with hSame | hNeighbour
      · subst u
        omega
      · have hne := hBipartite hNeighbour
        exact False.elim (hne (ha.2.trans hb.2.symm))
    · by_cases hlt : a < b
      · exact hlt
      · have hba : b < a := by omega
        have hReverse : v = u ∨ v ∈ M.neighbours u := by
          rcases hConflict with hSame | hNeighbour
          · exact Or.inl hSame.symm
          · exact Or.inr (M.symmetric hNeighbour)
        have h := M.selected_conflict_order colour phase hBipartite hb ha hba hReverse
        omega
  · intro hab
    exact M.selected_conflict_order colour phase hBipartite ha hb hab hConflict

theorem selected_same_site_injective (colour : V → Bool) (phase : Bool)
    {a b : Nat} {v : V} (ha : Selected colour phase a v)
    (hb : Selected colour phase b v)
    (hTime : M.completion a v = M.completion b v) : a = b := by
  have heq : layerColour phase a = layerColour phase b := ha.2.symm.trans hb.2
  have hParity := (layerColour_eq_iff phase a b).mp heq
  by_cases hab : a = b
  · exact hab
  · by_cases hlt : a < b
    · have h := M.same_site_even_order v hlt (by omega)
      omega
    · have h := M.same_site_even_order v (by omega : b < a) (by omega)
      omega

theorem selected_same_site_no_reuse (colour : V → Bool) (phase : Bool)
    {a b : Nat} {v : V} (ha : Selected colour phase a v)
    (hb : Selected colour phase b v) (hab : a ≠ b) :
    M.completion a v ≠ M.completion b v := by
  intro hTime
  exact hab (M.selected_same_site_injective colour phase ha hb hTime)

/-- A deterministic site/time identifier, with no stochastic interpretation. -/
def eventId (j : Nat) (v : V) : V × Nat := (v, M.completion j v)

/-- Distinct selected tasks cannot share a site/time identifier. -/
theorem selected_event_injective (colour : V → Bool) (phase : Bool)
    {a b : Nat} {u v : V} (ha : Selected colour phase a u)
    (hb : Selected colour phase b v) (hEvent : M.eventId a u = M.eventId b v) :
    a = b ∧ u = v := by
  have hSite : u = v := congrArg Prod.fst hEvent
  subst u
  have hTime : M.completion a v = M.completion b v := congrArg Prod.snd hEvent
  exact ⟨M.selected_same_site_injective colour phase ha hb hTime, rfl⟩

end System
end MathResearch.Readiness
