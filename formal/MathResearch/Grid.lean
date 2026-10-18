import MathResearch.Dynamics
import MathResearch.Majority

/-!
# The concrete four-neighbour square-lattice model

Tie marks are fixed deterministic Bool values.  This module instantiates the
bipartite splitting theorem with the actual majority rule and proves that a
square containing all initial ones remains a containing square.  No law or
independence of the marks, and no extinction-time estimate, is assumed here.
-/

namespace MathResearch.Grid

abbrev Site := Int × Int
abbrev Marks := Nat → Site → Bool

def north (v : Site) : Site := (v.1, v.2 + 1)
def east (v : Site) : Site := (v.1 + 1, v.2)
def south (v : Site) : Site := (v.1, v.2 - 1)
def west (v : Site) : Site := (v.1 - 1, v.2)

def colour (v : Site) : Bool := decide ((v.1 + v.2) % 2 = 0)

theorem north_opposite (v : Site) : colour (north v) ≠ colour v := by
  by_cases h : (v.1 + v.2) % 2 = 0
  · have hn : (v.1 + (v.2 + 1)) % 2 ≠ 0 := by omega
    simp [colour, north, h, hn]
  · have hn : (v.1 + (v.2 + 1)) % 2 = 0 := by omega
    simp [colour, north, h, hn]

theorem east_opposite (v : Site) : colour (east v) ≠ colour v := by
  by_cases h : (v.1 + v.2) % 2 = 0
  · have he : ((v.1 + 1) + v.2) % 2 ≠ 0 := by omega
    simp [colour, east, h, he]
  · have he : ((v.1 + 1) + v.2) % 2 = 0 := by omega
    simp [colour, east, h, he]

theorem south_opposite (v : Site) : colour (south v) ≠ colour v := by
  by_cases h : (v.1 + v.2) % 2 = 0
  · have hs : (v.1 + (v.2 - 1)) % 2 ≠ 0 := by omega
    simp [colour, south, h, hs]
  · have hs : (v.1 + (v.2 - 1)) % 2 = 0 := by omega
    simp [colour, south, h, hs]

theorem west_opposite (v : Site) : colour (west v) ≠ colour v := by
  by_cases h : (v.1 + v.2) % 2 = 0
  · have hw : ((v.1 - 1) + v.2) % 2 ≠ 0 := by omega
    simp [colour, west, h, hw]
  · have hw : ((v.1 - 1) + v.2) % 2 = 0 := by omega
    simp [colour, west, h, hw]

/-- Strict majority, with `marks t v` used exactly when two neighbours are 1. -/
def update (marks : Marks) (t : Nat) (v : Site) (state : State Site) : Bool :=
  Majority.update (state (north v)) (state (east v))
    (state (south v)) (state (west v)) (marks t v)

/-- The concrete lattice provides both hypotheses of the abstract dynamics. -/
def system (marks : Marks) : BipartiteSystem Site where
  colour := colour
  update := update marks
  opposite_local := by
    intro t v s r h
    unfold update
    rw [h (north v) (north_opposite v), h (east v) (east_opposite v),
      h (south v) (south_opposite v), h (west v) (west_opposite v)]
  zero_update := by
    intro t v
    exact Majority.zero_fixed (marks t v)

abbrev synchronous (marks : Marks) (initial : State Site) : Nat → State Site :=
  (system marks).synchronous initial

abbrev alternating (marks : Marks) (initial : State Site) (c : Bool) :
    Nat → State Site :=
  (system marks).alternating initial c

/-- The concrete lattice version of the active/inactive-colour identity. -/
theorem splitting (marks : Marks) (initial : State Site) (c : Bool)
    (t : Nat) (ht : 1 ≤ t) (v : Site) :
    alternating marks initial c t v =
      if colour v = activeColour c t then synchronous marks initial t v
      else synchronous marks initial (t - 1) v :=
  (system marks).splitting initial c t ht v

theorem absorption_times (marks : Marks) (initial : State Site) {T tf tt : Nat}
    (hT : FirstZero (synchronous marks initial) T)
    (hf : FirstZero (alternating marks initial false) tf)
    (ht : FirstZero (alternating marks initial true) tt) :
    T ≤ max tf tt ∧ max tf tt ≤ T + 1 :=
  (system marks).absorption_times initial hT hf ht

theorem finite_absorption_comparison (marks : Marks) (initial : State Site)
    (h : ∃ t, IsZero (synchronous marks initial t)) :
    ∃ T tf tt,
      FirstZero (synchronous marks initial) T ∧
      FirstZero (alternating marks initial false) tf ∧
      FirstZero (alternating marks initial true) tt ∧
      T ≤ max tf tt ∧ max tf tt ≤ T + 1 :=
  (system marks).finite_absorption_comparison initial h

/-- The half-open square `{0, ..., n-1}²`, including the empty case `n = 0`. -/
def Inside (n : Nat) (v : Site) : Prop :=
  0 ≤ v.1 ∧ v.1 < (n : Int) ∧ 0 ≤ v.2 ∧ v.2 < (n : Int)

instance (n : Nat) (v : Site) : Decidable (Inside n v) :=
  inferInstanceAs (Decidable (0 ≤ v.1 ∧ v.1 < (n : Int) ∧
    0 ≤ v.2 ∧ v.2 < (n : Int)))

/-- All nonzero coordinates lie in the square. -/
def Supported (n : Nat) (state : State Site) : Prop :=
  ∀ v, ¬ Inside n v → state v = false

theorem inside_of_north_east (n : Nat) (v : Site)
    (hn : Inside n (north v)) (he : Inside n (east v)) : Inside n v := by
  simp only [Inside, north, east] at *
  omega

theorem inside_of_north_south (n : Nat) (v : Site)
    (hn : Inside n (north v)) (hs : Inside n (south v)) : Inside n v := by
  simp only [Inside, north, south] at *
  omega

theorem inside_of_north_west (n : Nat) (v : Site)
    (hn : Inside n (north v)) (hw : Inside n (west v)) : Inside n v := by
  simp only [Inside, north, west] at *
  omega

theorem inside_of_east_south (n : Nat) (v : Site)
    (he : Inside n (east v)) (hs : Inside n (south v)) : Inside n v := by
  simp only [Inside, east, south] at *
  omega

theorem inside_of_east_west (n : Nat) (v : Site)
    (he : Inside n (east v)) (hw : Inside n (west v)) : Inside n v := by
  simp only [Inside, east, west] at *
  omega

theorem inside_of_south_west (n : Nat) (v : Site)
    (hs : Inside n (south v)) (hw : Inside n (west v)) : Inside n v := by
  simp only [Inside, south, west] at *
  omega

theorem inside_of_state_true (n : Nat) (state : State Site)
    (hSupport : Supported n state) {v : Site} (hv : state v = true) :
    Inside n v := by
  by_cases h : Inside n v
  · exact h
  · have hzero := hSupport v h
    rw [hv] at hzero
    contradiction

/-- An exterior site sees at most one nonzero neighbour in a supported state.
    The geometric fact is proved for all six pairs of distinct directions. -/
theorem neighbour_ones_le_one (n : Nat) (state : State Site) (v : Site)
    (hOutside : ¬ Inside n v) (hSupport : Supported n state) :
    (state (north v)).toNat + (state (east v)).toNat +
      (state (south v)).toNat + (state (west v)).toNat ≤ 1 := by
  have hne : state (north v) = true → state (east v) = true → False := by
    intro hn he
    exact hOutside (inside_of_north_east n v
      (inside_of_state_true n state hSupport hn) (inside_of_state_true n state hSupport he))
  have hns : state (north v) = true → state (south v) = true → False := by
    intro hn hs
    exact hOutside (inside_of_north_south n v
      (inside_of_state_true n state hSupport hn) (inside_of_state_true n state hSupport hs))
  have hnw : state (north v) = true → state (west v) = true → False := by
    intro hn hw
    exact hOutside (inside_of_north_west n v
      (inside_of_state_true n state hSupport hn) (inside_of_state_true n state hSupport hw))
  have hes : state (east v) = true → state (south v) = true → False := by
    intro he hs
    exact hOutside (inside_of_east_south n v
      (inside_of_state_true n state hSupport he) (inside_of_state_true n state hSupport hs))
  have hew : state (east v) = true → state (west v) = true → False := by
    intro he hw
    exact hOutside (inside_of_east_west n v
      (inside_of_state_true n state hSupport he) (inside_of_state_true n state hSupport hw))
  have hsw : state (south v) = true → state (west v) = true → False := by
    intro hs hw
    exact hOutside (inside_of_south_west n v
      (inside_of_state_true n state hSupport hs) (inside_of_state_true n state hSupport hw))
  cases hn : state (north v) <;> cases he : state (east v) <;>
    cases hs : state (south v) <;> cases hw : state (west v) <;> simp_all

/-- The purely geometric count of interior neighbours of an exterior site. -/
theorem inside_neighbours_le_one (n : Nat) (v : Site) (hOutside : ¬ Inside n v) :
    (decide (Inside n (north v))).toNat + (decide (Inside n (east v))).toNat +
      (decide (Inside n (south v))).toNat + (decide (Inside n (west v))).toNat ≤ 1 := by
  apply neighbour_ones_le_one n (fun w => decide (Inside n w)) v hOutside
  intro w hw
  simp [hw]

/-- The actual update cannot create a one outside the containing square. -/
theorem update_supported (marks : Marks) (t n : Nat) (state : State Site)
    (hSupport : Supported n state) :
    Supported n (fun v => update marks t v state) := by
  intro v hOutside
  exact Majority.at_most_one _ _ _ _ _
    (neighbour_ones_le_one n state v hOutside hSupport)

/-- Updating a single site also preserves the same containing square. -/
def singleSiteUpdate (marks : Marks) (t : Nat) (v : Site) (state : State Site) :
    State Site :=
  fun w => if w = v then update marks t v state else state w

theorem singleSiteUpdate_supported (marks : Marks) (t n : Nat) (v : Site)
    (state : State Site) (hSupport : Supported n state) :
    Supported n (singleSiteUpdate marks t v state) := by
  intro w hOutside
  by_cases hw : w = v
  · subst w
    simp only [singleSiteUpdate]
    exact update_supported marks t n state hSupport v hOutside
  · simp only [singleSiteUpdate, ite_eq_right hw]
    exact hSupport w hOutside

theorem synchronous_supported (marks : Marks) (n : Nat) (initial : State Site)
    (hSupport : Supported n initial) (t : Nat) :
    Supported n (synchronous marks initial t) := by
  induction t with
  | zero => exact hSupport
  | succ t ih =>
    exact update_supported marks (t + 1) n (synchronous marks initial t) ih

theorem alternating_supported (marks : Marks) (n : Nat) (initial : State Site)
    (hSupport : Supported n initial) (c : Bool) (t : Nat) :
    Supported n (alternating marks initial c t) := by
  cases t with
  | zero => exact hSupport
  | succ t =>
    intro v hOutside
    change (system marks).alternating initial c (t + 1) v = false
    rw [(system marks).splitting_succ initial c t v]
    change (if colour v = activeColour c (t + 1) then
      synchronous marks initial (t + 1) v else synchronous marks initial t v) = false
    by_cases hc : colour v = activeColour c (t + 1)
    · rw [ite_eq_left hc]
      exact synchronous_supported marks n initial hSupport (t + 1) v hOutside
    · rw [ite_eq_right hc]
      exact synchronous_supported marks n initial hSupport t v hOutside

end MathResearch.Grid
