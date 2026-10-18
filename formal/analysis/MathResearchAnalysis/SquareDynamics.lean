module

public import MathResearchAnalysis.BipartiteDynamics
public import MathResearchAnalysis.SquareSpin

set_option autoImplicit false

/-!
# Actual square-spin synchronous / checkerboard splitting

The zero-boundary four-neighbor majority rule supplies the bipartite locality
and zero preservation proofs. They are not assumptions of the final square
model. Both checkerboard trajectories use the same predetermined site marks
as synchronous dynamics at each slot. No fresh or independent marks are claimed.

Phase is the initialization color. Slot `t + 1` reads `marks (t + 1)` and
updates color `activeColour phase (t + 1)`, so the first positive slot updates
`!phase`. The core source migration and compiler boundary are recorded in
`BipartiteDynamics.lean`; this module only imports analysis-project oleans.
All absorption comparisons below are deterministic and conditional on finite
absorption witnesses. They do not establish a probabilistic time bound.
-/

public section

namespace MathResearchAnalysis.SquareDynamics

open SquareTasks BipartiteDynamics

abbrev Mark (n : ℕ) := Vertex n → Bool
abbrev Marks (n : ℕ) := ℕ → Mark n

/-- The actual square rule, with its locality and absorbing-zero proofs discharged. -/
@[expose] def system {n : ℕ} (marks : Marks n) : BipartiteSystem (Vertex n) where
  colour := SquareTasks.colour
  update := fun t v f => SquareSpin.rule f v (marks t v)
  opposite_local := by
    intro t v f g h
    apply SquareSpin.rule_reads_only
    intro u hu
    apply h u
    rw [adjacent_colour_flip hu]
    simp
  zero_update := fun t v => SquareSpin.rule_zero v (marks t v)

/-- Synchronous trajectory for the actual square rule and a fixed common mark field. -/
@[expose] def synchronous {n : ℕ} (marks : Marks n) (initial : SquareSpin.Config n) :
    ℕ → SquareSpin.Config n := (system marks).synchronous initial

/-- Checkerboard trajectory; phase records the color at initialization. -/
@[expose] def alternating {n : ℕ} (marks : Marks n) (initial : SquareSpin.Config n)
    (phase : Bool) : ℕ → SquareSpin.Config n :=
  (system marks).alternating initial phase

@[simp] theorem synchronous_zero {n : ℕ} (marks : Marks n) (initial : SquareSpin.Config n) :
    synchronous marks initial 0 = initial := rfl

@[simp] theorem alternating_zero {n : ℕ} (marks : Marks n) (initial : SquareSpin.Config n)
    (phase : Bool) : alternating marks initial phase 0 = initial := rfl

/-- The real synchronous step receives the mark at the positive output slot. -/
theorem synchronous_succ {n : ℕ} (marks : Marks n) (initial : SquareSpin.Config n)
    (t : ℕ) : synchronous marks initial (t + 1) =
      SquareSpin.synchronousStep (synchronous marks initial t) (marks (t + 1)) := rfl

/-- The abstract alternating step is definitionally the actual checkerboard step. -/
theorem alternating_succ {n : ℕ} (marks : Marks n) (initial : SquareSpin.Config n)
    (phase : Bool) (t : ℕ) : alternating marks initial phase (t + 1) =
      SquareSpin.checkerboardStep (alternating marks initial phase t)
        (activeColour phase (t + 1)) (marks (t + 1)) := rfl

/-- Task layer zero is positive slot one and updates the opposite initialization phase. -/
theorem mem_tasks_positive_slot (n : ℕ) (phase : Bool) (k : ℕ) (v : Vertex n) :
    v ∈ tasks n (!phase) k ↔ SquareTasks.colour v = activeColour phase (k + 1) := by
  rw [mem_tasks_positive_layer, activeColour_eq_parity]

theorem splitting_succ {n : ℕ} (marks : Marks n) (initial : SquareSpin.Config n)
    (phase : Bool) (t : ℕ) (v : Vertex n) :
    alternating marks initial phase (t + 1) v =
      if SquareTasks.colour v = activeColour phase (t + 1) then
        synchronous marks initial (t + 1) v else synchronous marks initial t v :=
  (system marks).splitting_succ initial phase t v

theorem splitting {n : ℕ} (marks : Marks n) (initial : SquareSpin.Config n)
    (phase : Bool) (t : ℕ) (ht : 1 ≤ t) (v : Vertex n) :
    alternating marks initial phase t v =
      if SquareTasks.colour v = activeColour phase t then
        synchronous marks initial t v else synchronous marks initial (t - 1) v :=
  (system marks).splitting initial phase t ht v

theorem active_value {n : ℕ} (marks : Marks n) (initial : SquareSpin.Config n)
    (phase : Bool) (t : ℕ) (ht : 1 ≤ t) (v : Vertex n)
    (hv : SquareTasks.colour v = activeColour phase t) :
    alternating marks initial phase t v = synchronous marks initial t v :=
  (system marks).active_value initial phase t ht v hv

theorem inactive_value {n : ℕ} (marks : Marks n) (initial : SquareSpin.Config n)
    (phase : Bool) (t : ℕ) (ht : 1 ≤ t) (v : Vertex n)
    (hv : SquareTasks.colour v ≠ activeColour phase t) :
    alternating marks initial phase t v = synchronous marks initial (t - 1) v :=
  (system marks).inactive_value initial phase t ht v hv

/-- At each site, one of the two common-mark checkerboard trajectories supplies the synchronous value. -/
theorem synchronous_reconstruct {n : ℕ} (marks : Marks n) (initial : SquareSpin.Config n)
    (t : ℕ) (v : Vertex n) : synchronous marks initial t v =
      if SquareTasks.colour v = activeColour false t then alternating marks initial false t v
      else alternating marks initial true t v := by
  cases t with
  | zero => split_ifs <;> rfl
  | succ t =>
    by_cases h : SquareTasks.colour v = activeColour false (t + 1)
    · rw [ite_eq_left h]
      exact (active_value marks initial false (t + 1) (by omega) v h).symm
    · rw [ite_eq_right h]
      have h' : SquareTasks.colour v = !(activeColour false (t + 1)) := by
        cases hc : SquareTasks.colour v <;>
          cases ha : activeColour false (t + 1) <;> simp_all
      have htrue : SquareTasks.colour v = activeColour true (t + 1) := by
        rw [show true = !false from rfl, activeColour_complement]
        exact h'
      exact (active_value marks initial true (t + 1) (by omega) v htrue).symm

theorem synchronous_zero_persists {n : ℕ} (marks : Marks n) (initial : SquareSpin.Config n)
    {t s : ℕ} (hz : IsZero (synchronous marks initial t)) (hle : t ≤ s) :
    IsZero (synchronous marks initial s) :=
  (system marks).synchronous_zero_persists initial hz hle

theorem alternating_zero_persists {n : ℕ} (marks : Marks n) (initial : SquareSpin.Config n)
    (phase : Bool) {t s : ℕ} (hz : IsZero (alternating marks initial phase t)) (hle : t ≤ s) :
    IsZero (alternating marks initial phase s) :=
  (system marks).alternating_zero_persists initial phase hz hle

theorem synchronous_zero_implies_alternating_next_zero {n : ℕ} (marks : Marks n)
    (initial : SquareSpin.Config n) (phase : Bool) (t : ℕ)
    (hz : IsZero (synchronous marks initial t)) :
    IsZero (alternating marks initial phase (t + 1)) :=
  (system marks).synchronous_zero_implies_alternating_next_zero initial phase t hz

theorem both_alternating_zero_implies_synchronous_zero {n : ℕ} (marks : Marks n)
    (initial : SquareSpin.Config n) (t : ℕ)
    (hf : IsZero (alternating marks initial false t))
    (ht : IsZero (alternating marks initial true t)) :
    IsZero (synchronous marks initial t) :=
  (system marks).both_alternating_zero_implies_synchronous_zero initial t hf ht

/-- A pathwise equivalence of absorption witnesses, without asserting that a witness exists. -/
theorem eventually_zero_iff {n : ℕ} (marks : Marks n) (initial : SquareSpin.Config n) :
    (∃ t, IsZero (synchronous marks initial t)) ↔
      (∃ t, IsZero (alternating marks initial false t)) ∧
      (∃ t, IsZero (alternating marks initial true t)) :=
  (system marks).eventually_zero_iff initial

theorem absorption_times {n : ℕ} (marks : Marks n) (initial : SquareSpin.Config n)
    {T tf tt : ℕ} (hT : FirstZero (synchronous marks initial) T)
    (hf : FirstZero (alternating marks initial false) tf)
    (ht : FirstZero (alternating marks initial true) tt) :
    T ≤ max tf tt ∧ max tf tt ≤ T + 1 :=
  (system marks).absorption_times initial hT hf ht

/-- Any actual finite synchronous absorption witness gives the one-slot first-time bracket. -/
theorem finite_absorption_comparison {n : ℕ} (marks : Marks n) (initial : SquareSpin.Config n)
    (h : ∃ t, IsZero (synchronous marks initial t)) :
    ∃ T tf tt, FirstZero (synchronous marks initial) T ∧
      FirstZero (alternating marks initial false) tf ∧
      FirstZero (alternating marks initial true) tt ∧
      T ≤ max tf tt ∧ max tf tt ≤ T + 1 :=
  (system marks).finite_absorption_comparison initial h

end MathResearchAnalysis.SquareDynamics
