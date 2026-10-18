module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Nat.Find
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Tactic

set_option autoImplicit false

/-!
# Genuine extended discrete recovery times

The first visit to the specified zero state is an extended natural number.
Samples that never visit zero have time infinity. No existence of a finite hit,
absorption, measurability or probability tail is assumed in the definition.
Absorption is needed only to replace a first-visit tail by the current state.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.ExtendedRecoveryTime

universe u v

variable {Ω : Type u} {State : Type v}

/-- The actual first zero time, with infinity precisely on samples that never hit zero. -/
def time (X : Nat → Ω → State) (zero : State) (ω : Ω) : ℕ∞ := by
  classical
  exact if h : ∃ s, X s ω = zero then (Nat.find h : ℕ∞) else ⊤

/-- A structural zero-absorption property, without any finite-hitting premise. -/
def Absorbing (X : Nat → Ω → State) (zero : State) : Prop :=
  ∀ ω {s t : Nat}, s ≤ t → X s ω = zero → X t ω = zero

theorem time_le_nat_iff (X : Nat → Ω → State) (zero : State) (ω : Ω) (t : Nat) :
    time X zero ω ≤ (t : ℕ∞) ↔ ∃ s ≤ t, X s ω = zero := by
  classical
  by_cases h : ∃ s, X s ω = zero
  · simpa only [time, dite_eq_left h, ENat.natCast_le_natCast] using Nat.find_le_iff h t
  · simp only [time, dite_eq_right h]
    constructor
    · intro ht
      exact False.elim ((not_le_of_gt (ENat.natCast_lt_top t)) ht)
    · rintro ⟨s, _, hs⟩
      exact False.elim (h ⟨s, hs⟩)

theorem time_eq_nat_iff (X : Nat → Ω → State) (zero : State) (ω : Ω) (t : Nat) :
    time X zero ω = (t : ℕ∞) ↔
      X t ω = zero ∧ ∀ s < t, X s ω ≠ zero := by
  classical
  by_cases h : ∃ s, X s ω = zero
  · simpa only [time, dite_eq_left h, ENat.natCast_inj] using Nat.find_eq_iff h
  · simp only [time, dite_eq_right h]
    constructor
    · intro ht
      exact False.elim ((ENat.top_ne_natCast t) ht)
    · intro ht
      exact False.elim (h ⟨t, ht.1⟩)

theorem time_eq_top_iff (X : Nat → Ω → State) (zero : State) (ω : Ω) :
    time X zero ω = ⊤ ↔ ∀ t, X t ω ≠ zero := by
  classical
  constructor
  · intro ht t hhit
    have hle := (time_le_nat_iff X zero ω t).mpr ⟨t, le_rfl, hhit⟩
    rw [ht] at hle
    exact (not_le_of_gt (ENat.natCast_lt_top t)) hle
  · intro hnever
    have hn : ¬ ∃ s, X s ω = zero := by
      rintro ⟨s, hs⟩
      exact hnever s hs
    simp only [time, dite_eq_right hn]

theorem time_ne_top_iff (X : Nat → Ω → State) (zero : State) (ω : Ω) :
    time X zero ω ≠ ⊤ ↔ ∃ t, X t ω = zero := by
  simpa only [not_forall, not_not] using not_congr (time_eq_top_iff X zero ω)

theorem time_le_nat_iff_of_absorbing (X : Nat → Ω → State) (zero : State)
    (absorbing : Absorbing X zero) (ω : Ω) (t : Nat) :
    time X zero ω ≤ (t : ℕ∞) ↔ X t ω = zero := by
  rw [time_le_nat_iff]
  constructor
  · rintro ⟨s, hst, hs⟩
    exact absorbing ω hst hs
  · intro ht
    exact ⟨t, le_rfl, ht⟩

/-- Under actual zero absorption, the recovery tail is exactly the nonzero-state event. -/
theorem time_gt_nat_iff_of_absorbing (X : Nat → Ω → State) (zero : State)
    (absorbing : Absorbing X zero) (ω : Ω) (t : Nat) :
    (t : ℕ∞) < time X zero ω ↔ X t ω ≠ zero := by
  simpa only [not_le] using not_congr
    (time_le_nat_iff_of_absorbing X zero absorbing ω t)

section Measurability

variable [MeasurableSpace Ω] [MeasurableSpace State] [MeasurableSingletonClass State]

theorem measurableSet_time_eq_nat (X : Nat → Ω → State) (zero : State)
    (measurable_X : ∀ t, Measurable (X t)) (t : Nat) :
    MeasurableSet {ω | time X zero ω = (t : ℕ∞)} := by
  have hhit : ∀ s, MeasurableSet {ω | X s ω = zero} :=
    fun s => (measurable_X s) (measurableSet_singleton zero)
  have hset : {ω | time X zero ω = (t : ℕ∞)} =
      {ω | X t ω = zero} ∩ ⋂ s : Nat, ⋂ (_ : s < t), {ω | X s ω ≠ zero} := by
    ext ω
    simp only [Set.mem_ofPred_eq, time_eq_nat_iff, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  exact (hhit t).inter (MeasurableSet.iInter fun s =>
    MeasurableSet.iInter fun (_ : s < t) => (hhit s).compl)

/-- Only measurable singleton zero and measurable time slices are needed; finite hits are not. -/
theorem time_measurable (X : Nat → Ω → State) (zero : State)
    (measurable_X : ∀ t, Measurable (X t)) : Measurable (time X zero) := by
  apply ENat.measurable_iff.mpr
  intro t
  exact measurableSet_time_eq_nat X zero measurable_X t

theorem measurableSet_time_le_nat (X : Nat → Ω → State) (zero : State)
    (measurable_X : ∀ t, Measurable (X t)) (t : Nat) :
    MeasurableSet {ω | time X zero ω ≤ (t : ℕ∞)} := by
  have hset : {ω | time X zero ω ≤ (t : ℕ∞)} =
      ⋃ s : Nat, ⋃ (_ : s ≤ t), {ω | X s ω = zero} := by
    ext ω
    simp only [Set.mem_ofPred_eq, time_le_nat_iff, Set.mem_iUnion, exists_prop]
  rw [hset]
  exact MeasurableSet.iUnion fun s => MeasurableSet.iUnion fun (_ : s ≤ t) =>
    (measurable_X s) (measurableSet_singleton zero)

theorem measurableSet_time_eq_top (X : Nat → Ω → State) (zero : State)
    (measurable_X : ∀ t, Measurable (X t)) :
    MeasurableSet {ω | time X zero ω = ⊤} := by
  exact (time_measurable X zero measurable_X) (measurableSet_singleton ⊤)

end Measurability

end MathResearchAnalysis.ExtendedRecoveryTime
