module

public import MathResearchAnalysis.InfiniteGridModel
public import MathResearchAnalysis.SquareSpin
public import MathResearchAnalysis.FiniteMajorityPeeling
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

/-!
# Strict-majority deletion in the actual square grid

True represents a minus spin and false the plus background. A legal cleanup
deletion has fewer than two true neighbours. Ties are retained by cleanup.
The bridge uses the actual four-direction rule and the existing finite-square
single-site update; it does not introduce a different update convention.
-/

@[expose] public section

namespace MathResearchAnalysis.GridMajorityPeeling

open InfiniteGridModel
open scoped BigOperators

def neighbors4 (v : Site) : Finset Site := {north v, east v, south v, west v}

def state (S : Finset Site) (v : Site) : Bool := decide (v ∈ S)

def degree4 (S : Finset Site) (v : Site) : Nat := (neighbors4 v ∩ S).card

theorem mem_neighbors4 (v u : Site) :
    u ∈ neighbors4 v ↔ u = north v ∨ u = east v ∨ u = south v ∨ u = west v := by
  simp [neighbors4]

theorem not_mem_neighbors4_self (v : Site) : v ∉ neighbors4 v := by
  simp only [mem_neighbors4, north, east, south, west, Prod.ext_iff]
  omega

theorem sum_neighbors4 (f : Site → Nat) (v : Site) :
    ∑ u ∈ neighbors4 v, f u = f (north v) + f (east v) + f (south v) + f (west v) := by
  have hn : north v ∉ ({east v, south v, west v} : Finset Site) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, north, east, south, west, Prod.ext_iff]
    omega
  have he : east v ∉ ({south v, west v} : Finset Site) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, east, south, west, Prod.ext_iff]
    omega
  have hs : south v ∉ ({west v} : Finset Site) := by
    simp only [Finset.mem_singleton, south, west, Prod.ext_iff]
    omega
  simp [neighbors4, hn, he, hs, Nat.add_assoc]

theorem card_neighbors4 (v : Site) : (neighbors4 v).card = 4 := by
  rw [Finset.card_eq_sum_ones, sum_neighbors4]

theorem degree4_eq_sum (S : Finset Site) (v : Site) :
    degree4 S v = ∑ u ∈ neighbors4 v, (state S u).toNat := by
  unfold degree4
  rw [← Finset.filter_mem_eq_inter, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : u ∈ S <;> simp [state, h]

theorem degree4_eq_four_inputs (S : Finset Site) (v : Site) :
    degree4 S v = (state S (north v)).toNat + (state S (east v)).toNat +
      (state S (south v)).toNat + (state S (west v)).toNat := by
  rw [degree4_eq_sum, sum_neighbors4]

theorem strict_majority_update_false (S : Finset Site) (v : Site)
    (h : degree4 S v < 2) (marks : Marks) (t : Nat) :
    InfiniteGridModel.update marks t v (state S) = false := by
  apply majority4_at_most_one
  rw [← degree4_eq_four_inputs]
  omega

theorem state_erase (S : Finset Site) (v : Site) :
    state (S.erase v) = Function.update (state S) v false := by
  funext u
  by_cases h : u = v
  · subst u
    simp [state]
  · simp [state, Finset.mem_erase, h]

theorem actual_single_write_eq_erase (S : Finset Site) (v : Site)
    (h : degree4 S v < 2) (marks : Marks) (t : Nat) :
    Function.update (state S) v (InfiniteGridModel.update marks t v (state S)) =
      state (S.erase v) := by
  rw [strict_majority_update_false S v h marks t, state_erase]

def finiteState {n : Nat} (S : Finset (SquareTasks.Vertex n))
    (v : SquareTasks.Vertex n) : Bool := decide (v ∈ S)

theorem finite_ones_eq_degree {n : Nat} (S : Finset (SquareTasks.Vertex n))
    (v : SquareTasks.Vertex n) :
    SquareSpin.ones (finiteState S) v = (SquareTasks.neighbors n v ∩ S).card := by
  rw [← Finset.filter_mem_eq_inter, Finset.card_eq_sum_ones, Finset.sum_filter]
  unfold SquareSpin.ones
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : u ∈ S <;> simp [finiteState, h]

theorem finite_cellUpdate_eq_erase {n : Nat} (S : Finset (SquareTasks.Vertex n))
    (v : SquareTasks.Vertex n) (h : (SquareTasks.neighbors n v ∩ S).card < 2) (tie : Bool) :
    SquareSpin.cellUpdate (finiteState S) v tie = finiteState (S.erase v) := by
  have hr : SquareSpin.rule (finiteState S) v tie = false := by
    simp [SquareSpin.rule, finite_ones_eq_degree, h, show ¬ 2 < (SquareTasks.neighbors n v ∩ S).card by omega]
  unfold SquareSpin.cellUpdate
  rw [hr]
  funext u
  by_cases he : u = v
  · subst u
    simp [finiteState]
  · simp [finiteState, Finset.mem_erase, he]

theorem degree_two_update_is_tie (S : Finset Site) (v : Site)
    (h : degree4 S v = 2) (marks : Marks) (t : Nat) :
    InfiniteGridModel.update marks t v (state S) = marks t v := by
  unfold InfiniteGridModel.update majority4
  rw [← degree4_eq_four_inputs]
  simp [h]

def cleanup (S : Finset Site) : Finset Site :=
  FiniteMajorityPeeling.core neighbors4 S

theorem cleanup_subset (S : Finset Site) : cleanup S ⊆ S :=
  FiniteMajorityPeeling.core_subset neighbors4 S

theorem cleanup_stable (S : Finset Site) :
    ∀ v ∈ cleanup S, 2 ≤ degree4 (cleanup S) v := by
  intro v hv
  have hs := FiniteMajorityPeeling.stable_core neighbors4 S
  have hmem : v ∈ FiniteMajorityPeeling.prune neighbors4 (cleanup S) := by
    rw [show FiniteMajorityPeeling.prune neighbors4 (cleanup S) = cleanup S from hs]
    exact hv
  exact ((FiniteMajorityPeeling.mem_prune neighbors4 (cleanup S) v).mp hmem).2

theorem cleanup_mono {S T : Finset Site} (h : S ⊆ T) : cleanup S ⊆ cleanup T :=
  FiniteMajorityPeeling.core_mono neighbors4 h

theorem cleanup_idempotent (S : Finset Site) : cleanup (cleanup S) = cleanup S :=
  FiniteMajorityPeeling.core_idempotent neighbors4 S

theorem cleanup_reachable (S : Finset Site) :
    FiniteMajorityPeeling.Deletes neighbors4 S (cleanup S) :=
  FiniteMajorityPeeling.deletes_to_core neighbors4 S

theorem terminal_cleanup_unique {S T : Finset Site}
    (h : FiniteMajorityPeeling.Deletes neighbors4 S T)
    (ht : FiniteMajorityPeeling.Terminal neighbors4 T) : T = cleanup S :=
  FiniteMajorityPeeling.terminal_deletes_eq_core neighbors4 h ht

theorem legal_delete_is_actual_write {S T : Finset Site}
    (h : FiniteMajorityPeeling.Delete neighbors4 S T) (marks : Marks) (t : Nat) :
    ∃ v ∈ S, Function.update (state S) v (InfiniteGridModel.update marks t v (state S)) = state T := by
  obtain ⟨v, hv, hd, rfl⟩ := h
  exact ⟨v, hv, actual_single_write_eq_erase S v hd marks t⟩

def finiteCleanup {n : Nat} (S : Finset (SquareTasks.Vertex n)) :
    Finset (SquareTasks.Vertex n) := FiniteMajorityPeeling.core (SquareTasks.neighbors n) S

theorem finiteCleanup_reachable {n : Nat} (S : Finset (SquareTasks.Vertex n)) :
    FiniteMajorityPeeling.Deletes (SquareTasks.neighbors n) S (finiteCleanup S) :=
  FiniteMajorityPeeling.deletes_to_core (SquareTasks.neighbors n) S

theorem finite_legal_delete_is_cellUpdate {n : Nat} {S T : Finset (SquareTasks.Vertex n)}
    (h : FiniteMajorityPeeling.Delete (SquareTasks.neighbors n) S T) (tie : Bool) :
    ∃ v ∈ S, SquareSpin.cellUpdate (finiteState S) v tie = finiteState T := by
  obtain ⟨v, hv, hd, rfl⟩ := h
  exact ⟨v, hv, finite_cellUpdate_eq_erase S v hd tie⟩

end MathResearchAnalysis.GridMajorityPeeling
