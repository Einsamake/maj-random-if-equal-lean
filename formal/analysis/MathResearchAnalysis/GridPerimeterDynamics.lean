module

public import MathResearchAnalysis.GridPerimeterUpdate
public import MathResearchAnalysis.DropletModifiedWord

set_option autoImplicit false

/-!
# Actual majority-word and forced-cleanup perimeter budgets

Perimeter means the number of actual exposed cell facets, each of physical
length one. Forced deletions cost at least two perimeter units per erased
site. The genuine four-input majority write never increases perimeter,
including for unstable occupied sets. These are deterministic event-index
statements; no synchronous or physical-time estimate is asserted here.
-/

@[expose] public section

namespace MathResearchAnalysis.GridPerimeterDynamics

open GridCellBoundary (Site perimeter)
open GridMajorityPeeling
open GridPerimeterUpdate (perimeter_insert perimeter_erase)
open DropletModifiedWord

theorem delete_perimeter_drop {S T : Finset Site}
    (h : FiniteMajorityPeeling.Delete neighbors4 S T) :
    perimeter T + 2 ≤ perimeter S := by
  obtain ⟨v, hv, hd, rfl⟩ := h
  have hp := perimeter_erase S v hv
  have hd' : degree4 S v < 2 := hd
  omega

theorem delete_perimeter_card_budget {S T : Finset Site}
    (h : FiniteMajorityPeeling.Delete neighbors4 S T) :
    perimeter T + 2 * S.card ≤ perimeter S + 2 * T.card := by
  have hp := delete_perimeter_drop h
  obtain ⟨v, hv, _, rfl⟩ := h
  have hc := Finset.card_erase_add_one hv
  omega

theorem deletes_perimeter_card_budget {S T : Finset Site}
    (h : FiniteMajorityPeeling.Deletes neighbors4 S T) :
    perimeter T + 2 * S.card ≤ perimeter S + 2 * T.card := by
  induction h with
  | refl => omega
  | tail _ hstep ih =>
    have hp := delete_perimeter_card_budget hstep
    omega

theorem cleanup_perimeter_card_budget (S : Finset Site) :
    perimeter (cleanup S) + 2 * S.card ≤ perimeter S + 2 * (cleanup S).card :=
  deletes_perimeter_card_budget (cleanup_reachable S)

theorem cleanup_perimeter_le (S : Finset Site) : perimeter (cleanup S) ≤ perimeter S := by
  have hp := cleanup_perimeter_card_budget S
  have hc := Finset.card_le_card (cleanup_subset S)
  omega

theorem localRule_true_degree_ge_two (S : Finset Site) (v : Site) (tie : Bool)
    (h : localRule S v tie = true) : 2 ≤ degree4 S v := by
  by_contra hn
  have hl : degree4 S v < 2 := by omega
  have hg : ¬ 2 < degree4 S v := by omega
  simp [localRule, InfiniteGridModel.majority4, ← degree4_eq_four_inputs, hg, hl] at h

theorem localRule_false_degree_le_two (S : Finset Site) (v : Site) (tie : Bool)
    (h : localRule S v tie = false) : degree4 S v ≤ 2 := by
  by_contra hn
  have hg : 2 < degree4 S v := by omega
  simp [localRule, InfiniteGridModel.majority4, ← degree4_eq_four_inputs, hg] at h

theorem rawStep_perimeter_le (S : Finset Site) (v : Site) (tie : Bool) :
    perimeter (rawStep S v tie) ≤ perimeter S := by
  cases ht : localRule S v tie with
  | false =>
    have heq : rawStep S v tie = S.erase v := by simp [rawStep, ht]
    rw [heq]
    by_cases hv : v ∈ S
    · have hd := localRule_false_degree_le_two S v tie ht
      have hp := perimeter_erase S v hv
      omega
    · simp [Finset.erase_eq_of_notMem hv]
  | true =>
    have heq : rawStep S v tie = insert v S := by simp [rawStep, ht]
    rw [heq]
    by_cases hv : v ∈ S
    · simp [Finset.insert_eq_of_mem hv]
    · have hd := localRule_true_degree_ge_two S v tie ht
      have hp := perimeter_insert S v hv
      omega

theorem maskedRawStep_perimeter_le (D S : Finset Site) (v : Site) (tie : Bool) :
    perimeter (maskedRawStep D S v tie) ≤ perimeter S := by
  by_cases hv : v ∈ D
  · simpa only [maskedRawStep, ite_eq_left hv] using rawStep_perimeter_le S v tie
  · simp [maskedRawStep, hv]

theorem modifiedStep_perimeter_le (D S : Finset Site) (v : Site) (tie : Bool) :
    perimeter (modifiedStep D S v tie) ≤ perimeter S := by
  by_cases hv : v ∈ D
  · simp only [modifiedStep, ite_eq_left hv]
    exact le_trans (cleanup_perimeter_le _) (rawStep_perimeter_le S v tie)
  · simp [modifiedStep, hv]

theorem rawWord_perimeter_le (D S : Finset Site) (w : List Event) :
    perimeter (rawWord D S w) ≤ perimeter S := by
  induction w generalizing S with
  | nil => simp
  | cons e w ih =>
    rw [rawWord_cons]
    exact le_trans (ih _) (maskedRawStep_perimeter_le D S e.1 e.2)

theorem modifiedWord_perimeter_le (D S : Finset Site) (w : List Event) :
    perimeter (modifiedWord D S w) ≤ perimeter S := by
  induction w generalizing S with
  | nil => simp
  | cons e w ih =>
    rw [modifiedWord_cons]
    exact le_trans (ih _) (modifiedStep_perimeter_le D S e.1 e.2)


/-- Extra occupied sites erased by cleanup after this masked majority event. -/
def eventLoss (D S : Finset Site) (e : Event) : Nat :=
  (maskedRawStep D S e.1 e.2).card - (modifiedStep D S e.1 e.2).card

/-- Total extra cleanup deletions, along the actual evolving modified word. -/
def wordLoss (D S : Finset Site) : List Event → Nat
  | [] => 0
  | e :: w => eventLoss D S e + wordLoss D (modifiedStep D S e.1 e.2) w

theorem eventLoss_of_not_mem (D S : Finset Site) (e : Event) (hv : e.1 ∉ D) :
    eventLoss D S e = 0 := by
  simp [eventLoss, maskedRawStep, modifiedStep, hv]

theorem modifiedStep_perimeter_loss_budget (D S : Finset Site) (e : Event) :
    perimeter (modifiedStep D S e.1 e.2) + 2 * eventLoss D S e ≤ perimeter S := by
  by_cases hv : e.1 ∈ D
  · simp only [modifiedStep, eventLoss, maskedRawStep, ite_eq_left hv]
    have hc := cleanup_perimeter_card_budget (rawStep S e.1 e.2)
    have hcard := Finset.card_le_card (cleanup_subset (rawStep S e.1 e.2))
    have hloss := Nat.sub_add_cancel hcard
    have hp := rawStep_perimeter_le S e.1 e.2
    omega
  · simp [modifiedStep, eventLoss_of_not_mem D S e hv, hv]

theorem modifiedWord_perimeter_loss_budget (D S : Finset Site) (w : List Event) :
    perimeter (modifiedWord D S w) + 2 * wordLoss D S w ≤ perimeter S := by
  induction w generalizing S with
  | nil => simp [wordLoss]
  | cons e w ih =>
    rw [modifiedWord_cons, wordLoss]
    have hhead := modifiedStep_perimeter_loss_budget D S e
    have htail := ih (modifiedStep D S e.1 e.2)
    omega

theorem twice_wordLoss_le_perimeter (D S : Finset Site) (w : List Event) :
    2 * wordLoss D S w ≤ perimeter S := by
  have h := modifiedWord_perimeter_loss_budget D S w
  omega

end MathResearchAnalysis.GridPerimeterDynamics
