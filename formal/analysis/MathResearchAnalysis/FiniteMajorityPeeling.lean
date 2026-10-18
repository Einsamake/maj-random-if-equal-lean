module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Logic.Relation
public import Mathlib.Tactic

set_option autoImplicit false

/-!
# Finite strict-majority peeling

Only the occupied set is finite; the ambient vertex type may be infinite.
Pruning deletes occupied vertices with fewer than two occupied neighbours.
The core is a bounded iterate, whose stability and maximality are proved.
Every terminal legal single-deletion chain has this same endpoint.
No claim about simple contours or the CMST good set is made here.
-/

public section

namespace MathResearchAnalysis.FiniteMajorityPeeling

universe u

variable {V : Type u} [DecidableEq V]

@[expose] def degree (neighbors : V → Finset V) (S : Finset V) (v : V) : Nat :=
  (neighbors v ∩ S).card

@[expose] def prune (neighbors : V → Finset V) (S : Finset V) : Finset V :=
  S.filter (fun v => 2 ≤ degree neighbors S v)

@[expose] def iteratePrune (neighbors : V → Finset V) (k : Nat) (S : Finset V) :
    Finset V := (prune neighbors)^[k] S

@[expose] def core (neighbors : V → Finset V) (S : Finset V) : Finset V :=
  iteratePrune neighbors S.card S

@[expose] def Stable (neighbors : V → Finset V) (S : Finset V) : Prop :=
  prune neighbors S = S

@[expose] def Delete (neighbors : V → Finset V) (S T : Finset V) : Prop :=
  ∃ v ∈ S, degree neighbors S v < 2 ∧ T = S.erase v

@[expose] def Deletes (neighbors : V → Finset V) (S T : Finset V) : Prop :=
  Relation.ReflTransGen (Delete neighbors) S T

@[expose] def Terminal (neighbors : V → Finset V) (S : Finset V) : Prop :=
  ¬ ∃ T, Delete neighbors S T

variable (neighbors : V → Finset V)

theorem mem_prune (S : Finset V) (v : V) :
    v ∈ prune neighbors S ↔ v ∈ S ∧ 2 ≤ degree neighbors S v :=
  Finset.mem_filter

theorem prune_subset (S : Finset V) : prune neighbors S ⊆ S := Finset.filter_subset _ _

theorem degree_mono {S T : Finset V} (hST : S ⊆ T) (v : V) :
    degree neighbors S v ≤ degree neighbors T v := by
  apply Finset.card_le_card
  intro w hw
  exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hw).1, hST (Finset.mem_inter.mp hw).2⟩

theorem prune_mono {S T : Finset V} (hST : S ⊆ T) :
    prune neighbors S ⊆ prune neighbors T := by
  intro v hv
  obtain ⟨hvS, hvdeg⟩ := (mem_prune neighbors S v).mp hv
  exact (mem_prune neighbors T v).mpr
    ⟨hST hvS, le_trans hvdeg (degree_mono neighbors hST v)⟩

theorem stable_iff (S : Finset V) :
    Stable neighbors S ↔ ∀ v ∈ S, 2 ≤ degree neighbors S v := by
  exact Finset.filter_eq_self

theorem iteratePrune_succ (k : Nat) (S : Finset V) :
    iteratePrune neighbors (k + 1) S = prune neighbors (iteratePrune neighbors k S) :=
  Function.iterate_succ_apply' _ _ _

theorem iteratePrune_add (k l : Nat) (S : Finset V) :
    iteratePrune neighbors (k + l) S =
      iteratePrune neighbors k (iteratePrune neighbors l S) :=
  Function.iterate_add_apply _ _ _ _

theorem iteratePrune_subset (k : Nat) (S : Finset V) : iteratePrune neighbors k S ⊆ S := by
  induction k with
  | zero => exact Finset.Subset.refl S
  | succ k ih =>
    rw [iteratePrune_succ]
    exact Finset.Subset.trans (prune_subset neighbors _) ih

theorem exists_stable_iterate (S : Finset V) :
    ∃ k ≤ S.card, Stable neighbors (iteratePrune neighbors k S) := by
  classical
  refine Finset.strongInductionOn S ?_
  intro S ih
  by_cases hS : Stable neighbors S
  · exact ⟨0, Nat.zero_le _, hS⟩
  · have hlt : prune neighbors S ⊂ S :=
      Finset.ssubset_iff_subset_ne.mpr ⟨prune_subset neighbors S, hS⟩
    obtain ⟨k, hk, hstable⟩ := ih (prune neighbors S) hlt
    refine ⟨k + 1, by have hc := Finset.card_lt_card hlt; omega, ?_⟩
    simpa only [iteratePrune, Function.iterate_succ_apply] using hstable

theorem stable_core (S : Finset V) : Stable neighbors (core neighbors S) := by
  obtain ⟨k, hk, hstable⟩ := exists_stable_iterate neighbors S
  have heq : core neighbors S = iteratePrune neighbors k S := by
    unfold core
    rw [← Nat.sub_add_cancel hk, iteratePrune_add]
    exact Function.iterate_fixed hstable _
  rw [heq]
  exact hstable

theorem core_subset (S : Finset V) : core neighbors S ⊆ S :=
  iteratePrune_subset neighbors S.card S

theorem stable_subset_iterate {R S : Finset V} (hR : Stable neighbors R) (hRS : R ⊆ S)
    (k : Nat) : R ⊆ iteratePrune neighbors k S := by
  induction k with
  | zero => exact hRS
  | succ k ih =>
    rw [iteratePrune_succ]
    calc
      R = prune neighbors R := hR.symm
      _ ⊆ prune neighbors (iteratePrune neighbors k S) := prune_mono neighbors ih

theorem core_greatest {R S : Finset V} (hR : Stable neighbors R) (hRS : R ⊆ S) :
    R ⊆ core neighbors S := stable_subset_iterate neighbors hR hRS S.card

theorem core_mono {S T : Finset V} (hST : S ⊆ T) : core neighbors S ⊆ core neighbors T :=
  core_greatest neighbors (stable_core neighbors S)
    (Finset.Subset.trans (core_subset neighbors S) hST)

theorem core_eq_self {S : Finset V} (hS : Stable neighbors S) : core neighbors S = S :=
  Function.iterate_fixed hS S.card

theorem core_idempotent (S : Finset V) : core neighbors (core neighbors S) = core neighbors S :=
  core_eq_self neighbors (stable_core neighbors S)

theorem terminal_iff_stable (S : Finset V) : Terminal neighbors S ↔ Stable neighbors S := by
  classical
  rw [stable_iff]
  constructor
  · intro h v hv
    by_contra hdeg
    exact h ⟨S.erase v, v, hv, by omega, rfl⟩
  · intro h hdel
    obtain ⟨T, v, hv, hdeg, _⟩ := hdel
    have := h v hv
    omega

theorem delete_subset {S T : Finset V} (h : Delete neighbors S T) : T ⊆ S := by
  obtain ⟨v, _, _, rfl⟩ := h
  exact Finset.erase_subset _ _

theorem delete_card_lt {S T : Finset V} (h : Delete neighbors S T) : T.card < S.card := by
  obtain ⟨v, hv, _, rfl⟩ := h
  exact Finset.card_erase_lt_of_mem hv

theorem stable_subset_delete {R S T : Finset V} (hR : Stable neighbors R)
    (hRS : R ⊆ S) (hdel : Delete neighbors S T) : R ⊆ T := by
  obtain ⟨v, _, hdeg, rfl⟩ := hdel
  intro w hw
  apply Finset.mem_erase.mpr
  constructor
  · intro heq
    subst w
    have hRdeg := (stable_iff neighbors R).mp hR v hw
    have hmono := degree_mono neighbors hRS v
    omega
  · exact hRS hw

theorem deletes_subset {S T : Finset V} (h : Deletes neighbors S T) : T ⊆ S := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | tail _ hstep ih => exact Finset.Subset.trans (delete_subset neighbors hstep) ih

theorem stable_subset_deletes {R S T : Finset V} (hR : Stable neighbors R)
    (hRS : R ⊆ S) (h : Deletes neighbors S T) : R ⊆ T := by
  induction h with
  | refl => exact hRS
  | tail _ hstep ih => exact stable_subset_delete neighbors hR ih hstep

theorem exists_terminal_deletes (S : Finset V) :
    ∃ T, Deletes neighbors S T ∧ Terminal neighbors T := by
  classical
  refine Finset.strongInductionOn S ?_
  intro S ih
  by_cases hterm : Terminal neighbors S
  · exact ⟨S, Relation.ReflTransGen.refl, hterm⟩
  · obtain ⟨T, hstep⟩ := not_not.mp hterm
    have hlt : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr
      ⟨delete_subset neighbors hstep, by
        intro heq
        have hc := delete_card_lt neighbors hstep
        rw [heq] at hc
        exact Nat.lt_irrefl _ hc⟩
    obtain ⟨U, hchain, hterminal⟩ := ih T hlt
    exact ⟨U, Relation.ReflTransGen.head hstep hchain, hterminal⟩

theorem terminal_deletes_eq_core {S T : Finset V} (hchain : Deletes neighbors S T)
    (hterminal : Terminal neighbors T) : T = core neighbors S := by
  apply Finset.Subset.antisymm
  · exact core_greatest neighbors ((terminal_iff_stable neighbors T).mp hterminal)
      (deletes_subset neighbors hchain)
  · exact stable_subset_deletes neighbors (stable_core neighbors S)
      (core_subset neighbors S) hchain

theorem deletes_to_core (S : Finset V) : Deletes neighbors S (core neighbors S) := by
  obtain ⟨T, hchain, hterminal⟩ := exists_terminal_deletes neighbors S
  rw [terminal_deletes_eq_core neighbors hchain hterminal] at hchain
  exact hchain

theorem terminal_deletion_order_independent {S T U : Finset V}
    (hT : Deletes neighbors S T) (ht : Terminal neighbors T)
    (hU : Deletes neighbors S U) (hu : Terminal neighbors U) : T = U :=
  (terminal_deletes_eq_core neighbors hT ht).trans
    (terminal_deletes_eq_core neighbors hU hu).symm

end MathResearchAnalysis.FiniteMajorityPeeling
