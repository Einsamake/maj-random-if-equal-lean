module

public import MathResearchAnalysis.DropletModifiedWord
public import MathResearchAnalysis.ClippedProtectedGeometry

set_option autoImplicit false

/-!
# Exact local criteria for cleanup after actual deletions

The degree formulas use actual four-neighbour adjacency. Single deletion is
stable precisely when every surviving occupied neighbour had degree at least
three. A two-site cleanup result is conditional on explicit original local
degrees of all survivors; no claim that Good geometry supplies these conditions
is stored here.
-/

@[expose] public section

namespace MathResearchAnalysis.GridCleanupDeletion

open InfiniteGridModel (Site)
open GridMajorityPeeling
open DropletModifiedWord (Stable)

/-- Exact neighbour loss, written additively to avoid truncated subtraction. -/
theorem degree4_erase_add (S : Finset Site) (u v : Site) :
    degree4 (S.erase v) u + (if v ∈ neighbors4 u ∧ v ∈ S then 1 else 0) = degree4 S u := by
  unfold degree4
  rw [Finset.inter_erase]
  by_cases hv : v ∈ neighbors4 u ∩ S
  · simpa only [Finset.mem_inter.mp hv, and_self, ite_true] using Finset.card_erase_add_one hv
  · have hn : ¬ (v ∈ neighbors4 u ∧ v ∈ S) := by simpa only [Finset.mem_inter] using hv
    simp [hn]

theorem degree4_erase_of_not_adjacent (S : Finset Site) (u v : Site)
    (h : v ∉ neighbors4 u) : degree4 (S.erase v) u = degree4 S u := by
  simpa only [h, false_and, ite_false, Nat.add_zero] using degree4_erase_add S u v

theorem degree4_erase_add_one {S : Finset Site} {u v : Site}
    (hv : v ∈ S) (h : v ∈ neighbors4 u) : degree4 (S.erase v) u + 1 = degree4 S u := by
  simpa only [hv, h, and_self, ite_true] using degree4_erase_add S u v

theorem cleanup_eq_self_iff_stable (S : Finset Site) : cleanup S = S ↔ Stable S := by
  constructor
  · intro h
    have hs := FiniteMajorityPeeling.stable_core neighbors4 S
    change Stable (cleanup S) at hs
    rwa [h] at hs
  · exact FiniteMajorityPeeling.core_eq_self neighbors4

theorem stable_erase_iff {S : Finset Site} {v : Site} (hS : Stable S) (hv : v ∈ S) :
    Stable (S.erase v) ↔ ∀ u ∈ S, u ∈ neighbors4 v → 3 ≤ degree4 S u := by
  change FiniteMajorityPeeling.Stable neighbors4 (S.erase v) ↔ _
  rw [FiniteMajorityPeeling.stable_iff]
  constructor
  · intro h u hu hnu
    have huv : u ≠ v := by
      intro heq
      subst u
      exact not_mem_neighbors4_self v hnu
    have hdu : 2 ≤ degree4 (S.erase v) u := h u (Finset.mem_erase.mpr ⟨huv, hu⟩)
    have hnv := (ClippedProtectedGeometry.neighbors4_symmetric v u).mp hnu
    have hd := degree4_erase_add_one hv hnv
    omega
  · intro h u hu
    obtain ⟨_, hu⟩ := Finset.mem_erase.mp hu
    change 2 ≤ degree4 (S.erase v) u
    by_cases hnv : v ∈ neighbors4 u
    · have hnu := (ClippedProtectedGeometry.neighbors4_symmetric u v).mp hnv
      have hdu := h u hu hnu
      have hd := degree4_erase_add_one hv hnv
      omega
    · rw [degree4_erase_of_not_adjacent S u v hnv]
      exact (FiniteMajorityPeeling.stable_iff neighbors4 S).mp hS u hu

theorem cleanup_erase_eq_self_iff {S : Finset Site} {v : Site} (hS : Stable S) (hv : v ∈ S) :
    cleanup (S.erase v) = S.erase v ↔ ∀ u ∈ S, u ∈ neighbors4 v → 3 ≤ degree4 S u := by
  rw [cleanup_eq_self_iff_stable, stable_erase_iff hS hv]

theorem cleanup_erase_card {S : Finset Site} {v : Site} (hS : Stable S) (hv : v ∈ S)
    (hdeg : ∀ u ∈ S, u ∈ neighbors4 v → 3 ≤ degree4 S u) :
    (cleanup (S.erase v)).card + 1 = S.card := by
  rw [(cleanup_erase_eq_self_iff hS hv).mpr hdeg]
  exact Finset.card_erase_add_one hv

theorem weak_neighbor_deleted_legally {S : Finset Site} {u v : Site}
    (hu : u ∈ S) (hv : v ∈ S) (hnu : u ∈ neighbors4 v) (hd : degree4 S u = 2) :
    FiniteMajorityPeeling.Delete neighbors4 (S.erase v) ((S.erase v).erase u) := by
  have huv : u ≠ v := by
    intro h
    subst u
    exact not_mem_neighbors4_self v hnu
  have hnv := (ClippedProtectedGeometry.neighbors4_symmetric v u).mp hnu
  have hloss := degree4_erase_add_one hv hnv
  exact ⟨u, Finset.mem_erase.mpr ⟨huv, hu⟩, by change degree4 (S.erase v) u < 2; omega, rfl⟩

/-- An exact criterion for all remaining sites after two actual deletions. -/
theorem stable_erase_pair_iff {S : Finset Site} {u v : Site}
    (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    Stable ((S.erase v).erase u) ↔
      ∀ w ∈ S, w ≠ v → w ≠ u →
        2 + (if v ∈ neighbors4 w then 1 else 0) + (if u ∈ neighbors4 w then 1 else 0)
          ≤ degree4 S w := by
  have hu' : u ∈ S.erase v := Finset.mem_erase.mpr ⟨huv, hu⟩
  change FiniteMajorityPeeling.Stable neighbors4 ((S.erase v).erase u) ↔ _
  rw [FiniteMajorityPeeling.stable_iff]
  constructor
  · intro h w hw hwv hwu
    have hdw : 2 ≤ degree4 ((S.erase v).erase u) w :=
      h w (Finset.mem_erase.mpr ⟨hwu, Finset.mem_erase.mpr ⟨hwv, hw⟩⟩)
    have hd1 := degree4_erase_add S w v
    have hd2 := degree4_erase_add (S.erase v) w u
    simp only [hv, hu', and_true] at hd1 hd2
    omega
  · intro h w hw
    obtain ⟨hwu, hw'⟩ := Finset.mem_erase.mp hw
    obtain ⟨hwv, hwS⟩ := Finset.mem_erase.mp hw'
    have hdw := h w hwS hwv hwu
    have hd1 := degree4_erase_add S w v
    have hd2 := degree4_erase_add (S.erase v) w u
    simp only [hv, hu', and_true] at hd1 hd2
    change 2 ≤ degree4 ((S.erase v).erase u) w
    omega

theorem cleanup_erase_eq_pair_of_local_degrees {S : Finset Site} {u v : Site}
    (hu : u ∈ S) (hv : v ∈ S) (hnu : u ∈ neighbors4 v) (hd : degree4 S u = 2)
    (hdeg : ∀ w ∈ S, w ≠ v → w ≠ u →
      2 + (if v ∈ neighbors4 w then 1 else 0) + (if u ∈ neighbors4 w then 1 else 0)
        ≤ degree4 S w) : cleanup (S.erase v) = (S.erase v).erase u := by
  have huv : u ≠ v := by
    intro h
    subst u
    exact not_mem_neighbors4_self v hnu
  have hstable := (stable_erase_pair_iff hu hv huv).mpr hdeg
  have hterminal := (FiniteMajorityPeeling.terminal_iff_stable neighbors4 _).mpr hstable
  exact (terminal_cleanup_unique (Relation.ReflTransGen.single
    (weak_neighbor_deleted_legally hu hv hnu hd)) hterminal).symm

theorem cleanup_erase_pair_card {S : Finset Site} {u v : Site}
    (hu : u ∈ S) (hv : v ∈ S) (hnu : u ∈ neighbors4 v) (hd : degree4 S u = 2)
    (hdeg : ∀ w ∈ S, w ≠ v → w ≠ u →
      2 + (if v ∈ neighbors4 w then 1 else 0) + (if u ∈ neighbors4 w then 1 else 0)
        ≤ degree4 S w) : (cleanup (S.erase v)).card + 2 = S.card := by
  rw [cleanup_erase_eq_pair_of_local_degrees hu hv hnu hd hdeg]
  have huv : u ≠ v := by
    intro h
    subst u
    exact not_mem_neighbors4_self v hnu
  have h1 := Finset.card_erase_add_one hv
  have h2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨huv, hu⟩)
  omega

end MathResearchAnalysis.GridCleanupDeletion
