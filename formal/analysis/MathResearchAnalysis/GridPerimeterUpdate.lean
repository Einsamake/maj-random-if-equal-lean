module

public import MathResearchAnalysis.GridCellBoundary
public import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

/-!
# Exposed-edge perimeter under an actual single-site update

The perimeter is the cardinality of the actual oriented exposed cell facets.
Every formula is for arbitrary finite occupied sets on the four-neighbour grid.
All identities use addition in Nat, avoiding truncated subtraction.
-/

@[expose] public section

namespace MathResearchAnalysis.GridPerimeterUpdate

open InfiniteGridModel GridCellBoundary GridMajorityPeeling
open scoped BigOperators

abbrev Site := InfiniteGridModel.Site

theorem neighbor_relation_symmetric (v u : Site) :
    v ∈ neighbors4 u ↔ u ∈ neighbors4 v := by
  simp only [mem_neighbors4, north, east, south, west, Prod.ext_iff]
  omega

theorem perimeter_eq_sum_exposed (S : Finset Site) :
    perimeter S = ∑ v ∈ S, ∑ d : Direction, if neighbor v d ∉ S then 1 else 0 := by
  unfold perimeter boundary
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

theorem exposed_plus_degree (S : Finset Site) (v : Site) :
    (∑ d : Direction, if neighbor v d ∉ S then 1 else 0) + degree4 S v = 4 := by
  rw [Fin.sum_univ_four, degree4_eq_four_inputs]
  by_cases hn : north v ∈ S <;> by_cases he : east v ∈ S <;>
    by_cases hs : south v ∈ S <;> by_cases hw : west v ∈ S <;>
    simp [state, hn, he, hs, hw]

theorem perimeter_plus_total_degree (S : Finset Site) :
    perimeter S + ∑ v ∈ S, degree4 S v = 4 * S.card := by
  rw [perimeter_eq_sum_exposed, ← Finset.sum_add_distrib]
  calc
    (∑ v ∈ S, ((∑ d : Direction, if neighbor v d ∉ S then 1 else 0) + degree4 S v)) =
        ∑ v ∈ S, 4 := by
      apply Finset.sum_congr rfl
      intro v _
      exact exposed_plus_degree S v
    _ = 4 * S.card := by simp [Nat.mul_comm]

theorem degree4_insert (S : Finset Site) (v u : Site) (hv : v ∉ S) :
    degree4 (insert v S) u = degree4 S u + if v ∈ neighbors4 u then 1 else 0 := by
  by_cases hn : v ∈ neighbors4 u
  · have hi : neighbors4 u ∩ insert v S = insert v (neighbors4 u ∩ S) := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_insert]
      aesop
    have hvn : v ∉ neighbors4 u ∩ S := by simp [hv]
    simp only [degree4, hi, Finset.card_insert_of_notMem hvn, ite_eq_left hn]
  · have hi : neighbors4 u ∩ insert v S = neighbors4 u ∩ S := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_insert]
      aesop
    simp only [degree4, hi, ite_eq_right hn, Nat.add_zero]

theorem degree4_insert_self (S : Finset Site) (v : Site) (hv : v ∉ S) :
    degree4 (insert v S) v = degree4 S v := by
  rw [degree4_insert S v v hv]
  simp [not_mem_neighbors4_self]

theorem occupied_neighbor_sum (S : Finset Site) (v : Site) :
    (∑ u ∈ S, if v ∈ neighbors4 u then 1 else 0) = degree4 S v := by
  simp_rw [neighbor_relation_symmetric]
  rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  unfold degree4
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_inter]
  exact and_comm

theorem total_degree_insert (S : Finset Site) (v : Site) (hv : v ∉ S) :
    (∑ u ∈ insert v S, degree4 (insert v S) u) =
      (∑ u ∈ S, degree4 S u) + 2 * degree4 S v := by
  rw [Finset.sum_insert hv, degree4_insert_self S v hv]
  simp_rw [degree4_insert S v _ hv]
  rw [Finset.sum_add_distrib, occupied_neighbor_sum]
  omega

theorem perimeter_insert (S : Finset Site) (v : Site) (hv : v ∉ S) :
    perimeter (insert v S) + 2 * degree4 S v = perimeter S + 4 := by
  have hnew := perimeter_plus_total_degree (insert v S)
  have hold := perimeter_plus_total_degree S
  rw [total_degree_insert S v hv, Finset.card_insert_of_notMem hv] at hnew
  omega

theorem degree4_erase_self (S : Finset Site) (v : Site) :
    degree4 (S.erase v) v = degree4 S v := by
  have h := degree4_insert_self (S.erase v) v (Finset.notMem_erase v S)
  by_cases hv : v ∈ S
  · rw [Finset.insert_erase hv] at h
    exact h.symm
  · simp [Finset.erase_eq_of_notMem hv]

theorem perimeter_erase (S : Finset Site) (v : Site) (hv : v ∈ S) :
    perimeter (S.erase v) + 4 = perimeter S + 2 * degree4 S v := by
  have h := perimeter_insert (S.erase v) v (Finset.notMem_erase v S)
  rw [Finset.insert_erase hv, degree4_erase_self] at h
  omega

theorem perimeter_insert_tie (S : Finset Site) (v : Site)
    (hv : v ∉ S) (hd : degree4 S v = 2) :
    perimeter (insert v S) = perimeter S := by
  have h := perimeter_insert S v hv
  omega

theorem perimeter_erase_tie (S : Finset Site) (v : Site)
    (hv : v ∈ S) (hd : degree4 S v = 2) :
    perimeter (S.erase v) = perimeter S := by
  have h := perimeter_erase S v hv
  omega

end MathResearchAnalysis.GridPerimeterUpdate
