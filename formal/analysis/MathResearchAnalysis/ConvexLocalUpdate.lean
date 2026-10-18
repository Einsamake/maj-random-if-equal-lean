module

public import MathResearchAnalysis.OrthogonalGridConvexity
public import MathResearchAnalysis.DropletModifiedWord

set_option autoImplicit false

/-!
Actual single-site majority classification under proved interval-convexity and
stability conditions. This does not assert geometric Good equivalence or
modified-update contour invariance.
-/

@[expose] public section
namespace MathResearchAnalysis.ConvexLocalUpdate
open GridCellBoundary (Site)
open InfiniteGridModel (north east south west)
open OrthogonalGridConvexity

theorem mem_of_east_west {S : Finset Site} {v : Site} (h : RowConvex S)
    (he : east v ∈ S) (hw : west v ∈ S) : v ∈ S := by
  exact h (v.1-1) (v.1+1) v.1 v.2 hw he (by omega) (by omega)

theorem mem_of_north_south {S : Finset Site} {v : Site} (h : ColumnConvex S)
    (hn : north v ∈ S) (hs : south v ∈ S) : v ∈ S := by
  exact h v.1 (v.2-1) (v.2+1) v.2 hs hn (by omega) (by omega)

theorem vacant_no_east_west {S : Finset Site} {v : Site} (h : RowConvex S)
    (hv : v ∉ S) : ¬ (east v ∈ S ∧ west v ∈ S) :=
  fun hew => hv (mem_of_east_west h hew.1 hew.2)

theorem vacant_no_north_south {S : Finset Site} {v : Site} (h : ColumnConvex S)
    (hv : v ∉ S) : ¬ (north v ∈ S ∧ south v ∈ S) :=
  fun hns => hv (mem_of_north_south h hns.1 hns.2)
theorem vacant_degree4_le_two {S : Finset Site} {v : Site}
    (hr : RowConvex S) (hc : ColumnConvex S) (hv : v ∉ S) :
    GridMajorityPeeling.degree4 S v ≤ 2 := by
  have hns := vacant_no_north_south hc hv
  have hew := vacant_no_east_west hr hv
  rw [GridMajorityPeeling.degree4_eq_four_inputs]
  by_cases hn : north v ∈ S <;> by_cases he : east v ∈ S <;>
    by_cases hs : south v ∈ S <;> by_cases hw : west v ∈ S
  all_goals simp_all [GridMajorityPeeling.state]
theorem vacant_localRule_true_iff {S : Finset Site} {v : Site} (tie : Bool)
    (hr : RowConvex S) (hc : ColumnConvex S) (hv : v ∉ S) :
    DropletModifiedWord.localRule S v tie = true ↔
      GridMajorityPeeling.degree4 S v = 2 ∧ tie = true := by
  have hd := vacant_degree4_le_two hr hc hv
  simp only [DropletModifiedWord.localRule, InfiniteGridModel.majority4,
    ← GridMajorityPeeling.degree4_eq_four_inputs]
  by_cases h2 : GridMajorityPeeling.degree4 S v = 2
  · simp [h2]
  · have hlt : GridMajorityPeeling.degree4 S v < 2 := by omega
    simp [not_lt.mpr hd, hlt, h2]
theorem localRule_eq_tie_of_degree_two (S : Finset Site) (v : Site) (tie : Bool)
    (h : GridMajorityPeeling.degree4 S v = 2) :
    DropletModifiedWord.localRule S v tie = tie := by
  simp only [DropletModifiedWord.localRule, InfiniteGridModel.majority4,
    ← GridMajorityPeeling.degree4_eq_four_inputs, h]
  rfl

theorem stable_occupied_localRule_false_iff {S : Finset Site} {v : Site} (tie : Bool)
    (hst : DropletModifiedWord.Stable S) (hv : v ∈ S) :
    DropletModifiedWord.localRule S v tie = false ↔
      GridMajorityPeeling.degree4 S v = 2 ∧ tie = false := by
  have hd : 2 ≤ GridMajorityPeeling.degree4 S v :=
    (FiniteMajorityPeeling.stable_iff GridMajorityPeeling.neighbors4 S).mp hst v hv
  simp only [DropletModifiedWord.localRule, InfiniteGridModel.majority4,
    ← GridMajorityPeeling.degree4_eq_four_inputs]
  by_cases h2 : GridMajorityPeeling.degree4 S v = 2
  · simp [h2]
  · have hgt : 2 < GridMajorityPeeling.degree4 S v := by omega
    simp [hgt, h2]

theorem cleanup_eq_self_of_stable {S : Finset Site} (hst : DropletModifiedWord.Stable S) :
    GridMajorityPeeling.cleanup S = S :=
  FiniteMajorityPeeling.core_eq_self GridMajorityPeeling.neighbors4 hst

theorem rawStep_of_birth {S : Finset Site} {v : Site}
    (hr : RowConvex S) (hc : ColumnConvex S) (hv : v ∉ S)
    (hd : GridMajorityPeeling.degree4 S v = 2) :
    DropletModifiedWord.rawStep S v true = insert v S := by
  have ht := (vacant_localRule_true_iff true hr hc hv).mpr ⟨hd, rfl⟩
  simp [DropletModifiedWord.rawStep, ht]

theorem rawStep_of_death {S : Finset Site} {v : Site}
    (hst : DropletModifiedWord.Stable S) (hv : v ∈ S)
    (hd : GridMajorityPeeling.degree4 S v = 2) :
    DropletModifiedWord.rawStep S v false = S.erase v := by
  have ht := (stable_occupied_localRule_false_iff false hst hv).mpr ⟨hd, rfl⟩
  simp [DropletModifiedWord.rawStep, ht]

theorem rawStep_classification {S : Finset Site} (v : Site) (tie : Bool)
    (hr : RowConvex S) (hc : ColumnConvex S) (hst : DropletModifiedWord.Stable S) :
    DropletModifiedWord.rawStep S v tie = S ∨
      (v ∉ S ∧ GridMajorityPeeling.degree4 S v = 2 ∧ tie = true ∧
        DropletModifiedWord.rawStep S v tie = insert v S) ∨
      (v ∈ S ∧ GridMajorityPeeling.degree4 S v = 2 ∧ tie = false ∧
        DropletModifiedWord.rawStep S v tie = S.erase v) := by
  by_cases hv : v ∈ S
  · by_cases hf : DropletModifiedWord.localRule S v tie = false
    · obtain ⟨hd, ht⟩ := (stable_occupied_localRule_false_iff tie hst hv).mp hf
      exact Or.inr (Or.inr ⟨hv, hd, ht, by simp [DropletModifiedWord.rawStep, hf]⟩)
    · have ht : DropletModifiedWord.localRule S v tie = true := Bool.eq_true_of_not_eq_false hf
      exact Or.inl (by simp [DropletModifiedWord.rawStep, ht, hv])
  · by_cases ht : DropletModifiedWord.localRule S v tie = true
    · obtain ⟨hd, hb⟩ := (vacant_localRule_true_iff tie hr hc hv).mp ht
      exact Or.inr (Or.inl ⟨hv, hd, hb, by simp [DropletModifiedWord.rawStep, ht]⟩)
    · exact Or.inl (by simp [DropletModifiedWord.rawStep, ht, hv])

theorem rawStep_eq_self_of_degree_ne_two {S : Finset Site} (v : Site) (tie : Bool)
    (hr : RowConvex S) (hc : ColumnConvex S) (hst : DropletModifiedWord.Stable S)
    (hd : GridMajorityPeeling.degree4 S v ≠ 2) : DropletModifiedWord.rawStep S v tie = S := by
  rcases rawStep_classification v tie hr hc hst with h | h | h
  · exact h
  · exact False.elim (hd h.2.1)
  · exact False.elim (hd h.2.1)

theorem rawStep_birth_card {S : Finset Site} {v : Site}
    (hr : RowConvex S) (hc : ColumnConvex S) (hv : v ∉ S)
    (hd : GridMajorityPeeling.degree4 S v = 2) :
    (DropletModifiedWord.rawStep S v true).card = S.card + 1 := by
  rw [rawStep_of_birth hr hc hv hd, Finset.card_insert_of_notMem hv]

theorem rawStep_death_card {S : Finset Site} {v : Site}
    (hst : DropletModifiedWord.Stable S) (hv : v ∈ S)
    (hd : GridMajorityPeeling.degree4 S v = 2) :
    (DropletModifiedWord.rawStep S v false).card + 1 = S.card := by
  rw [rawStep_of_death hst hv hd]
  exact Finset.card_erase_add_one hv

theorem modifiedStep_classification {S : Finset Site} (D : Finset Site) (v : Site) (tie : Bool)
    (hr : RowConvex S) (hc : ColumnConvex S) (hst : DropletModifiedWord.Stable S) :
    DropletModifiedWord.modifiedStep D S v tie = S ∨
      (v ∈ D ∧ v ∉ S ∧ GridMajorityPeeling.degree4 S v = 2 ∧ tie = true ∧
        DropletModifiedWord.modifiedStep D S v tie = GridMajorityPeeling.cleanup (insert v S)) ∨
      (v ∈ D ∧ v ∈ S ∧ GridMajorityPeeling.degree4 S v = 2 ∧ tie = false ∧
        DropletModifiedWord.modifiedStep D S v tie = GridMajorityPeeling.cleanup (S.erase v)) := by
  by_cases hvD : v ∈ D
  · rcases rawStep_classification v tie hr hc hst with h | h | h
    · exact Or.inl (by simp [DropletModifiedWord.modifiedStep, hvD, h, cleanup_eq_self_of_stable hst])
    · exact Or.inr (Or.inl ⟨hvD, h.1, h.2.1, h.2.2.1,
        by simp [DropletModifiedWord.modifiedStep, hvD, h.2.2.2]⟩)
    · exact Or.inr (Or.inr ⟨hvD, h.1, h.2.1, h.2.2.1,
        by simp [DropletModifiedWord.modifiedStep, hvD, h.2.2.2]⟩)
  · exact Or.inl (by simp [DropletModifiedWord.modifiedStep, hvD])

end MathResearchAnalysis.ConvexLocalUpdate
