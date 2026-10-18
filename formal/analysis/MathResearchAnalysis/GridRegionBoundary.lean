module

public import MathResearchAnalysis.GridCellRegion
public import MathResearchAnalysis.GridBoundaryIncidence

set_option autoImplicit false

/-!
# The full topological frontier of a finite occupied cell union

All segments contain their complete real affine interpolation, including
endpoints. Local occupied rectangles cover genuine open neighbourhoods.
At a lattice corner a mixed four-cell occupancy supplies an actual exposed
incident edge. This identifies the whole frontier without a Jordan premise.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.GridRegionBoundary

open GridCellBoundary GridBoundarySegments GridCellRegion
open InfiniteGridModel (north east south west)
open Set

theorem mem_north_segment_iff (v : Site) (p : Plane) :
    p ∈ closedSegment (v, (⟨0, by decide⟩ : Direction)) ↔
      2 * (v.1 : Real) - 1 ≤ p.1 ∧ p.1 ≤ 2 * (v.1 : Real) + 1 ∧
      p.2 = 2 * (v.2 : Real) + 1 := by
  constructor
  · rintro ⟨t, ht0, ht1, hp⟩
    rw [segmentPoint_north] at hp
    have hx := congrArg Prod.fst hp
    have hy := congrArg Prod.snd hp
    dsimp only at hx hy
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨hx0, hx1, hy⟩
    refine ⟨(2 * (v.1 : Real) + 1 - p.1) / 2, by linarith, by linarith, ?_⟩
    rw [segmentPoint_north]
    apply Prod.ext
    · dsimp only
      linarith
    · dsimp only
      linarith

theorem mem_east_segment_iff (v : Site) (p : Plane) :
    p ∈ closedSegment (v, (⟨1, by decide⟩ : Direction)) ↔
      p.1 = 2 * (v.1 : Real) + 1 ∧
      2 * (v.2 : Real) - 1 ≤ p.2 ∧ p.2 ≤ 2 * (v.2 : Real) + 1 := by
  constructor
  · rintro ⟨t, ht0, ht1, hp⟩
    rw [segmentPoint_east] at hp
    have hx := congrArg Prod.fst hp
    have hy := congrArg Prod.snd hp
    dsimp only at hx hy
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨hx, hy0, hy1⟩
    refine ⟨(p.2 - (2 * (v.2 : Real) - 1)) / 2, by linarith, by linarith, ?_⟩
    rw [segmentPoint_east]
    apply Prod.ext
    · dsimp only
      linarith
    · dsimp only
      linarith

theorem mem_south_segment_iff (v : Site) (p : Plane) :
    p ∈ closedSegment (v, (⟨2, by decide⟩ : Direction)) ↔
      2 * (v.1 : Real) - 1 ≤ p.1 ∧ p.1 ≤ 2 * (v.1 : Real) + 1 ∧
      p.2 = 2 * (v.2 : Real) - 1 := by
  constructor
  · rintro ⟨t, ht0, ht1, hp⟩
    rw [segmentPoint_south] at hp
    have hx := congrArg Prod.fst hp
    have hy := congrArg Prod.snd hp
    dsimp only at hx hy
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨hx0, hx1, hy⟩
    refine ⟨(p.1 - (2 * (v.1 : Real) - 1)) / 2, by linarith, by linarith, ?_⟩
    rw [segmentPoint_south]
    apply Prod.ext
    · dsimp only
      linarith
    · dsimp only
      linarith

theorem mem_west_segment_iff (v : Site) (p : Plane) :
    p ∈ closedSegment (v, (⟨3, by decide⟩ : Direction)) ↔
      p.1 = 2 * (v.1 : Real) - 1 ∧
      2 * (v.2 : Real) - 1 ≤ p.2 ∧ p.2 ≤ 2 * (v.2 : Real) + 1 := by
  constructor
  · rintro ⟨t, ht0, ht1, hp⟩
    rw [segmentPoint_west] at hp
    have hx := congrArg Prod.fst hp
    have hy := congrArg Prod.snd hp
    dsimp only at hx hy
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨hx, hy0, hy1⟩
    refine ⟨(2 * (v.2 : Real) + 1 - p.2) / 2, by linarith, by linarith, ?_⟩
    rw [segmentPoint_west]
    apply Prod.ext
    · dsimp only
      linarith
    · dsimp only
      linarith

theorem horizontal_pair_rectangle_subset_region {S : Finset Site} (v : Site)
    (hv : v ∈ S) (he : east v ∈ S) :
    Ioo (2 * (v.1 : Real) - 1) (2 * (v.1 : Real) + 3) ×ˢ
      Ioo (2 * (v.2 : Real) - 1) (2 * (v.2 : Real) + 1) ⊆ region S := by
  intro p hp
  obtain ⟨⟨hx0, hx1⟩, hy0, hy1⟩ := hp
  by_cases hx : p.1 ≤ 2 * (v.1 : Real) + 1
  · apply cellBox_subset_region hv
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · apply cellBox_subset_region he
    dsimp [cellBox, east]
    push_cast
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem vertical_pair_rectangle_subset_region {S : Finset Site} (v : Site)
    (hv : v ∈ S) (hn : north v ∈ S) :
    Ioo (2 * (v.1 : Real) - 1) (2 * (v.1 : Real) + 1) ×ˢ
      Ioo (2 * (v.2 : Real) - 1) (2 * (v.2 : Real) + 3) ⊆ region S := by
  intro p hp
  obtain ⟨⟨hx0, hx1⟩, hy0, hy1⟩ := hp
  by_cases hy : p.2 ≤ 2 * (v.2 : Real) + 1
  · apply cellBox_subset_region hv
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · apply cellBox_subset_region hn
    dsimp [cellBox, north]
    push_cast
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem four_cells_rectangle_subset_region {S : Finset Site} (v : Site)
    (hv : v ∈ S) (hn : north v ∈ S) (hne : north (east v) ∈ S) (he : east v ∈ S) :
    Ioo (2 * (v.1 : Real) - 1) (2 * (v.1 : Real) + 3) ×ˢ
      Ioo (2 * (v.2 : Real) - 1) (2 * (v.2 : Real) + 3) ⊆ region S := by
  intro p hp
  obtain ⟨⟨hx0, hx1⟩, hy0, hy1⟩ := hp
  by_cases hx : p.1 ≤ 2 * (v.1 : Real) + 1 <;>
    by_cases hy : p.2 ≤ 2 * (v.2 : Real) + 1
  · apply cellBox_subset_region hv
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · apply cellBox_subset_region hn
    dsimp [cellBox, north]
    push_cast
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · apply cellBox_subset_region he
    dsimp [cellBox, east]
    push_cast
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · apply cellBox_subset_region hne
    dsimp [cellBox, north, east]
    push_cast
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem corner_mem_interior_of_four_cells {S : Finset Site} (a : Site)
    (hsw : a ∈ S) (hnw : north a ∈ S)
    (hne : north (east a) ∈ S) (hse : east a ∈ S) :
    realSite (GridBoundaryIncidence.corner a) ∈ interior (region S) := by
  apply interior_maximal (four_cells_rectangle_subset_region a hsw hnw hne hse)
    (isOpen_Ioo.prod isOpen_Ioo)
  simp only [mem_prod, mem_Ioo, realSite, GridBoundaryIncidence.corner,
    Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one]
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem corner_mem_outgoing_segment (a : Site) (e : HalfEdge)
    (he : e ∈ GridBoundaryIncidence.outgoingCandidates a) :
    realSite (GridBoundaryIncidence.corner a) ∈ closedSegment e := by
  have hsource := (GridBoundaryIncidence.source_eq_corner_iff e a).mpr he
  rw [← hsource]
  exact source_mem_closedSegment e

theorem corner_exposed_or_interior (S : Finset Site) (a : Site)
    (hocc : a ∈ S ∨ north a ∈ S ∨ north (east a) ∈ S ∨ east a ∈ S) :
    (∃ e ∈ boundary S, realSite (GridBoundaryIncidence.corner a) ∈ closedSegment e) ∨
      realSite (GridBoundaryIncidence.corner a) ∈ interior (region S) := by
  have hcases :
      (a ∈ S ∧ north a ∈ S ∧ north (east a) ∈ S ∧ east a ∈ S) ∨
      (a ∉ S ∧ north a ∉ S ∧ north (east a) ∉ S ∧ east a ∉ S) ∨
      (a ∈ S ∧ north a ∉ S) ∨
      (north a ∈ S ∧ north (east a) ∉ S) ∨
      (north (east a) ∈ S ∧ east a ∉ S) ∨ (east a ∈ S ∧ a ∉ S) := by
    tauto
  rcases hcases with h | h | h | h | h | h
  · exact Or.inr (corner_mem_interior_of_four_cells a h.1 h.2.1 h.2.2.1 h.2.2.2)
  · exact False.elim (by tauto)
  · left
    refine ⟨(a, 0), (mem_boundary_north S a).mpr h, ?_⟩
    exact corner_mem_outgoing_segment a (a, 0) (by
      simp [GridBoundaryIncidence.outgoingCandidates])
  · left
    refine ⟨(north a, 1), (mem_boundary_east S (north a)).mpr ⟨h.1, ?_⟩, ?_⟩
    · simpa [north, east] using h.2
    · exact corner_mem_outgoing_segment a (north a, 1) (by
        simp [GridBoundaryIncidence.outgoingCandidates])
  · left
    refine ⟨(north (east a), 2),
      (mem_boundary_south S (north (east a))).mpr ⟨h.1, ?_⟩, ?_⟩
    · simpa [north, south] using h.2
    · exact corner_mem_outgoing_segment a (north (east a), 2) (by
        simp [GridBoundaryIncidence.outgoingCandidates])
  · left
    refine ⟨(east a, 3), (mem_boundary_west S (east a)).mpr ⟨h.1, ?_⟩, ?_⟩
    · simpa [east, west] using h.2
    · exact corner_mem_outgoing_segment a (east a, 3) (by
        simp [GridBoundaryIncidence.outgoingCandidates])
theorem north_face_exposed_or_interior (S : Finset Site) (v : Site) (p : Plane)
    (hv : v ∈ S)
    (hx : 2 * (v.1 : Real) - 1 < p.1 ∧ p.1 < 2 * (v.1 : Real) + 1)
    (hy : p.2 = 2 * (v.2 : Real) + 1) :
    (∃ e ∈ boundary S, p ∈ closedSegment e) ∨ p ∈ interior (region S) := by
  by_cases hn : north v ∈ S
  · right
    apply interior_maximal (vertical_pair_rectangle_subset_region v hv hn)
      (isOpen_Ioo.prod isOpen_Ioo)
    exact ⟨hx, ⟨by linarith, by linarith⟩⟩
  · left
    exact ⟨(v, 0), (mem_boundary_north S v).mpr ⟨hv, hn⟩,
      (mem_north_segment_iff v p).mpr ⟨hx.1.le, hx.2.le, hy⟩⟩

theorem east_face_exposed_or_interior (S : Finset Site) (v : Site) (p : Plane)
    (hv : v ∈ S) (hx : p.1 = 2 * (v.1 : Real) + 1)
    (hy : 2 * (v.2 : Real) - 1 < p.2 ∧ p.2 < 2 * (v.2 : Real) + 1) :
    (∃ e ∈ boundary S, p ∈ closedSegment e) ∨ p ∈ interior (region S) := by
  by_cases he : east v ∈ S
  · right
    apply interior_maximal (horizontal_pair_rectangle_subset_region v hv he)
      (isOpen_Ioo.prod isOpen_Ioo)
    exact ⟨⟨by linarith, by linarith⟩, hy⟩
  · left
    exact ⟨(v, 1), (mem_boundary_east S v).mpr ⟨hv, he⟩,
      (mem_east_segment_iff v p).mpr ⟨hx, hy.1.le, hy.2.le⟩⟩

theorem south_face_exposed_or_interior (S : Finset Site) (v : Site) (p : Plane)
    (hv : v ∈ S)
    (hx : 2 * (v.1 : Real) - 1 < p.1 ∧ p.1 < 2 * (v.1 : Real) + 1)
    (hy : p.2 = 2 * (v.2 : Real) - 1) :
    (∃ e ∈ boundary S, p ∈ closedSegment e) ∨ p ∈ interior (region S) := by
  by_cases hs : south v ∈ S
  · have hb : north (south v) ∈ S := by simpa [north, south] using hv
    right
    apply interior_maximal (vertical_pair_rectangle_subset_region (south v) hs hb)
      (isOpen_Ioo.prod isOpen_Ioo)
    simp only [mem_prod, mem_Ioo, south, Int.cast_sub, Int.cast_one]
    exact ⟨hx, ⟨by linarith, by linarith⟩⟩
  · left
    exact ⟨(v, 2), (mem_boundary_south S v).mpr ⟨hv, hs⟩,
      (mem_south_segment_iff v p).mpr ⟨hx.1.le, hx.2.le, hy⟩⟩

theorem west_face_exposed_or_interior (S : Finset Site) (v : Site) (p : Plane)
    (hv : v ∈ S) (hx : p.1 = 2 * (v.1 : Real) - 1)
    (hy : 2 * (v.2 : Real) - 1 < p.2 ∧ p.2 < 2 * (v.2 : Real) + 1) :
    (∃ e ∈ boundary S, p ∈ closedSegment e) ∨ p ∈ interior (region S) := by
  by_cases hw : west v ∈ S
  · have hb : east (west v) ∈ S := by simpa [east, west] using hv
    right
    apply interior_maximal (horizontal_pair_rectangle_subset_region (west v) hw hb)
      (isOpen_Ioo.prod isOpen_Ioo)
    simp only [mem_prod, mem_Ioo, west, Int.cast_sub, Int.cast_one]
    exact ⟨⟨by linarith, by linarith⟩, hy⟩
  · left
    exact ⟨(v, 3), (mem_boundary_west S v).mpr ⟨hv, hw⟩,
      (mem_west_segment_iff v p).mpr ⟨hx, hy.1.le, hy.2.le⟩⟩

theorem cellBox_exposed_or_interior (S : Finset Site) (v : Site) (p : Plane)
    (hv : v ∈ S) (hp : p ∈ cellBox v) :
    (∃ e ∈ boundary S, p ∈ closedSegment e) ∨ p ∈ interior (region S) := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hp
  by_cases hxL : p.1 = 2 * (v.1 : Real) - 1
  · by_cases hyB : p.2 = 2 * (v.2 : Real) - 1
    · let a := south (west v)
      have hpc : p = realSite (GridBoundaryIncidence.corner a) := by
        apply Prod.ext
        · dsimp [realSite, GridBoundaryIncidence.corner, a, south, west]
          push_cast
          linarith
        · dsimp [realSite, GridBoundaryIncidence.corner, a, south, west]
          push_cast
          linarith
      have hocc : north (east a) ∈ S := by simpa [a, north, east, south, west] using hv
      rw [hpc]
      exact corner_exposed_or_interior S a (Or.inr (Or.inr (Or.inl hocc)))
    · by_cases hyT : p.2 = 2 * (v.2 : Real) + 1
      · let a := west v
        have hpc : p = realSite (GridBoundaryIncidence.corner a) := by
          apply Prod.ext
          · dsimp [realSite, GridBoundaryIncidence.corner, a, west]
            push_cast
            linarith
          · dsimp [realSite, GridBoundaryIncidence.corner, a, west]
            push_cast
            linarith
        have hocc : east a ∈ S := by simpa [a, east, west] using hv
        rw [hpc]
        exact corner_exposed_or_interior S a (Or.inr (Or.inr (Or.inr hocc)))
      · exact west_face_exposed_or_interior S v p hv hxL
          ⟨lt_of_le_of_ne hy0 (Ne.symm hyB), lt_of_le_of_ne hy1 hyT⟩
  · by_cases hxR : p.1 = 2 * (v.1 : Real) + 1
    · by_cases hyB : p.2 = 2 * (v.2 : Real) - 1
      · let a := south v
        have hpc : p = realSite (GridBoundaryIncidence.corner a) := by
          apply Prod.ext
          · dsimp [realSite, GridBoundaryIncidence.corner, a, south]
            push_cast
            linarith
          · dsimp [realSite, GridBoundaryIncidence.corner, a, south]
            push_cast
            linarith
        have hocc : north a ∈ S := by simpa [a, north, south] using hv
        rw [hpc]
        exact corner_exposed_or_interior S a (Or.inr (Or.inl hocc))
      · by_cases hyT : p.2 = 2 * (v.2 : Real) + 1
        · have hpc : p = realSite (GridBoundaryIncidence.corner v) := by
            apply Prod.ext
            · dsimp [realSite, GridBoundaryIncidence.corner]
              push_cast
              linarith
            · dsimp [realSite, GridBoundaryIncidence.corner]
              push_cast
              linarith
          rw [hpc]
          exact corner_exposed_or_interior S v (Or.inl hv)
        · exact east_face_exposed_or_interior S v p hv hxR
            ⟨lt_of_le_of_ne hy0 (Ne.symm hyB), lt_of_le_of_ne hy1 hyT⟩
    · have hx : 2 * (v.1 : Real) - 1 < p.1 ∧ p.1 < 2 * (v.1 : Real) + 1 :=
        ⟨lt_of_le_of_ne hx0 (Ne.symm hxL), lt_of_le_of_ne hx1 hxR⟩
      by_cases hyB : p.2 = 2 * (v.2 : Real) - 1
      · exact south_face_exposed_or_interior S v p hv hx hyB
      · by_cases hyT : p.2 = 2 * (v.2 : Real) + 1
        · exact north_face_exposed_or_interior S v p hv hx hyT
        · right
          apply cellInterior_subset_interior_region hv
          exact (mem_cellInterior v p).mpr
            ⟨hx.1, hx.2, lt_of_le_of_ne hy0 (Ne.symm hyB), lt_of_le_of_ne hy1 hyT⟩

theorem frontier_region_subset_boundarySegments (S : Finset Site) :
    frontier (region S) ⊆ ⋃ e ∈ boundary S, closedSegment e := by
  intro p hp
  have hreg := frontier_region_subset S hp
  have hnot := (mem_frontier_iff_notMem_interior hreg).mp hp
  obtain ⟨v, hv, hpv⟩ := (mem_region S p).mp hreg
  rcases cellBox_exposed_or_interior S v p hv hpv with hexp | hint
  · simpa only [mem_iUnion, exists_prop] using hexp
  · exact False.elim (hnot hint)

theorem frontier_region_eq_boundarySegments (S : Finset Site) :
    frontier (region S) = ⋃ e ∈ boundary S, closedSegment e :=
  Subset.antisymm (frontier_region_subset_boundarySegments S) (boundarySegments_subset_frontier S)

theorem mem_frontier_region_iff (S : Finset Site) (p : Plane) :
    p ∈ frontier (region S) ↔ ∃ e ∈ boundary S, p ∈ closedSegment e := by
  rw [frontier_region_eq_boundarySegments]
  simp only [mem_iUnion, exists_prop]

end MathResearchAnalysis.GridRegionBoundary
