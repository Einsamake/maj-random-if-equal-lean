module

public import MathResearchAnalysis.GridCellRegion
public import MathResearchAnalysis.ClippedBoundaryBox

set_option autoImplicit false

/-!
# The minimum rectangle of the actual occupied region and its frontier

Containment is proved for every real point of every occupied square. Four
actual frontier points attain the bounds, so the rectangle is minimal for
both the region and its entire frontier, not merely for a selected vertex list.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.ClippedRegionBox

open GridCellBoundary GridBoundarySegments

def extent (L : Nat) : Real := 2 * (L : Real) + 1

def box (L : Nat) : Set Plane :=
  Set.Icc (-(extent L)) (extent L) ×ˢ Set.Icc (-(extent L)) (extent L)

theorem region_subset_box (L : Nat) :
    GridCellRegion.region (ClippedDiamondGeometry.clippedDomain L) ⊆ box L := by
  intro p hp
  obtain ⟨v, hv, hp⟩ := (GridCellRegion.mem_region _ _).mp hp
  obtain ⟨hx, hy, _⟩ := (ClippedDiamondGeometry.mem_clippedDomain L v).mp hv
  have hxR : |(v.1 : Real)| ≤ (L : Real) := by exact_mod_cast hx
  have hyR : |(v.2 : Real)| ≤ (L : Real) := by exact_mod_cast hy
  obtain ⟨hx0, hx1⟩ := abs_le.mp hxR
  obtain ⟨hy0, hy1⟩ := abs_le.mp hyR
  obtain ⟨hp0, hp1, hp2, hp3⟩ := hp
  change (-(extent L) ≤ p.1 ∧ p.1 ≤ extent L) ∧
    (-(extent L) ≤ p.2 ∧ p.2 ≤ extent L)
  dsimp [extent]
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem frontier_subset_box (L : Nat) :
    frontier (GridCellRegion.region (ClippedDiamondGeometry.clippedDomain L)) ⊆ box L :=
  (GridCellRegion.frontier_region_subset _).trans (region_subset_box L)

theorem vertex_mem_frontier (L : Nat) {z : Site} (hz : z ∈ ClippedBoundaryBox.vertices L) :
    realSite z ∈ frontier (GridCellRegion.region (ClippedDiamondGeometry.clippedDomain L)) := by
  rcases Finset.mem_union.mp hz with hz | hz
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
    exact GridCellRegion.boundary_source_mem_frontier he
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
    exact GridCellRegion.boundary_target_mem_frontier he

theorem right_frontier (L : Nat) :
    (extent L, -1) ∈ frontier (GridCellRegion.region (ClippedDiamondGeometry.clippedDomain L)) := by
  have h := vertex_mem_frontier L (ClippedBoundaryBox.right_vertex L)
  simpa only [realSite, extent, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
    Int.cast_neg, Int.cast_one] using h

theorem left_frontier (L : Nat) :
    (-(extent L), 1) ∈ frontier (GridCellRegion.region (ClippedDiamondGeometry.clippedDomain L)) := by
  have h := vertex_mem_frontier L (ClippedBoundaryBox.left_vertex L)
  simpa [realSite, extent, sub_eq_add_neg, add_comm] using h

theorem top_frontier (L : Nat) :
    (1, extent L) ∈ frontier (GridCellRegion.region (ClippedDiamondGeometry.clippedDomain L)) := by
  have h := vertex_mem_frontier L (ClippedBoundaryBox.top_vertex L)
  simpa [realSite, extent] using h

theorem bottom_frontier (L : Nat) :
    (-1, -(extent L)) ∈ frontier (GridCellRegion.region (ClippedDiamondGeometry.clippedDomain L)) := by
  have h := vertex_mem_frontier L (ClippedBoundaryBox.bottom_vertex L)
  simpa [realSite, extent, sub_eq_add_neg, add_comm] using h

theorem minimum_frontier_rectangle (L : Nat) (a b c d : Real)
    (h : frontier (GridCellRegion.region (ClippedDiamondGeometry.clippedDomain L)) ⊆
      Set.Icc a b ×ˢ Set.Icc c d) :
    box L ⊆ Set.Icc a b ×ˢ Set.Icc c d := by
  have hl := h (left_frontier L)
  have hr := h (right_frontier L)
  have ht := h (top_frontier L)
  have hb := h (bottom_frontier L)
  rintro p ⟨hx, hy⟩
  exact ⟨⟨hl.1.1.trans hx.1, hx.2.trans hr.1.2⟩,
    ⟨hb.2.1.trans hy.1, hy.2.trans ht.2.2⟩⟩

theorem minimum_region_rectangle (L : Nat) (a b c d : Real)
    (h : GridCellRegion.region (ClippedDiamondGeometry.clippedDomain L) ⊆
      Set.Icc a b ×ˢ Set.Icc c d) :
    box L ⊆ Set.Icc a b ×ˢ Set.Icc c d :=
  minimum_frontier_rectangle L a b c d ((GridCellRegion.frontier_region_subset _).trans h)

theorem span (L : Nat) : extent L - (-(extent L)) = 4 * (L : Real) + 2 := by
  unfold extent
  ring

/-- The physical facet count matches the minimum rectangle perimeter after
rescaling doubled coordinates by one half. The arc-length bridge is separate. -/
theorem facet_perimeter_eq_rescaled_rectangle (L : Nat) :
    (perimeter (ClippedDiamondGeometry.clippedDomain L) : Real) =
      2 * ((extent L - (-(extent L))) / 2 + (extent L - (-(extent L))) / 2) := by
  rw [ClippedBoundaryPerimeter.physical_perimeter]
  push_cast
  unfold extent
  ring

end MathResearchAnalysis.ClippedRegionBox
