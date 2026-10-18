module

public import MathResearchAnalysis.GridPhysicalRegion
public import MathResearchAnalysis.ClippedRegionBox

set_option autoImplicit false

/-!
# The true minimum rectangle in the original unit-cell scale

The explicit half-scale homeomorphism transports the actual region, frontier,
and attained extreme points. Consequently the rectangle is minimal for the
entire original-unit region and its actual topological frontier. The numerical
perimeter identity is a rectangle/facet equality, not an arc-length theorem.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.ClippedPhysicalBox

open GridCellBoundary GridBoundarySegments GridCellRegion GridPhysicalRegion

def physicalExtent (L : Nat) : Real := ClippedRegionBox.extent L / 2

def box (L : Nat) : Set Plane :=
  Set.Icc (-(physicalExtent L)) (physicalExtent L) ×ˢ
    Set.Icc (-(physicalExtent L)) (physicalExtent L)

theorem physicalExtent_eq (L : Nat) : physicalExtent L = (L : Real) + 1/2 := by
  unfold physicalExtent ClippedRegionBox.extent
  ring

theorem physicalExtent_pos (L : Nat) : 0 < physicalExtent L := by
  rw [physicalExtent_eq]
  positivity

theorem halfScale_mem_box_iff (L : Nat) (p : Plane) :
    halfScale p ∈ box L ↔ p ∈ ClippedRegionBox.box L := by
  change ((-(ClippedRegionBox.extent L / 2) ≤ p.1/2 ∧ p.1/2 ≤ ClippedRegionBox.extent L/2) ∧
    (-(ClippedRegionBox.extent L / 2) ≤ p.2/2 ∧ p.2/2 ≤ ClippedRegionBox.extent L/2)) ↔
    ((-(ClippedRegionBox.extent L) ≤ p.1 ∧ p.1 ≤ ClippedRegionBox.extent L) ∧
      (-(ClippedRegionBox.extent L) ≤ p.2 ∧ p.2 ≤ ClippedRegionBox.extent L))
  constructor <;> rintro ⟨⟨hx0,hx1⟩,⟨hy0,hy1⟩⟩
  all_goals repeat' constructor
  all_goals linarith

theorem halfScale_image_box (L : Nat) : halfScale '' ClippedRegionBox.box L = box L := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact (halfScale_mem_box_iff L q).mpr hq
  · intro hp
    refine ⟨halfScale.symm p, ?_, halfScale.apply_symm_apply p⟩
    apply (halfScale_mem_box_iff L _).mp
    simpa only [halfScale.apply_symm_apply] using hp

theorem region_subset_box (L : Nat) :
    unitRegion (ClippedDiamondGeometry.clippedDomain L) ⊆ box L := by
  rw [← halfScale_image_region, ← halfScale_image_box]
  exact Set.image_mono (ClippedRegionBox.region_subset_box L)

theorem frontier_subset_box (L : Nat) :
    frontier (unitRegion (ClippedDiamondGeometry.clippedDomain L)) ⊆ box L :=
  (isClosed_unitRegion _).frontier_subset.trans (region_subset_box L)

theorem right_frontier (L : Nat) :
    (physicalExtent L, -(1/2 : Real)) ∈
      frontier (unitRegion (ClippedDiamondGeometry.clippedDomain L)) := by
  have h : halfScale (ClippedRegionBox.extent L, -1) ∈
      halfScale '' frontier (region (ClippedDiamondGeometry.clippedDomain L)) :=
    ⟨_, ClippedRegionBox.right_frontier L, rfl⟩
  rw [halfScale_frontier_region] at h
  simpa [halfScale_apply, physicalExtent, neg_div] using h

theorem left_frontier (L : Nat) :
    (-(physicalExtent L), (1/2 : Real)) ∈
      frontier (unitRegion (ClippedDiamondGeometry.clippedDomain L)) := by
  have h : halfScale (-(ClippedRegionBox.extent L), 1) ∈
      halfScale '' frontier (region (ClippedDiamondGeometry.clippedDomain L)) :=
    ⟨_, ClippedRegionBox.left_frontier L, rfl⟩
  rw [halfScale_frontier_region] at h
  simpa [halfScale_apply, physicalExtent, neg_div] using h

theorem top_frontier (L : Nat) :
    ((1/2 : Real), physicalExtent L) ∈
      frontier (unitRegion (ClippedDiamondGeometry.clippedDomain L)) := by
  have h : halfScale (1, ClippedRegionBox.extent L) ∈
      halfScale '' frontier (region (ClippedDiamondGeometry.clippedDomain L)) :=
    ⟨_, ClippedRegionBox.top_frontier L, rfl⟩
  rw [halfScale_frontier_region] at h
  simpa [halfScale_apply, physicalExtent] using h

theorem bottom_frontier (L : Nat) :
    (-(1/2 : Real), -(physicalExtent L)) ∈
      frontier (unitRegion (ClippedDiamondGeometry.clippedDomain L)) := by
  have h : halfScale (-1, -(ClippedRegionBox.extent L)) ∈
      halfScale '' frontier (region (ClippedDiamondGeometry.clippedDomain L)) :=
    ⟨_, ClippedRegionBox.bottom_frontier L, rfl⟩
  rw [halfScale_frontier_region] at h
  simpa [halfScale_apply, physicalExtent, neg_div] using h

theorem minimum_frontier_rectangle (L : Nat) (a b c d : Real)
    (h : frontier (unitRegion (ClippedDiamondGeometry.clippedDomain L)) ⊆
      Set.Icc a b ×ˢ Set.Icc c d) : box L ⊆ Set.Icc a b ×ˢ Set.Icc c d := by
  have hl := h (left_frontier L)
  have hr := h (right_frontier L)
  have ht := h (top_frontier L)
  have hb := h (bottom_frontier L)
  rintro p ⟨hx,hy⟩
  exact ⟨⟨hl.1.1.trans hx.1, hx.2.trans hr.1.2⟩,
    ⟨hb.2.1.trans hy.1, hy.2.trans ht.2.2⟩⟩

theorem minimum_region_rectangle (L : Nat) (a b c d : Real)
    (h : unitRegion (ClippedDiamondGeometry.clippedDomain L) ⊆
      Set.Icc a b ×ˢ Set.Icc c d) : box L ⊆ Set.Icc a b ×ˢ Set.Icc c d :=
  minimum_frontier_rectangle L a b c d ((isClosed_unitRegion _).frontier_subset.trans h)

theorem physical_span (L : Nat) :
    physicalExtent L - (-(physicalExtent L)) = 2 * (L : Real) + 1 := by
  rw [physicalExtent_eq]
  ring

theorem rectangle_perimeter (L : Nat) :
    2 * ((physicalExtent L - (-(physicalExtent L))) +
      (physicalExtent L - (-(physicalExtent L)))) = 8 * (L : Real) + 4 := by
  rw [physicalExtent_eq]
  ring

theorem facet_perimeter_eq_rectangle (L : Nat) :
    (perimeter (ClippedDiamondGeometry.clippedDomain L) : Real) =
      2 * ((physicalExtent L - (-(physicalExtent L))) +
        (physicalExtent L - (-(physicalExtent L)))) := by
  rw [rectangle_perimeter, ClippedBoundaryPerimeter.physical_perimeter]
  push_cast
  ring

end MathResearchAnalysis.ClippedPhysicalBox

