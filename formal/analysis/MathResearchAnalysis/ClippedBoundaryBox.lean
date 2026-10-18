module

public import MathResearchAnalysis.ClippedBoundaryPerimeter

set_option autoImplicit false

/-!
# Actual extreme boundary coordinates of the initial clipped droplet

Coordinates are doubled. Physical perimeter is the exposed unit-facet count;
the sum of the two doubled coordinate spans equals twice physical width plus
height. The equality below is derived for the actual initial set. It is not
a simple-curve assertion or a proposed invariant for arbitrary configurations.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.ClippedBoundaryBox

open InfiniteGridModel GridCellBoundary ClippedBoundaryPerimeter ClippedOrthogonalSections

abbrev Site := InfiniteGridModel.Site

def vertices (L : Nat) : Finset Site :=
  ((boundary (ClippedDiamondGeometry.clippedDomain L)).image source) ∪
    ((boundary (ClippedDiamondGeometry.clippedDomain L)).image target)

theorem source_mem_vertices (L : Nat) {e : HalfEdge}
    (he : e ∈ boundary (ClippedDiamondGeometry.clippedDomain L)) : source e ∈ vertices L :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)

theorem target_mem_vertices (L : Nat) {e : HalfEdge}
    (he : e ∈ boundary (ClippedDiamondGeometry.clippedDomain L)) : target e ∈ vertices L :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)

theorem corner_bounds (L : Nat) (z p : Site)
    (hz : z ∈ ClippedDiamondGeometry.clippedDomain L) (hp : p ∈ cellCorners z) :
    |p.1| ≤ 2 * (L : Int) + 1 ∧ |p.2| ≤ 2 * (L : Int) + 1 := by
  have h := (ClippedDiamondGeometry.mem_clippedDomain L z).mp hz
  have hx := abs_le.mp h.1
  have hy := abs_le.mp h.2.1
  simp only [cellCorners, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  all_goals constructor <;> rw [abs_le] <;> constructor <;> dsimp <;> omega

theorem vertex_bounds (L : Nat) (p : Site) (hp : p ∈ vertices L) :
    |p.1| ≤ 2 * (L : Int) + 1 ∧ |p.2| ≤ 2 * (L : Int) + 1 := by
  rcases Finset.mem_union.mp hp with hs | ht
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hs
    exact corner_bounds L e.1 (source e) (boundary_owner_mem he) (source_mem_cellCorners e)
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ht
    exact corner_bounds L e.1 (target e) (boundary_owner_mem he) (target_mem_cellCorners e)

theorem right_vertex (L : Nat) : (2 * (L : Int) + 1, -1) ∈ vertices L := by
  have h : (((L : Int), 0), (1 : Direction)) ∈
      boundary (ClippedDiamondGeometry.clippedDomain L) := by
    apply (east_boundary_iff L ((L : Int), 0)).mpr
    simp [sectionRadius_zero]
  simpa using source_mem_vertices L h

theorem left_vertex (L : Nat) : (-2 * (L : Int) - 1, 1) ∈ vertices L := by
  have h : ((-(L : Int), 0), (3 : Direction)) ∈
      boundary (ClippedDiamondGeometry.clippedDomain L) := by
    apply (west_boundary_iff L (-(L : Int), 0)).mpr
    simp [sectionRadius_zero]
  have he : source ((-(L : Int), 0), (3 : Direction)) = (-2 * (L : Int) - 1, 1) := by
    simp only [source_west]
    apply Prod.ext
    · dsimp
      ring
    · norm_num
  rw [← he]
  exact source_mem_vertices L h

theorem top_vertex (L : Nat) : (1, 2 * (L : Int) + 1) ∈ vertices L := by
  have h : ((0, (L : Int)), (0 : Direction)) ∈
      boundary (ClippedDiamondGeometry.clippedDomain L) := by
    apply (north_boundary_iff L (0, (L : Int))).mpr
    simp [sectionRadius_zero]
  simpa using source_mem_vertices L h

theorem bottom_vertex (L : Nat) : (-1, -2 * (L : Int) - 1) ∈ vertices L := by
  have h : ((0, -(L : Int)), (2 : Direction)) ∈
      boundary (ClippedDiamondGeometry.clippedDomain L) := by
    apply (south_boundary_iff L (0, -(L : Int))).mpr
    simp [sectionRadius_zero]
  have he : source ((0, -(L : Int)), (2 : Direction)) = (-1, -2 * (L : Int) - 1) := by
    simp only [source_south]
    apply Prod.ext
    · norm_num
    · dsimp
      ring
  rw [← he]
  exact source_mem_vertices L h

def coordinate (horizontal : Bool) (p : Site) : Int := if horizontal then p.1 else p.2

def coordinates (L : Nat) (horizontal : Bool) : Finset Int :=
  (vertices L).image (coordinate horizontal)

theorem lower_mem_coordinates (L : Nat) (horizontal : Bool) :
    -2 * (L : Int) - 1 ∈ coordinates L horizontal := by
  cases horizontal
  · exact Finset.mem_image.mpr ⟨_, bottom_vertex L, rfl⟩
  · exact Finset.mem_image.mpr ⟨_, left_vertex L, rfl⟩

theorem upper_mem_coordinates (L : Nat) (horizontal : Bool) :
    2 * (L : Int) + 1 ∈ coordinates L horizontal := by
  cases horizontal
  · exact Finset.mem_image.mpr ⟨_, top_vertex L, rfl⟩
  · exact Finset.mem_image.mpr ⟨_, right_vertex L, rfl⟩

theorem coordinates_nonempty (L : Nat) (horizontal : Bool) :
    (coordinates L horizontal).Nonempty := ⟨_, lower_mem_coordinates L horizontal⟩

theorem coordinate_bounds (L : Nat) (horizontal : Bool) (a : Int)
    (ha : a ∈ coordinates L horizontal) :
    -2 * (L : Int) - 1 ≤ a ∧ a ≤ 2 * (L : Int) + 1 := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
  have hb := vertex_bounds L p hp
  cases horizontal <;> dsimp [coordinate]
  · have hy := abs_le.mp hb.2
    constructor <;> omega
  · have hx := abs_le.mp hb.1
    constructor <;> omega

def minimum (L : Nat) (horizontal : Bool) : Int :=
  (coordinates L horizontal).min' (coordinates_nonempty L horizontal)

def maximum (L : Nat) (horizontal : Bool) : Int :=
  (coordinates L horizontal).max' (coordinates_nonempty L horizontal)

theorem minimum_eq (L : Nat) (horizontal : Bool) :
    minimum L horizontal = -2 * (L : Int) - 1 := by
  apply le_antisymm
  · exact Finset.min'_le _ _ (lower_mem_coordinates L horizontal)
  · exact (coordinate_bounds L horizontal _ (Finset.min'_mem _ _)).1

theorem maximum_eq (L : Nat) (horizontal : Bool) :
    maximum L horizontal = 2 * (L : Int) + 1 := by
  apply le_antisymm
  · exact (coordinate_bounds L horizontal _ (Finset.max'_mem _ _)).2
  · exact Finset.le_max' _ _ (upper_mem_coordinates L horizontal)

theorem doubled_span (L : Nat) (horizontal : Bool) :
    maximum L horizontal - minimum L horizontal = 4 * (L : Int) + 2 := by
  rw [maximum_eq, minimum_eq]
  omega

/-- The paper's minimal-rectangle perimeter equality for the actual initial set,
written in doubled coordinates with the physical unit-facet perimeter. -/
theorem perimeter_eq_doubled_spans (L : Nat) :
    (perimeter (ClippedDiamondGeometry.clippedDomain L) : Int) =
      (maximum L true - minimum L true) + (maximum L false - minimum L false) := by
  rw [physical_perimeter, doubled_span, doubled_span]
  omega

end MathResearchAnalysis.ClippedBoundaryBox
