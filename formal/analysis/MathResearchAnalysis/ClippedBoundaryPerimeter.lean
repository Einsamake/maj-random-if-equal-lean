module

public import MathResearchAnalysis.GridCellBoundary
public import MathResearchAnalysis.ClippedOrthogonalSections

set_option autoImplicit false

/-!
# The actual clipped droplet perimeter

Boundary facets are concrete exposed unit cell sides. Their doubled-coordinate
segments have length two, whereas each facet contributes one to physical
perimeter. The following count is derived from the exact orthogonal sections;
it is not a field of a proposed Good configuration structure.
-/

@[expose] public section

namespace MathResearchAnalysis.ClippedBoundaryPerimeter

open InfiniteGridModel GridCellBoundary ClippedOrthogonalSections

abbrev Site := InfiniteGridModel.Site

/-- The unique upper exposed endpoint of a nonempty integer interval. -/
theorem interval_upper_end (r y : Int) (hr : 0 ≤ r) :
    (|y| ≤ r ∧ ¬ |y + 1| ≤ r) ↔ y = r := by
  simp only [abs_le]
  omega

theorem interval_lower_end (r y : Int) (hr : 0 ≤ r) :
    (|y| ≤ r ∧ ¬ |y - 1| ≤ r) ↔ y = -r := by
  simp only [abs_le]
  omega

theorem north_boundary_iff (L : Nat) (z : Site) :
    (z, (0 : Direction)) ∈ boundary (ClippedDiamondGeometry.clippedDomain L) ↔
      |z.1| ≤ (L : Int) ∧ z.2 = sectionRadius L z.1 := by
  rcases z with ⟨x, y⟩
  rw [mem_boundary]
  change (((x, y) ∈ ClippedDiamondGeometry.clippedDomain L) ∧
    (x, y + 1) ∉ ClippedDiamondGeometry.clippedDomain L) ↔ _
  rw [mem_clipped_column_iff, mem_clipped_column_iff]
  constructor
  · rintro ⟨⟨hx, hy⟩, hn⟩
    exact ⟨hx, (interval_upper_end _ _ (sectionRadius_nonneg L x hx)).mp
      ⟨hy, fun h => hn ⟨hx, h⟩⟩⟩
  · rintro ⟨hx, hy⟩
    have h := (interval_upper_end _ _ (sectionRadius_nonneg L x hx)).mpr hy
    exact ⟨⟨hx, h.1⟩, fun hn => h.2 hn.2⟩

theorem east_boundary_iff (L : Nat) (z : Site) :
    (z, (1 : Direction)) ∈ boundary (ClippedDiamondGeometry.clippedDomain L) ↔
      |z.2| ≤ (L : Int) ∧ z.1 = sectionRadius L z.2 := by
  rcases z with ⟨x, y⟩
  rw [mem_boundary]
  change (((x, y) ∈ ClippedDiamondGeometry.clippedDomain L) ∧
    (x + 1, y) ∉ ClippedDiamondGeometry.clippedDomain L) ↔ _
  rw [mem_clipped_row_iff, mem_clipped_row_iff]
  constructor
  · rintro ⟨⟨hy, hx⟩, hn⟩
    exact ⟨hy, (interval_upper_end _ _ (sectionRadius_nonneg L y hy)).mp
      ⟨hx, fun h => hn ⟨hy, h⟩⟩⟩
  · rintro ⟨hy, hx⟩
    have h := (interval_upper_end _ _ (sectionRadius_nonneg L y hy)).mpr hx
    exact ⟨⟨hy, h.1⟩, fun hn => h.2 hn.2⟩

theorem south_boundary_iff (L : Nat) (z : Site) :
    (z, (2 : Direction)) ∈ boundary (ClippedDiamondGeometry.clippedDomain L) ↔
      |z.1| ≤ (L : Int) ∧ z.2 = -sectionRadius L z.1 := by
  rcases z with ⟨x, y⟩
  rw [mem_boundary]
  change (((x, y) ∈ ClippedDiamondGeometry.clippedDomain L) ∧
    (x, y - 1) ∉ ClippedDiamondGeometry.clippedDomain L) ↔ _
  rw [mem_clipped_column_iff, mem_clipped_column_iff]
  constructor
  · rintro ⟨⟨hx, hy⟩, hn⟩
    exact ⟨hx, (interval_lower_end _ _ (sectionRadius_nonneg L x hx)).mp
      ⟨hy, fun h => hn ⟨hx, h⟩⟩⟩
  · rintro ⟨hx, hy⟩
    have h := (interval_lower_end _ _ (sectionRadius_nonneg L x hx)).mpr hy
    exact ⟨⟨hx, h.1⟩, fun hn => h.2 hn.2⟩

theorem west_boundary_iff (L : Nat) (z : Site) :
    (z, (3 : Direction)) ∈ boundary (ClippedDiamondGeometry.clippedDomain L) ↔
      |z.2| ≤ (L : Int) ∧ z.1 = -sectionRadius L z.2 := by
  rcases z with ⟨x, y⟩
  rw [mem_boundary]
  change (((x, y) ∈ ClippedDiamondGeometry.clippedDomain L) ∧
    (x - 1, y) ∉ ClippedDiamondGeometry.clippedDomain L) ↔ _
  rw [mem_clipped_row_iff, mem_clipped_row_iff]
  constructor
  · rintro ⟨⟨hy, hx⟩, hn⟩
    exact ⟨hy, (interval_lower_end _ _ (sectionRadius_nonneg L y hy)).mp
      ⟨hx, fun h => hn ⟨hy, h⟩⟩⟩
  · rintro ⟨hy, hx⟩
    have h := (interval_lower_end _ _ (sectionRadius_nonneg L y hy)).mpr hx
    exact ⟨⟨hy, h.1⟩, fun hn => h.2 hn.2⟩

/-- Each direction has one exposed facet per integer section coordinate. -/
def facet (L : Nat) (p : Direction × Int) : HalfEdge :=
  let a := p.2
  let r := sectionRadius L a
  (if p.1 = 0 then (a, r) else if p.1 = 1 then (r, a)
    else if p.1 = 2 then (a, -r) else (-r, a), p.1)

def facetIndex (e : HalfEdge) : Direction × Int :=
  (e.2, if e.2 = 0 ∨ e.2 = 2 then e.1.1 else e.1.2)

theorem facetIndex_facet (L : Nat) (p : Direction × Int) :
    facetIndex (facet L p) = p := by
  rcases p with ⟨d, a⟩
  fin_cases d <;> simp [facet, facetIndex]

theorem facet_injective (L : Nat) : Function.Injective (facet L) :=
  (show Function.LeftInverse facetIndex (facet L) from facetIndex_facet L).injective

def facetIndices (L : Nat) : Finset (Direction × Int) :=
  Finset.univ ×ˢ Finset.Icc (-(L : Int)) L

theorem mem_facetIndices (L : Nat) (p : Direction × Int) :
    p ∈ facetIndices L ↔ |p.2| ≤ (L : Int) := by
  simp [facetIndices, abs_le]

theorem facet_mem_boundary (L : Nat) (p : Direction × Int)
    (hp : p ∈ facetIndices L) :
    facet L p ∈ boundary (ClippedDiamondGeometry.clippedDomain L) := by
  have ha := (mem_facetIndices L p).mp hp
  rcases p with ⟨d, a⟩
  fin_cases d
  · simpa [facet] using (north_boundary_iff L (a, sectionRadius L a)).mpr ⟨ha, rfl⟩
  · simpa [facet] using (east_boundary_iff L (sectionRadius L a, a)).mpr ⟨ha, rfl⟩
  · simpa [facet] using (south_boundary_iff L (a, -sectionRadius L a)).mpr ⟨ha, rfl⟩
  · simpa [facet] using (west_boundary_iff L (-sectionRadius L a, a)).mpr ⟨ha, rfl⟩

theorem facetIndex_mem_of_boundary (L : Nat) (e : HalfEdge)
    (he : e ∈ boundary (ClippedDiamondGeometry.clippedDomain L)) :
    facetIndex e ∈ facetIndices L := by
  rcases e with ⟨⟨x,y⟩,d⟩
  rw [mem_facetIndices]
  fin_cases d
  · simpa [facetIndex] using ((north_boundary_iff L (x,y)).mp he).1
  · simpa [facetIndex] using ((east_boundary_iff L (x,y)).mp he).1
  · simpa [facetIndex] using ((south_boundary_iff L (x,y)).mp he).1
  · simpa [facetIndex] using ((west_boundary_iff L (x,y)).mp he).1

theorem facet_facetIndex_of_boundary (L : Nat) (e : HalfEdge)
    (he : e ∈ boundary (ClippedDiamondGeometry.clippedDomain L)) :
    facet L (facetIndex e) = e := by
  rcases e with ⟨⟨x,y⟩,d⟩
  fin_cases d
  · have hy := ((north_boundary_iff L (x,y)).mp he).2
    simpa [facet, facetIndex] using hy.symm
  · have hx := ((east_boundary_iff L (x,y)).mp he).2
    simpa [facet, facetIndex] using hx.symm
  · have hy := ((south_boundary_iff L (x,y)).mp he).2
    simpa [facet, facetIndex] using hy.symm
  · have hx := ((west_boundary_iff L (x,y)).mp he).2
    simpa [facet, facetIndex] using hx.symm

theorem boundary_eq_facet_image (L : Nat) :
    boundary (ClippedDiamondGeometry.clippedDomain L) = (facetIndices L).image (facet L) := by
  ext e
  constructor
  · intro he
    exact Finset.mem_image.mpr ⟨facetIndex e, facetIndex_mem_of_boundary L e he,
      facet_facetIndex_of_boundary L e he⟩
  · intro he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    exact facet_mem_boundary L p hp

theorem boundary_card (L : Nat) :
    (boundary (ClippedDiamondGeometry.clippedDomain L)).card = 4 * (2 * L + 1) := by
  rw [boundary_eq_facet_image, Finset.card_image_of_injective _ (facet_injective L)]
  simp [facetIndices, Int.card_Icc]
  omega

theorem physical_perimeter (L : Nat) :
    perimeter (ClippedDiamondGeometry.clippedDomain L) = 8 * L + 4 := by
  change (boundary (ClippedDiamondGeometry.clippedDomain L)).card = _
  rw [boundary_card]
  omega

end MathResearchAnalysis.ClippedBoundaryPerimeter
