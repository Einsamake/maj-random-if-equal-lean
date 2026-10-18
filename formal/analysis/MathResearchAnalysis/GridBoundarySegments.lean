module

public import MathResearchAnalysis.GridCellBoundary

set_option autoImplicit false

/-!
# Actual continuous segments of exposed cell half-edges

The integer corner coordinates are embedded in R^2. A closed edge contains
all affine interpolation points with parameter in [0,1], not just endpoints.
A strict interior point belongs to no occupied neighboring cell across an
exposed face. This proves endpoint-only intersections without assuming a
contour or a noncrossing field.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.GridBoundarySegments

open GridCellBoundary
open InfiniteGridModel (north east south west)

abbrev Plane := Real × Real

def realSite (z : Site) : Plane := ((z.1 : Real), (z.2 : Real))

def segmentPoint (e : HalfEdge) (t : Real) : Plane :=
  ((realSite (source e)).1 + t * ((realSite (target e)).1 - (realSite (source e)).1),
    (realSite (source e)).2 + t * ((realSite (target e)).2 - (realSite (source e)).2))

def closedSegment (e : HalfEdge) : Set Plane :=
  {p | ∃ t : Real, 0 ≤ t ∧ t ≤ 1 ∧ p = segmentPoint e t}

def cellBox (v : Site) : Set Plane :=
  {p | 2 * (v.1 : Real) - 1 ≤ p.1 ∧ p.1 ≤ 2 * (v.1 : Real) + 1 ∧
    2 * (v.2 : Real) - 1 ≤ p.2 ∧ p.2 ≤ 2 * (v.2 : Real) + 1}

theorem realSite_injective : Function.Injective realSite := by
  intro z w h
  apply Prod.ext
  · have hx := congrArg Prod.fst h
    dsimp [realSite] at hx
    exact_mod_cast hx
  · have hy := congrArg Prod.snd h
    dsimp [realSite] at hy
    exact_mod_cast hy

theorem mem_closedSegment (e : HalfEdge) (p : Plane) :
    p ∈ closedSegment e ↔ ∃ t : Real, 0 ≤ t ∧ t ≤ 1 ∧ p = segmentPoint e t := Iff.rfl

theorem segmentPoint_convex (e : HalfEdge) (t : Real) :
    segmentPoint e t =
      ((1-t) * (realSite (source e)).1 + t * (realSite (target e)).1,
        (1-t) * (realSite (source e)).2 + t * (realSite (target e)).2) := by
  apply Prod.ext <;> dsimp [segmentPoint] <;> ring

@[simp] theorem segmentPoint_zero (e : HalfEdge) : segmentPoint e 0 = realSite (source e) := by
  simp [segmentPoint]

@[simp] theorem segmentPoint_one (e : HalfEdge) : segmentPoint e 1 = realSite (target e) := by
  apply Prod.ext <;> dsimp [segmentPoint, realSite] <;> ring

theorem source_mem_closedSegment (e : HalfEdge) : realSite (source e) ∈ closedSegment e :=
  ⟨0, le_refl _, by norm_num, (segmentPoint_zero e).symm⟩

theorem target_mem_closedSegment (e : HalfEdge) : realSite (target e) ∈ closedSegment e :=
  ⟨1, by norm_num, le_refl _, (segmentPoint_one e).symm⟩

@[simp] theorem segmentPoint_north (v : Site) (t : Real) :
    segmentPoint (v, ⟨0, by decide⟩) t = (2 * (v.1 : Real) + 1 - 2*t, 2 * (v.2 : Real) + 1) := by
  apply Prod.ext <;> dsimp [segmentPoint, realSite, source, target] <;> push_cast <;> ring

@[simp] theorem segmentPoint_east (v : Site) (t : Real) :
    segmentPoint (v, ⟨1, by decide⟩) t = (2 * (v.1 : Real) + 1, 2 * (v.2 : Real) - 1 + 2*t) := by
  apply Prod.ext <;> dsimp [segmentPoint, realSite, source, target] <;> push_cast <;> ring

@[simp] theorem segmentPoint_south (v : Site) (t : Real) :
    segmentPoint (v, ⟨2, by decide⟩) t = (2 * (v.1 : Real) - 1 + 2*t, 2 * (v.2 : Real) - 1) := by
  apply Prod.ext <;> dsimp [segmentPoint, realSite, source, target] <;> push_cast <;> ring

@[simp] theorem segmentPoint_west (v : Site) (t : Real) :
    segmentPoint (v, ⟨3, by decide⟩) t = (2 * (v.1 : Real) - 1, 2 * (v.2 : Real) + 1 - 2*t) := by
  apply Prod.ext <;> dsimp [segmentPoint, realSite, source, target] <;> push_cast <;> ring

theorem segmentPoint_mem_cellBox (e : HalfEdge) (t : Real) (ht : 0 ≤ t ∧ t ≤ 1) :
    segmentPoint e t ∈ cellBox e.1 := by
  rcases e with ⟨v, d⟩
  fin_cases d <;> simp only [segmentPoint_north, segmentPoint_east, segmentPoint_south,
    segmentPoint_west, cellBox, Set.mem_ofPred_eq]
  all_goals repeat' constructor
  all_goals linarith [ht.1, ht.2]

theorem closedSegment_subset_cellBox (e : HalfEdge) : closedSegment e ⊆ cellBox e.1 := by
  rintro p ⟨t, ht0, ht1, rfl⟩
  exact segmentPoint_mem_cellBox e t ⟨ht0, ht1⟩

private theorem cell_center_unique_in_strict_interval (a b : Int) (x : Real)
    (ha0 : 2 * (a : Real) - 1 < x) (ha1 : x < 2 * (a : Real) + 1)
    (hb0 : 2 * (b : Real) - 1 ≤ x) (hb1 : x ≤ 2 * (b : Real) + 1) : b = a := by
  have hhi : (b : Real) < (a : Real) + 1 := by linarith
  have hlo : (a : Real) < (b : Real) + 1 := by linarith
  have hhiZ : b < a + 1 := by exact_mod_cast hhi
  have hloZ : a < b + 1 := by exact_mod_cast hlo
  omega

private theorem cell_center_on_positive_face (a b : Int)
    (hlo : 2 * (b : Real) - 1 ≤ 2 * (a : Real) + 1)
    (hhi : 2 * (a : Real) + 1 ≤ 2 * (b : Real) + 1) : b = a ∨ b = a + 1 := by
  have hloR : (a : Real) ≤ (b : Real) := by linarith
  have hhiR : (b : Real) ≤ (a : Real) + 1 := by linarith
  have hloZ : a ≤ b := by exact_mod_cast hloR
  have hhiZ : b ≤ a + 1 := by exact_mod_cast hhiR
  omega

private theorem cell_center_on_negative_face (a b : Int)
    (hlo : 2 * (b : Real) - 1 ≤ 2 * (a : Real) - 1)
    (hhi : 2 * (a : Real) - 1 ≤ 2 * (b : Real) + 1) : b = a ∨ b = a - 1 := by
  have hloR : (a : Real) - 1 ≤ (b : Real) := by linarith
  have hhiR : (b : Real) ≤ (a : Real) := by linarith
  have hloZ : a - 1 ≤ b := by exact_mod_cast hloR
  have hhiZ : b ≤ a := by exact_mod_cast hhiR
  omega

/-- A strict interior point lies only in its own cell or the cell across this face. -/
theorem interior_cell_owner_or_neighbor (e : HalfEdge) (t : Real)
    (ht0 : 0 < t) (ht1 : t < 1) (w : Site)
    (hw : segmentPoint e t ∈ cellBox w) : w = e.1 ∨ w = neighbor e.1 e.2 := by
  rcases e with ⟨v, d⟩
  fin_cases d
  · rw [segmentPoint_north] at hw
    obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
    have hx := cell_center_unique_in_strict_interval v.1 w.1
      (2 * (v.1 : Real) + 1 - 2*t) (by linarith) (by linarith) hx0 hx1
    have hy := cell_center_on_positive_face v.2 w.2 hy0 hy1
    rcases hy with hy | hy
    · exact Or.inl (Prod.ext hx hy)
    · exact Or.inr (Prod.ext hx hy)
  · rw [segmentPoint_east] at hw
    obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
    have hy := cell_center_unique_in_strict_interval v.2 w.2
      (2 * (v.2 : Real) - 1 + 2*t) (by linarith) (by linarith) hy0 hy1
    have hx := cell_center_on_positive_face v.1 w.1 hx0 hx1
    rcases hx with hx | hx
    · exact Or.inl (Prod.ext hx hy)
    · exact Or.inr (Prod.ext hx hy)
  · rw [segmentPoint_south] at hw
    obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
    have hx := cell_center_unique_in_strict_interval v.1 w.1
      (2 * (v.1 : Real) - 1 + 2*t) (by linarith) (by linarith) hx0 hx1
    have hy := cell_center_on_negative_face v.2 w.2 hy0 hy1
    rcases hy with hy | hy
    · exact Or.inl (Prod.ext hx hy)
    · exact Or.inr (Prod.ext hx hy)
  · rw [segmentPoint_west] at hw
    obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
    have hy := cell_center_unique_in_strict_interval v.2 w.2
      (2 * (v.2 : Real) + 1 - 2*t) (by linarith) (by linarith) hy0 hy1
    have hx := cell_center_on_negative_face v.1 w.1 hx0 hx1
    rcases hx with hx | hx
    · exact Or.inl (Prod.ext hx hy)
    · exact Or.inr (Prod.ext hx hy)

theorem direction_eq_of_same_cell_interior (v : Site) (d c : Direction) (t u : Real)
    (ht0 : 0 < t) (ht1 : t < 1) (h : segmentPoint (v,d) t = segmentPoint (v,c) u) : d = c := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases d <;> fin_cases c <;>
    simp only [segmentPoint_north, segmentPoint_east, segmentPoint_south,
      segmentPoint_west] at hx hy
  all_goals first | rfl | linarith

theorem common_point_is_left_endpoint {S : Finset Site} {e f : HalfEdge} {p : Plane}
    (he : e ∈ boundary S) (hf : f ∈ boundary S) (hne : e ≠ f)
    (hp : p ∈ closedSegment e) (hq : p ∈ closedSegment f) :
    p = realSite (source e) ∨ p = realSite (target e) := by
  obtain ⟨t, ht0, ht1, rfl⟩ := hp
  by_cases hz : t = 0
  · subst t
    exact Or.inl (segmentPoint_zero e)
  by_cases ho : t = 1
  · subst t
    exact Or.inr (segmentPoint_one e)
  have ht0' : 0 < t := lt_of_le_of_ne ht0 (fun h => hz h.symm)
  have ht1' : t < 1 := lt_of_le_of_ne ht1 ho
  have hw := interior_cell_owner_or_neighbor e t ht0' ht1' f.1
    (closedSegment_subset_cellBox f hq)
  rcases hw with hw | hw
  · obtain ⟨u, _, _, hu⟩ := hq
    rcases e with ⟨v,d⟩
    rcases f with ⟨w,c⟩
    dsimp at hw
    subst w
    have hd := direction_eq_of_same_cell_interior v d c t u ht0' ht1' hu
    exact False.elim (hne (Prod.ext rfl hd))
  · exact False.elim (boundary_neighbor_not_mem he (hw ▸ boundary_owner_mem hf))

/-- Different actual exposed faces intersect only at an endpoint of each face. -/
theorem boundary_segments_intersect_only_endpoints
    {S : Finset Site} {e f : HalfEdge} {p : Plane}
    (he : e ∈ boundary S) (hf : f ∈ boundary S) (hne : e ≠ f)
    (hp : p ∈ closedSegment e) (hq : p ∈ closedSegment f) :
    (p = realSite (source e) ∨ p = realSite (target e)) ∧
      (p = realSite (source f) ∨ p = realSite (target f)) :=
  ⟨common_point_is_left_endpoint he hf hne hp hq,
    common_point_is_left_endpoint hf he hne.symm hq hp⟩

end MathResearchAnalysis.GridBoundarySegments


