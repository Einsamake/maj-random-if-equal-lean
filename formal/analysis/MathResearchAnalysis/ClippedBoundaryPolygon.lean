module

public import MathResearchAnalysis.ClippedBoundaryCycle
public import MathResearchAnalysis.GridBoundarySegments
public import Mathlib.Geometry.Polygon.Basic

set_option autoImplicit false

/-!
# The actual initial boundary as a polygon

Vertices follow the proved successor permutation of all actual exposed facets.
The edges below are full real segments. No topological frontier or simple-curve
property is included as an input.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.ClippedBoundaryPolygon

open GridCellBoundary GridBoundarySegments ClippedBoundaryCycle

abbrev Index (L : Nat) := Fin (8 * L + 4)

def facetAt (L : Nat) (i : Index L) : Edges L :=
  ((successor L) ^ i.val) (anchor L)

def vertex (L : Nat) (i : Index L) : Plane := realSite (source (facetAt L i).val)

def polygon (L : Nat) : Polygon Plane (8 * L + 4) := ⟨vertex L⟩

theorem facetAt_bijective (L : Nat) (hL : 1 ≤ L) :
    Function.Bijective (facetAt L) := enumeration_bijective L hL (anchor L)

theorem vertex_injective (L : Nat) (hL : 1 ≤ L) : Function.Injective (vertex L) := by
  intro i j hij
  exact vertex_enumeration_injective L hL (anchor L) (realSite_injective hij)

theorem facetAt_next (L : Nat) (hL : 1 ≤ L) (i : Index L) :
    facetAt L (finRotate (8 * L + 4) i) = successor L (facetAt L i) := by
  unfold facetAt
  by_cases hi : i = Fin.last (8 * L + 3)
  · have hv : i.val = 8 * L + 3 := congrArg Fin.val hi
    have hr : (finRotate (8 * L + 4) i).val = 0 := by
      rw [hi, finRotate_last]
      rfl
    rw [hr, hv]
    have hreturn := returns_after_perimeter L hL (anchor L)
    rw [show 8 * L + 4 = (8 * L + 3) + 1 by omega,
      pow_succ', Equiv.Perm.mul_apply] at hreturn
    simpa only [pow_zero, Equiv.Perm.one_apply] using hreturn.symm
  · rw [coe_finRotate_of_ne_last hi, pow_succ', Equiv.Perm.mul_apply]

theorem vertex_next (L : Nat) (hL : 1 ≤ L) (i : Index L) :
    vertex L (finRotate (8 * L + 4) i) = realSite (target (facetAt L i).val) := by
  unfold vertex
  rw [facetAt_next L hL, successor_source]

theorem nondegenerate_edges (L : Nat) (hL : 1 ≤ L) :
    (polygon L).HasNondegenerateEdges := by
  intro i
  change vertex L i ≠ vertex L (finRotate (8 * L + 4) i)
  rw [vertex_next L hL]
  intro heq
  exact source_ne_target (facetAt L i).val (realSite_injective heq)

theorem edgePath_eq_segmentPoint (L : Nat) (hL : 1 ≤ L) (i : Index L) (t : Real) :
    (polygon L).edgePath Real i t = segmentPoint (facetAt L i).val t := by
  change AffineMap.lineMap (vertex L i) (vertex L (finRotate (8 * L + 4) i)) t = _
  rw [vertex_next L hL, AffineMap.lineMap_apply_module, segmentPoint_convex]
  rfl

theorem edgeSet_eq_closedSegment (L : Nat) (hL : 1 ≤ L) (i : Index L) :
    (polygon L).edgeSet Real i = closedSegment (facetAt L i).val := by
  rw [Polygon.edgeSet_eq_image_edgePath]
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht.1, ht.2, edgePath_eq_segmentPoint L hL i t⟩
  · rintro ⟨t, ht0, ht1, rfl⟩
    exact ⟨t, ⟨ht0, ht1⟩, edgePath_eq_segmentPoint L hL i t⟩

theorem mem_boundary_iff (L : Nat) (hL : 1 ≤ L) (p : Plane) :
    p ∈ (polygon L).boundary Real ↔
      ∃ e ∈ boundary (ClippedDiamondGeometry.clippedDomain L), p ∈ closedSegment e := by
  simp only [Polygon.boundary, Set.mem_iUnion, edgeSet_eq_closedSegment L hL]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨(facetAt L i).val, (facetAt L i).property, hi⟩
  · rintro ⟨e, he, hp⟩
    obtain ⟨i, hi⟩ := (facetAt_bijective L hL).2 ⟨e, he⟩
    exact ⟨i, hi ▸ hp⟩

theorem edges_intersect_only_endpoints (L : Nat) (hL : 1 ≤ L)
    {i j : Index L} (hij : i ≠ j) {p : Plane}
    (hi : p ∈ (polygon L).edgeSet Real i) (hj : p ∈ (polygon L).edgeSet Real j) :
    (p = vertex L i ∨ p = vertex L (finRotate (8 * L + 4) i)) ∧
      (p = vertex L j ∨ p = vertex L (finRotate (8 * L + 4) j)) := by
  rw [edgeSet_eq_closedSegment L hL] at hi hj
  have he : (facetAt L i).val ≠ (facetAt L j).val := by
    intro h
    exact hij ((facetAt_bijective L hL).1 (Subtype.ext h))
  have h := boundary_segments_intersect_only_endpoints
    (facetAt L i).property (facetAt L j).property he hi hj
  rw [vertex_next L hL i, vertex_next L hL j]
  exact h

theorem nonadjacent_edges_disjoint (L : Nat) (hL : 1 ≤ L) {i j : Index L}
    (hij : i ≠ j) (hnext : finRotate (8 * L + 4) i ≠ j)
    (hprev : finRotate (8 * L + 4) j ≠ i) :
    Disjoint ((polygon L).edgeSet Real i) ((polygon L).edgeSet Real j) := by
  apply Set.disjoint_left.mpr
  intro p hi hj
  have h := edges_intersect_only_endpoints L hL hij hi hj
  rcases h.1 with hi | hi <;> rcases h.2 with hj | hj
  · exact hij (vertex_injective L hL (hi.symm.trans hj))
  · exact hprev (vertex_injective L hL (hj.symm.trans hi))
  · exact hnext (vertex_injective L hL (hi.symm.trans hj))
  · exact hij ((finRotate (8 * L + 4)).injective
      (vertex_injective L hL (hi.symm.trans hj)))

end MathResearchAnalysis.ClippedBoundaryPolygon
