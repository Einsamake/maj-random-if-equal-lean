module

public import MathResearchAnalysis.OrthogonalBoundaryCycle
public import MathResearchAnalysis.GridBoundarySegments
public import Mathlib.Geometry.Polygon.Basic

set_option autoImplicit false

/-!
# The general actual boundary as a polygon

Vertices follow the proved successor permutation of all actual exposed facets.
The edges below are full real segments. No topological frontier or simple-curve
property is included as an input.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.OrthogonalBoundaryPolygon

open GridCellBoundary GridBoundarySegments OrthogonalBoundaryCycle

abbrev Index (R : Region) := Fin (perimeter R.val)

def facetAt (R : Region) (i : Index R) : Edges R :=
  ((successor R) ^ i.val) (anchor R)

def vertex (R : Region) (i : Index R) : Plane := realSite (source (facetAt R i).val)

def polygon (R : Region) : Polygon Plane (perimeter R.val) := ⟨vertex R⟩

theorem facetAt_bijective (R : Region)  :
    Function.Bijective (facetAt R) := enumeration_bijective R (anchor R)

theorem vertex_injective (R : Region)  : Function.Injective (vertex R) := by
  intro i j hij
  exact vertex_enumeration_injective R (anchor R) (realSite_injective hij)

theorem rotate_val {n : Nat} (i : Fin n) :
    (finRotate n i).val = if i.val+1 = n then 0 else i.val+1 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [coe_finRotate]
    by_cases hi : i = Fin.last n
    · simp [hi]
    · rw [ite_eq_right hi,ite_eq_right (by intro h; apply hi; apply Fin.ext; simpa only [Fin.val_last] using (Nat.add_right_cancel h))]

theorem facetAt_next (R : Region) (i : Index R) :
    facetAt R (finRotate (perimeter R.val) i) = successor R (facetAt R i) := by
  unfold facetAt
  rw [rotate_val]
  split_ifs with hi
  · have hreturn := returns_after_perimeter R (anchor R)
    rw [← hi,pow_succ',Equiv.Perm.mul_apply] at hreturn
    simpa only [pow_zero,Equiv.Perm.one_apply] using hreturn.symm
  · rw [pow_succ',Equiv.Perm.mul_apply]

theorem vertex_next (R : Region)  (i : Index R) :
    vertex R (finRotate (perimeter R.val) i) = realSite (target (facetAt R i).val) := by
  unfold vertex
  rw [facetAt_next R, successor_source]

theorem nondegenerate_edges (R : Region)  :
    (polygon R).HasNondegenerateEdges := by
  intro i
  change vertex R i ≠ vertex R (finRotate (perimeter R.val) i)
  rw [vertex_next R]
  intro heq
  exact source_ne_target (facetAt R i).val (realSite_injective heq)

theorem edgePath_eq_segmentPoint (R : Region)  (i : Index R) (t : Real) :
    (polygon R).edgePath Real i t = segmentPoint (facetAt R i).val t := by
  change AffineMap.lineMap (vertex R i) (vertex R (finRotate (perimeter R.val) i)) t = _
  rw [vertex_next R, AffineMap.lineMap_apply_module, segmentPoint_convex]
  rfl

theorem edgeSet_eq_closedSegment (R : Region)  (i : Index R) :
    (polygon R).edgeSet Real i = closedSegment (facetAt R i).val := by
  rw [Polygon.edgeSet_eq_image_edgePath]
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht.1, ht.2, edgePath_eq_segmentPoint R i t⟩
  · rintro ⟨t, ht0, ht1, rfl⟩
    exact ⟨t, ⟨ht0, ht1⟩, edgePath_eq_segmentPoint R i t⟩

theorem mem_boundary_iff (R : Region)  (p : Plane) :
    p ∈ (polygon R).boundary Real ↔
      ∃ e ∈ boundary R.val, p ∈ closedSegment e := by
  simp only [Polygon.boundary, Set.mem_iUnion, edgeSet_eq_closedSegment R]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨(facetAt R i).val, (facetAt R i).property, hi⟩
  · rintro ⟨e, he, hp⟩
    obtain ⟨i, hi⟩ := (facetAt_bijective R).2 ⟨e, he⟩
    exact ⟨i, hi ▸ hp⟩

theorem edges_intersect_only_endpoints (R : Region) 
    {i j : Index R} (hij : i ≠ j) {p : Plane}
    (hi : p ∈ (polygon R).edgeSet Real i) (hj : p ∈ (polygon R).edgeSet Real j) :
    (p = vertex R i ∨ p = vertex R (finRotate (perimeter R.val) i)) ∧
      (p = vertex R j ∨ p = vertex R (finRotate (perimeter R.val) j)) := by
  rw [edgeSet_eq_closedSegment R] at hi hj
  have he : (facetAt R i).val ≠ (facetAt R j).val := by
    intro h
    exact hij ((facetAt_bijective R).1 (Subtype.ext h))
  have h := boundary_segments_intersect_only_endpoints
    (facetAt R i).property (facetAt R j).property he hi hj
  rw [vertex_next R i, vertex_next R j]
  exact h

theorem nonadjacent_edges_disjoint (R : Region)  {i j : Index R}
    (hij : i ≠ j) (hnext : finRotate (perimeter R.val) i ≠ j)
    (hprev : finRotate (perimeter R.val) j ≠ i) :
    Disjoint ((polygon R).edgeSet Real i) ((polygon R).edgeSet Real j) := by
  apply Set.disjoint_left.mpr
  intro p hi hj
  have h := edges_intersect_only_endpoints R hij hi hj
  rcases h.1 with hi | hi <;> rcases h.2 with hj | hj
  · exact hij (vertex_injective R (hi.symm.trans hj))
  · exact hprev (vertex_injective R (hj.symm.trans hi))
  · exact hnext (vertex_injective R (hi.symm.trans hj))
  · exact hij ((finRotate (perimeter R.val)).injective
      (vertex_injective R (hi.symm.trans hj)))

end MathResearchAnalysis.OrthogonalBoundaryPolygon
