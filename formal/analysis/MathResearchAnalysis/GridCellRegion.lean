module

public import MathResearchAnalysis.GridBoundarySegments
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Constructions.SumProd

set_option autoImplicit false

/-!
# The actual finite occupied cell region and its exposed faces

The region is the union of genuine closed, twice-scaled real cell boxes.
Empty-cell open interiors lie outside this union, and their closures include
whole exposed faces, including corners. This proves exposed segments are in
the actual topological frontier, without assuming the desired identification.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.GridCellRegion

open GridCellBoundary GridBoundarySegments
open InfiniteGridModel (north east south west)
open Set

/-- The real closed-cell union of the actual occupied lattice sites. -/
def region (S : Finset Site) : Set Plane := ⋃ v ∈ S, cellBox v

/-- The genuine open rectangle strictly inside one lattice cell. -/
def cellInterior (v : Site) : Set Plane :=
  Ioo (2 * (v.1 : Real) - 1) (2 * (v.1 : Real) + 1) ×ˢ
    Ioo (2 * (v.2 : Real) - 1) (2 * (v.2 : Real) + 1)

theorem mem_region (S : Finset Site) (p : Plane) :
    p ∈ region S ↔ ∃ v ∈ S, p ∈ cellBox v := by
  simp only [region, mem_iUnion, exists_prop]

theorem mem_cellInterior (v : Site) (p : Plane) :
    p ∈ cellInterior v ↔
      2 * (v.1 : Real) - 1 < p.1 ∧ p.1 < 2 * (v.1 : Real) + 1 ∧
      2 * (v.2 : Real) - 1 < p.2 ∧ p.2 < 2 * (v.2 : Real) + 1 := by
  simp only [cellInterior, mem_prod, mem_Ioo]
  tauto

theorem cellBox_eq_prod (v : Site) :
    cellBox v =
      Icc (2 * (v.1 : Real) - 1) (2 * (v.1 : Real) + 1) ×ˢ
        Icc (2 * (v.2 : Real) - 1) (2 * (v.2 : Real) + 1) := by
  ext p
  simp only [cellBox, mem_ofPred_eq, mem_prod, mem_Icc]
  tauto

theorem isCompact_cellBox (v : Site) : IsCompact (cellBox v) := by
  rw [cellBox_eq_prod]
  exact isCompact_Icc.prod isCompact_Icc

theorem isClosed_cellBox (v : Site) : IsClosed (cellBox v) := (isCompact_cellBox v).isClosed

theorem isOpen_cellInterior (v : Site) : IsOpen (cellInterior v) :=
  isOpen_Ioo.prod isOpen_Ioo

theorem closure_cellInterior (v : Site) : closure (cellInterior v) = cellBox v := by
  unfold cellInterior
  rw [closure_prod_eq,
    closure_Ioo (show 2 * (v.1 : Real) - 1 ≠ 2 * (v.1 : Real) + 1 by linarith),
    closure_Ioo (show 2 * (v.2 : Real) - 1 ≠ 2 * (v.2 : Real) + 1 by linarith)]
  exact (cellBox_eq_prod v).symm

theorem isCompact_region (S : Finset Site) : IsCompact (region S) :=
  S.isCompact_biUnion (fun v _ => isCompact_cellBox v)

theorem isClosed_region (S : Finset Site) : IsClosed (region S) :=
  (isCompact_region S).isClosed

theorem frontier_region_subset (S : Finset Site) : frontier (region S) ⊆ region S :=
  (isClosed_region S).frontier_subset
@[simp] theorem region_empty : region ∅ = ∅ := by simp [region]

theorem cellBox_subset_region {S : Finset Site} {v : Site} (hv : v ∈ S) :
    cellBox v ⊆ region S := by
  intro p hp
  exact (mem_region S p).mpr ⟨v, hv, hp⟩

theorem region_mono {S T : Finset Site} (hST : S ⊆ T) : region S ⊆ region T := by
  intro p hp
  obtain ⟨v, hv, hpv⟩ := (mem_region S p).mp hp
  exact (mem_region T p).mpr ⟨v, hST hv, hpv⟩

theorem cellInterior_subset_cellBox (v : Site) : cellInterior v ⊆ cellBox v := by
  intro p hp
  obtain ⟨hx0, hx1, hy0, hy1⟩ := (mem_cellInterior v p).mp hp
  exact ⟨hx0.le, hx1.le, hy0.le, hy1.le⟩

theorem cellInterior_subset_interior_region {S : Finset Site} {v : Site} (hv : v ∈ S) :
    cellInterior v ⊆ interior (region S) :=
  interior_maximal ((cellInterior_subset_cellBox v).trans (cellBox_subset_region hv))
    (isOpen_cellInterior v)
private theorem unique_integer_cell_center (a b : Int) (x : Real)
    (ha0 : 2 * (a : Real) - 1 < x) (ha1 : x < 2 * (a : Real) + 1)
    (hb0 : 2 * (b : Real) - 1 ≤ x) (hb1 : x ≤ 2 * (b : Real) + 1) : b = a := by
  have hhi : (b : Real) < (a : Real) + 1 := by linarith
  have hlo : (a : Real) < (b : Real) + 1 := by linarith
  have hhiZ : b < a + 1 := by exact_mod_cast hhi
  have hloZ : a < b + 1 := by exact_mod_cast hlo
  omega

/-- An open cell interior meets the closed box of no other lattice cell. -/
theorem cellInterior_owner_unique (v w : Site) {p : Plane}
    (hp : p ∈ cellInterior v) (hq : p ∈ cellBox w) : w = v := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := (mem_cellInterior v p).mp hp
  obtain ⟨hwx0, hwx1, hwy0, hwy1⟩ := hq
  exact Prod.ext
    (unique_integer_cell_center v.1 w.1 p.1 hx0 hx1 hwx0 hwx1)
    (unique_integer_cell_center v.2 w.2 p.2 hy0 hy1 hwy0 hwy1)

theorem cellInterior_subset_compl_region {S : Finset Site} {w : Site} (hw : w ∉ S) :
    cellInterior w ⊆ (region S)ᶜ := by
  intro p hp hreg
  obtain ⟨v, hv, hpv⟩ := (mem_region S p).mp hreg
  have hvw := cellInterior_owner_unique w v hp hpv
  exact hw (hvw ▸ hv)

/-- The entire exposed face also lies in the adjacent cell's closed box. -/
theorem closedSegment_subset_neighborBox (e : HalfEdge) :
    closedSegment e ⊆ cellBox (neighbor e.1 e.2) := by
  rintro p ⟨t, ht0, ht1, rfl⟩
  rcases e with ⟨v, d⟩
  fin_cases d <;>
    simp only [segmentPoint_north, segmentPoint_east, segmentPoint_south, segmentPoint_west,
      GridCellBoundary.neighbor, north, east, south, west, cellBox, mem_ofPred_eq,
      Int.cast_add, Int.cast_sub, Int.cast_one]
  all_goals repeat' constructor
  all_goals linarith

/-- Every actual exposed face, including its endpoints, belongs to the frontier. -/
theorem closedSegment_subset_frontier {S : Finset Site} {e : HalfEdge} (he : e ∈ boundary S) :
    closedSegment e ⊆ frontier (region S) := by
  intro p hp
  have howner : p ∈ region S :=
    cellBox_subset_region (boundary_owner_mem he) (closedSegment_subset_cellBox e hp)
  have hneighbor : p ∈ closure (cellInterior (neighbor e.1 e.2)) := by
    rw [closure_cellInterior]
    exact closedSegment_subset_neighborBox e hp
  rw [frontier_eq_closure_inter_closure]
  exact ⟨subset_closure howner,
    closure_mono (cellInterior_subset_compl_region (boundary_neighbor_not_mem he)) hneighbor⟩

theorem boundarySegments_subset_frontier (S : Finset Site) :
    (⋃ e ∈ boundary S, closedSegment e) ⊆ frontier (region S) := by
  intro p hp
  obtain ⟨e, he, hp⟩ := (show (p ∈ ⋃ e ∈ boundary S, closedSegment e) ↔
    ∃ e ∈ boundary S, p ∈ closedSegment e by simp only [mem_iUnion, exists_prop]).mp hp
  exact closedSegment_subset_frontier he hp

theorem boundary_source_mem_frontier {S : Finset Site} {e : HalfEdge} (he : e ∈ boundary S) :
    realSite (source e) ∈ frontier (region S) :=
  closedSegment_subset_frontier he (source_mem_closedSegment e)

theorem boundary_target_mem_frontier {S : Finset Site} {e : HalfEdge} (he : e ∈ boundary S) :
    realSite (target e) ∈ frontier (region S) :=
  closedSegment_subset_frontier he (target_mem_closedSegment e)

end MathResearchAnalysis.GridCellRegion

