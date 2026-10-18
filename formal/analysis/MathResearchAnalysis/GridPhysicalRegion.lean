module

public import MathResearchAnalysis.GridCellRegion
public import Mathlib.Topology.Homeomorph.Defs

set_option autoImplicit false

/-!
# Exact return to the original unit-cell geometry

The working cell boxes have side two. The explicit homeomorphism p |-> p/2
carries their actual finite union to the genuine unit squares centered at the
original lattice sites, and carries the actual frontier to its frontier.
Unit faces below retain the entire real affine segment, including endpoints.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.GridPhysicalRegion

open GridCellBoundary GridBoundarySegments GridCellRegion Set

def halfScale : Plane ≃ₜ Plane where
  toFun := fun p => (p.1 / 2, p.2 / 2)
  invFun := fun p => (2 * p.1, 2 * p.2)
  left_inv := fun p => by apply Prod.ext <;> dsimp <;> ring
  right_inv := fun p => by apply Prod.ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem halfScale_apply (p : Plane) : halfScale p = (p.1 / 2, p.2 / 2) := rfl

@[simp] theorem halfScale_symm_apply (p : Plane) : halfScale.symm p = (2*p.1, 2*p.2) := rfl

/-- The original closed unit square centered at the actual lattice site v. -/
def unitCell (v : Site) : Set Plane :=
  {p | (v.1 : Real) - 1/2 ≤ p.1 ∧ p.1 ≤ (v.1 : Real) + 1/2 ∧
    (v.2 : Real) - 1/2 ≤ p.2 ∧ p.2 ≤ (v.2 : Real) + 1/2}

def unitRegion (S : Finset Site) : Set Plane := ⋃ v ∈ S, unitCell v

theorem mem_unitRegion (S : Finset Site) (p : Plane) :
    p ∈ unitRegion S ↔ ∃ v ∈ S, p ∈ unitCell v := by
  simp only [unitRegion, mem_iUnion, exists_prop]

theorem unitCell_eq_prod (v : Site) :
    unitCell v = Icc ((v.1 : Real)-1/2) ((v.1 : Real)+1/2) ×ˢ
      Icc ((v.2 : Real)-1/2) ((v.2 : Real)+1/2) := by
  ext p
  simp only [unitCell, mem_ofPred_eq, mem_prod, mem_Icc]
  tauto

theorem halfScale_mem_unitCell_iff (v : Site) (p : Plane) :
    halfScale p ∈ unitCell v ↔ p ∈ cellBox v := by
  change ((v.1 : Real)-1/2 ≤ p.1/2 ∧ p.1/2 ≤ (v.1 : Real)+1/2 ∧
    (v.2 : Real)-1/2 ≤ p.2/2 ∧ p.2/2 ≤ (v.2 : Real)+1/2) ↔
    (2*(v.1 : Real)-1 ≤ p.1 ∧ p.1 ≤ 2*(v.1 : Real)+1 ∧
      2*(v.2 : Real)-1 ≤ p.2 ∧ p.2 ≤ 2*(v.2 : Real)+1)
  constructor <;> rintro ⟨hx0,hx1,hy0,hy1⟩
  all_goals repeat' constructor
  all_goals linarith

theorem halfScale_image_cellBox (v : Site) : halfScale '' cellBox v = unitCell v := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact (halfScale_mem_unitCell_iff v q).mpr hq
  · intro hp
    refine ⟨halfScale.symm p, ?_, halfScale.apply_symm_apply p⟩
    apply (halfScale_mem_unitCell_iff v _).mp
    simpa only [halfScale.apply_symm_apply] using hp

theorem halfScale_image_region (S : Finset Site) : halfScale '' region S = unitRegion S := by
  simp only [region, unitRegion, Set.image_iUnion, halfScale_image_cellBox]

theorem halfScale_frontier_region (S : Finset Site) :
    halfScale '' frontier (region S) = frontier (unitRegion S) := by
  rw [halfScale.image_frontier, halfScale_image_region]

theorem isCompact_unitRegion (S : Finset Site) : IsCompact (unitRegion S) := by
  rw [← halfScale_image_region]
  exact (isCompact_region S).image halfScale.continuous

theorem isClosed_unitRegion (S : Finset Site) : IsClosed (unitRegion S) :=
  (isCompact_unitRegion S).isClosed

@[simp] theorem unitRegion_empty : unitRegion ∅ = ∅ := by simp [unitRegion]

def physicalSource (e : HalfEdge) : Plane := halfScale (realSite (source e))

def physicalTarget (e : HalfEdge) : Plane := halfScale (realSite (target e))

def unitSegmentPoint (e : HalfEdge) (t : Real) : Plane :=
  ((1-t) * (physicalSource e).1 + t * (physicalTarget e).1,
    (1-t) * (physicalSource e).2 + t * (physicalTarget e).2)

def unitClosedSegment (e : HalfEdge) : Set Plane :=
  {p | ∃ t : Real, 0 ≤ t ∧ t ≤ 1 ∧ p = unitSegmentPoint e t}

theorem halfScale_segmentPoint (e : HalfEdge) (t : Real) :
    halfScale (segmentPoint e t) = unitSegmentPoint e t := by
  rw [segmentPoint_convex]
  apply Prod.ext <;>
    dsimp [halfScale, unitSegmentPoint, physicalSource, physicalTarget] <;> ring

theorem halfScale_image_closedSegment (e : HalfEdge) :
    halfScale '' closedSegment e = unitClosedSegment e := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨t,ht0,ht1,rfl⟩ := hq
    exact ⟨t,ht0,ht1,halfScale_segmentPoint e t⟩
  · rintro ⟨t,ht0,ht1,rfl⟩
    exact ⟨segmentPoint e t, ⟨t,ht0,ht1,rfl⟩, halfScale_segmentPoint e t⟩

theorem unitClosedSegment_subset_frontier {S : Finset Site} {e : HalfEdge}
    (he : e ∈ boundary S) : unitClosedSegment e ⊆ frontier (unitRegion S) := by
  intro p hp
  rw [← halfScale_image_closedSegment] at hp
  obtain ⟨q,hq,rfl⟩ := hp
  rw [← halfScale_frontier_region]
  exact ⟨q,closedSegment_subset_frontier he hq,rfl⟩

theorem physicalSource_ne_target (e : HalfEdge) : physicalSource e ≠ physicalTarget e := by
  intro h
  exact source_ne_target e (realSite_injective (halfScale.injective h))

theorem physicalSource_mem_unitClosedSegment (e : HalfEdge) :
    physicalSource e ∈ unitClosedSegment e := by
  rw [← halfScale_image_closedSegment]
  exact ⟨realSite (source e), source_mem_closedSegment e, rfl⟩

theorem physicalTarget_mem_unitClosedSegment (e : HalfEdge) :
    physicalTarget e ∈ unitClosedSegment e := by
  rw [← halfScale_image_closedSegment]
  exact ⟨realSite (target e), target_mem_closedSegment e, rfl⟩

theorem halfScale_image_boundarySegments (S : Finset Site) :
    halfScale '' (⋃ e ∈ boundary S, closedSegment e) =
      ⋃ e ∈ boundary S, unitClosedSegment e := by
  simp only [Set.image_iUnion, halfScale_image_closedSegment]

/-- The actual unit face has coordinate length one in the original scale. -/
theorem unit_edge_length (e : HalfEdge) :
    |(physicalTarget e).1 - (physicalSource e).1| +
      |(physicalTarget e).2 - (physicalSource e).2| = 1 := by
  have hi := GridCellBoundary.scaled_edge_length e
  have hr : |((target e).1 : Real) - ((source e).1 : Real)| +
      |((target e).2 : Real) - ((source e).2 : Real)| = 2 := by exact_mod_cast hi
  change |((target e).1 : Real)/2 - ((source e).1 : Real)/2| +
    |((target e).2 : Real)/2 - ((source e).2 : Real)/2| = 1
  rw [← sub_div, ← sub_div, abs_div, abs_div]
  norm_num
  linarith
end MathResearchAnalysis.GridPhysicalRegion

