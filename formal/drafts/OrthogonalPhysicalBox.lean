module
public import MathResearchAnalysis.OrthogonalPerimeter
public import MathResearchAnalysis.GridPhysicalRegion
set_option autoImplicit false
/-! Actual minimum rectangle for arbitrary nonempty finite unit-cell regions,
and its perimeter for connected orthogonally convex sets. Standalone draft. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.OrthogonalPhysicalBox
open GridCellBoundary (Site HalfEdge boundary perimeter)
open GridBoundarySegments (Plane realSite)
open InfiniteGridModel (north east south west)
open GridPhysicalRegion
open OrthogonalGridConvexity

def minX (S : Finset Site) (hne : S.Nonempty) : Int := (S.image Prod.fst).min' (hne.image Prod.fst)
def maxX (S : Finset Site) (hne : S.Nonempty) : Int := (S.image Prod.fst).max' (hne.image Prod.fst)
def minY (S : Finset Site) (hne : S.Nonempty) : Int := (S.image Prod.snd).min' (hne.image Prod.snd)
def maxY (S : Finset Site) (hne : S.Nonempty) : Int := (S.image Prod.snd).max' (hne.image Prod.snd)

def box (S : Finset Site) (hne : S.Nonempty) : Set Plane :=
  Set.Icc ((minX S hne : Real)-1/2) ((maxX S hne : Real)+1/2) ×ˢ
    Set.Icc ((minY S hne : Real)-1/2) ((maxY S hne : Real)+1/2)

theorem coordinate_bounds {S : Finset Site} (hne : S.Nonempty) {v : Site} (hv : v ∈ S) :
    minX S hne ≤ v.1 ∧ v.1 ≤ maxX S hne ∧ minY S hne ≤ v.2 ∧ v.2 ≤ maxY S hne :=
  ⟨Finset.min'_le _ _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩),
   Finset.le_max' _ _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩),
   Finset.min'_le _ _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩),
   Finset.le_max' _ _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)⟩

theorem unitRegion_subset_box {S : Finset Site} (hne : S.Nonempty) : unitRegion S ⊆ box S hne := by
  intro p hp
  obtain ⟨v,hv,hcell⟩ := (mem_unitRegion S p).mp hp
  obtain ⟨hxlo,hxhi,hylo,hyhi⟩ := coordinate_bounds hne hv
  have hxrlo : (minX S hne : Real) ≤ (v.1 : Real) := by exact_mod_cast hxlo
  have hxrhi : (v.1 : Real) ≤ (maxX S hne : Real) := by exact_mod_cast hxhi
  have hyrlo : (minY S hne : Real) ≤ (v.2 : Real) := by exact_mod_cast hylo
  have hyrhi : (v.2 : Real) ≤ (maxY S hne : Real) := by exact_mod_cast hyhi
  rcases hcell with ⟨ha,hb,hc,hd⟩
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

theorem frontier_subset_box {S : Finset Site} (hne : S.Nonempty) :
    frontier (unitRegion S) ⊆ box S hne :=
  (isClosed_unitRegion S).frontier_subset.trans (unitRegion_subset_box hne)

theorem right_frontier_witness {S : Finset Site} (hne : S.Nonempty) :
    ∃ p ∈ frontier (unitRegion S), p.1 = (maxX S hne : Real)+1/2 := by
  obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp (Finset.max'_mem (S.image Prod.fst) (hne.image Prod.fst))
  have hdir : east v ∉ S := by
    intro hd
    have hbound := Finset.le_max' (S.image Prod.fst) (east v).1 (Finset.mem_image.mpr ⟨_,hd,rfl⟩)
    rw [← heq] at hbound
    dsimp [east] at hbound
    omega
  have he : (v,1) ∈ boundary S := (GridCellBoundary.mem_boundary_east S v).mpr ⟨hv,hdir⟩
  refine ⟨physicalSource (v,1),unitClosedSegment_subset_frontier he (physicalSource_mem_unitClosedSegment _),?_⟩
  change ((GridCellBoundary.source (v,(1 : GridCellBoundary.Direction))).1 : Real)/2 = (maxX S hne : Real)+1/2
  norm_num [GridCellBoundary.source]
  push_cast
  change ((2*(v.1 : Real)+1)/2) = (maxX S hne : Real)+1/2
  have heqr : (v.1 : Real) = (maxX S hne : Real) := by exact_mod_cast heq
  rw [heqr]
  ring

theorem left_frontier_witness {S : Finset Site} (hne : S.Nonempty) :
    ∃ p ∈ frontier (unitRegion S), p.1 = (minX S hne : Real)-1/2 := by
  obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp (Finset.min'_mem (S.image Prod.fst) (hne.image Prod.fst))
  have hdir : west v ∉ S := by
    intro hd
    have hbound := Finset.min'_le (S.image Prod.fst) (west v).1 (Finset.mem_image.mpr ⟨_,hd,rfl⟩)
    rw [← heq] at hbound
    dsimp [west] at hbound
    omega
  have he : (v,3) ∈ boundary S := (GridCellBoundary.mem_boundary_west S v).mpr ⟨hv,hdir⟩
  refine ⟨physicalSource (v,3),unitClosedSegment_subset_frontier he (physicalSource_mem_unitClosedSegment _),?_⟩
  change ((GridCellBoundary.source (v,(3 : GridCellBoundary.Direction))).1 : Real)/2 = (minX S hne : Real)-1/2
  norm_num [GridCellBoundary.source]
  push_cast
  change ((2*(v.1 : Real)-1)/2) = (minX S hne : Real)-1/2
  have heqr : (v.1 : Real) = (minX S hne : Real) := by exact_mod_cast heq
  rw [heqr]
  ring

theorem upper_frontier_witness {S : Finset Site} (hne : S.Nonempty) :
    ∃ p ∈ frontier (unitRegion S), p.2 = (maxY S hne : Real)+1/2 := by
  obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp (Finset.max'_mem (S.image Prod.snd) (hne.image Prod.snd))
  have hdir : north v ∉ S := by
    intro hd
    have hbound := Finset.le_max' (S.image Prod.snd) (north v).2 (Finset.mem_image.mpr ⟨_,hd,rfl⟩)
    rw [← heq] at hbound
    dsimp [north] at hbound
    omega
  have he : (v,0) ∈ boundary S := (GridCellBoundary.mem_boundary_north S v).mpr ⟨hv,hdir⟩
  refine ⟨physicalSource (v,0),unitClosedSegment_subset_frontier he (physicalSource_mem_unitClosedSegment _),?_⟩
  change ((GridCellBoundary.source (v,(0 : GridCellBoundary.Direction))).2 : Real)/2 = (maxY S hne : Real)+1/2
  norm_num [GridCellBoundary.source]
  push_cast
  change ((2*(v.2 : Real)+1)/2) = (maxY S hne : Real)+1/2
  have heqr : (v.2 : Real) = (maxY S hne : Real) := by exact_mod_cast heq
  rw [heqr]
  ring

theorem lower_frontier_witness {S : Finset Site} (hne : S.Nonempty) :
    ∃ p ∈ frontier (unitRegion S), p.2 = (minY S hne : Real)-1/2 := by
  obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp (Finset.min'_mem (S.image Prod.snd) (hne.image Prod.snd))
  have hdir : south v ∉ S := by
    intro hd
    have hbound := Finset.min'_le (S.image Prod.snd) (south v).2 (Finset.mem_image.mpr ⟨_,hd,rfl⟩)
    rw [← heq] at hbound
    dsimp [south] at hbound
    omega
  have he : (v,2) ∈ boundary S := (GridCellBoundary.mem_boundary_south S v).mpr ⟨hv,hdir⟩
  refine ⟨physicalSource (v,2),unitClosedSegment_subset_frontier he (physicalSource_mem_unitClosedSegment _),?_⟩
  change ((GridCellBoundary.source (v,(2 : GridCellBoundary.Direction))).2 : Real)/2 = (minY S hne : Real)-1/2
  norm_num [GridCellBoundary.source]
  push_cast
  change ((2*(v.2 : Real)-1)/2) = (minY S hne : Real)-1/2
  have heqr : (v.2 : Real) = (minY S hne : Real) := by exact_mod_cast heq
  rw [heqr]
  ring

theorem box_minimal_for_frontier {S : Finset Site} (hne : S.Nonempty)
    {a b c d : Real} (hrect : frontier (unitRegion S) ⊆ Set.Icc a b ×ˢ Set.Icc c d) :
    box S hne ⊆ Set.Icc a b ×ˢ Set.Icc c d := by
  obtain ⟨pr,hpr,hr⟩ := right_frontier_witness hne
  obtain ⟨pl,hpl,hl⟩ := left_frontier_witness hne
  obtain ⟨pu,hpu,hu⟩ := upper_frontier_witness hne
  obtain ⟨pd,hpd,hd⟩ := lower_frontier_witness hne
  have hrb : (maxX S hne : Real)+1/2 ≤ b := by simpa only [← hr] using (hrect hpr).1.2
  have hla : a ≤ (minX S hne : Real)-1/2 := by simpa only [← hl] using (hrect hpl).1.1
  have hud : (maxY S hne : Real)+1/2 ≤ d := by simpa only [← hu] using (hrect hpu).2.2
  have hdc : c ≤ (minY S hne : Real)-1/2 := by simpa only [← hd] using (hrect hpd).2.1
  intro p hp
  exact ⟨⟨hla.trans hp.1.1,hp.1.2.trans hrb⟩,⟨hdc.trans hp.2.1,hp.2.2.trans hud⟩⟩

theorem box_minimal_for_region {S : Finset Site} (hne : S.Nonempty)
    {a b c d : Real} (hrect : unitRegion S ⊆ Set.Icc a b ×ˢ Set.Icc c d) :
    box S hne ⊆ Set.Icc a b ×ˢ Set.Icc c d :=
  box_minimal_for_frontier hne ((isClosed_unitRegion S).frontier_subset.trans hrect)

theorem nat_span_real (a b : Int) (h : a ≤ b) :
    ((b+1-a).toNat : Real) = (b : Real)+1-(a : Real) := by
  have hi := Int.toNat_of_nonneg (by omega : 0 ≤ b+1-a)
  exact_mod_cast hi

/-- Facet count equals the perimeter of the actual minimum unit-scale rectangle.
This statement does not assert a continuous boundary parametrization or arc length. -/
theorem perimeter_eq_minimum_rectangle {S : Finset Site} (hne : S.Nonempty)
    (hr : RowConvex S) (hc : ColumnConvex S) (hconn : FourConnected S) :
    (perimeter S : Real) = 2 *
      (((maxX S hne : Real)+1/2-((minX S hne : Real)-1/2)) +
       ((maxY S hne : Real)+1/2-((minY S hne : Real)-1/2))) := by
  have hxmin : minX S hne ≤ maxX S hne :=
    Finset.min'_le _ _ (Finset.max'_mem (S.image Prod.fst) (hne.image Prod.fst))
  have hymin : minY S hne ≤ maxY S hne :=
    Finset.min'_le _ _ (Finset.max'_mem (S.image Prod.snd) (hne.image Prod.snd))
  have hPi : (perimeter S : Real) = 2 *
      (((maxX S hne + 1 - minX S hne).toNat : Real) +
       ((maxY S hne + 1 - minY S hne).toNat : Real)) := by
    exact_mod_cast OrthogonalPerimeter.perimeter_eq_integer_spans hr hc hconn hne
  rw [nat_span_real _ _ hxmin,nat_span_real _ _ hymin] at hPi
  linarith

end MathResearchAnalysis.OrthogonalPhysicalBox
#print axioms MathResearchAnalysis.OrthogonalPhysicalBox.minX
#print axioms MathResearchAnalysis.OrthogonalPhysicalBox.maxX
#print axioms MathResearchAnalysis.OrthogonalPhysicalBox.minY
#print axioms MathResearchAnalysis.OrthogonalPhysicalBox.maxY
#print axioms MathResearchAnalysis.OrthogonalPhysicalBox.box
#print axioms MathResearchAnalysis.OrthogonalPhysicalBox.coordinate_bounds
#print axioms MathResearchAnalysis.OrthogonalPhysicalBox.unitRegion_subset_box
#print axioms MathResearchAnalysis.OrthogonalPhysicalBox.frontier_subset_box
#print axioms MathResearchAnalysis.OrthogonalPhysicalBox.right_frontier_witness
#print axioms MathResearchAnalysis.OrthogonalPhysicalBox.left_frontier_witness
#print axioms MathResearchAnalysis.OrthogonalPhysicalBox.upper_frontier_witness
#print axioms MathResearchAnalysis.OrthogonalPhysicalBox.lower_frontier_witness
#print axioms MathResearchAnalysis.OrthogonalPhysicalBox.box_minimal_for_frontier
#print axioms MathResearchAnalysis.OrthogonalPhysicalBox.box_minimal_for_region
#print axioms MathResearchAnalysis.OrthogonalPhysicalBox.nat_span_real
#print axioms MathResearchAnalysis.OrthogonalPhysicalBox.perimeter_eq_minimum_rectangle
