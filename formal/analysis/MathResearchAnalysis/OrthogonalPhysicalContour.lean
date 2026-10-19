module
public import MathResearchAnalysis.OrthogonalContourLength
public import MathResearchAnalysis.OrthogonalPhysicalBox
public import MathResearchAnalysis.ClippedInitialContour
public import MathResearchAnalysis.GridRegionConnectivity
set_option autoImplicit false
/-! The entire actual physical frontier is a simple closed curve with its full Euclidean arc length. Discrete orthogonal shape conditions, and only those conditions, supply the geometry. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.OrthogonalPhysicalContour
open GridCellBoundary GridBoundarySegments OrthogonalBoundaryCycle OrthogonalBoundaryPolygon OrthogonalBoundaryCurve
open GridPhysicalRegion OrthogonalContourLength OrthogonalGridConvexity OrthogonalPhysicalBox
open ClippedInitialContour (euclideanPoint)

/-- The proved actual polygonal boundary is the entire actual region frontier. -/
theorem polygon_boundary_eq_frontier (R : Region)  :
    (polygon R).boundary Real =
      frontier (GridCellRegion.region R.val) := by
  ext p
  rw [OrthogonalBoundaryPolygon.mem_boundary_iff R,
    GridRegionBoundary.mem_frontier_region_iff]

def physicalTrace (R : Region) (t : Real) : Plane := halfScale (trace R (perimeter R.val) t)

def physicalCurve (R : Region) (t : Real) : Plane := halfScale (curve R t)

theorem continuous_physicalTrace (R : Region) : Continuous (physicalTrace R) :=
  halfScale.continuous.comp (continuous_trace R _)

theorem physicalTrace_closed (R : Region)  :
    physicalTrace R ((perimeter R.val : Nat) : Real) = physicalTrace R 0 :=
  congrArg halfScale (trace_closed R)

theorem physicalTrace_injective_Ico (R : Region)  :
    Set.InjOn (physicalTrace R) (Set.Ico 0 ((perimeter R.val : Nat) : Real)) := by
  intro t ht s hs h
  exact trace_injective_Ico R ht hs (halfScale.injective h)

theorem physicalTrace_image (R : Region)  :
    physicalTrace R '' Set.Icc 0 ((perimeter R.val : Nat) : Real) =
      frontier (unitRegion R.val) := by
  calc
    _ = halfScale '' (trace R (perimeter R.val) '' Set.Icc 0 ((perimeter R.val : Nat) : Real)) :=
      (Set.image_image _ _ _).symm
    _ = _ := by rw [trace_image R, polygon_boundary_eq_frontier R, halfScale_frontier_region]

theorem continuous_physicalCurve (R : Region) : Continuous (physicalCurve R) :=
  halfScale.continuous.comp (continuous_curve R)

theorem physicalCurve_closed (R : Region)  : physicalCurve R 1 = physicalCurve R 0 :=
  congrArg halfScale (curve_closed R)

theorem physicalCurve_injective_Ico (R : Region)  :
    Set.InjOn (physicalCurve R) (Set.Ico 0 1) := by
  intro t ht s hs h
  exact curve_injective_Ico R ht hs (halfScale.injective h)

theorem physicalCurve_image (R : Region)  :
    physicalCurve R '' Set.Icc 0 1 = frontier (unitRegion R.val) := by
  calc
    _ = halfScale '' (curve R '' Set.Icc 0 1) := (Set.image_image _ _ _).symm
    _ = _ := by rw [curve_image R, polygon_boundary_eq_frontier R, halfScale_frontier_region]

theorem euclidean_physicalTrace (R : Region) :
    (fun t => euclideanPoint (physicalTrace R t)) = unitTrace R (perimeter R.val) := rfl

theorem physicalTrace_length (R : Region) :
    eVariationOn (fun t => euclideanPoint (physicalTrace R t))
      (Set.Icc 0 ((perimeter R.val : Nat) : Real)) = (perimeter R.val : Nat) := by
  rw [euclidean_physicalTrace]
  exact unitTrace_length R


theorem physicalTrace_length_eq_minimum_rectangle (R : Region) (hr : RowConvex R.val) :
    eVariationOn (fun t => euclideanPoint (physicalTrace R t))
      (Set.Icc 0 ((perimeter R.val : Nat) : Real)) =
      ENNReal.ofReal (2 *
        (((maxX R.val R.property.2.2.2 : Real)+1/2-((minX R.val R.property.2.2.2 : Real)-1/2)) +
         ((maxY R.val R.property.2.2.2 : Real)+1/2-((minY R.val R.property.2.2.2 : Real)-1/2)))) := by
  rw [physicalTrace_length,← perimeter_eq_minimum_rectangle R.property.2.2.2 hr R.property.1 R.property.2.1,
    ENNReal.ofReal_natCast]

end MathResearchAnalysis.OrthogonalPhysicalContour
