module

public import MathResearchAnalysis.GridRegionBoundary
public import MathResearchAnalysis.GridPhysicalRegion
public import MathResearchAnalysis.ClippedPhysicalBox
public import MathResearchAnalysis.GridContourLength
public import MathResearchAnalysis.ClippedProtectedGeometry

set_option autoImplicit false

/-!
# The actual clipped initial configuration satisfies the geometric Good conditions

The curve covers the full topological frontier of the actual unit-square union.
Simplicity is injectivity on the half-open parameter interval, with equal
endpoints. Length is the genuine Euclidean extended variation, not a chosen
partition sum or the maximum metric of a product. The rectangle is proved
minimal for the full actual region, and the inner diamond and cleanup are the
previously constructed model objects. No Good-preservation or exit-area result
is asserted here.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.ClippedInitialContour

open GridCellBoundary GridBoundarySegments ClippedBoundaryCycle ClippedBoundaryPolygon
open ClippedBoundaryCurve GridPhysicalRegion GridContourLength

/-- The proved actual polygonal boundary is the entire actual region frontier. -/
theorem polygon_boundary_eq_frontier (L : Nat) (hL : 1 ≤ L) :
    (polygon L).boundary Real =
      frontier (GridCellRegion.region (ClippedDiamondGeometry.clippedDomain L)) := by
  ext p
  rw [ClippedBoundaryPolygon.mem_boundary_iff L hL,
    GridRegionBoundary.mem_frontier_region_iff]

def physicalTrace (L : Nat) (t : Real) : Plane := halfScale (trace L (8 * L + 4) t)

def physicalCurve (L : Nat) (t : Real) : Plane := halfScale (curve L t)

def euclideanPoint (p : Plane) : EuclideanPlane := !₂[p.1, p.2]

theorem continuous_physicalTrace (L : Nat) : Continuous (physicalTrace L) :=
  halfScale.continuous.comp (continuous_trace L _)

theorem physicalTrace_closed (L : Nat) (hL : 1 ≤ L) :
    physicalTrace L ((8 * L + 4 : Nat) : Real) = physicalTrace L 0 :=
  congrArg halfScale (trace_closed L hL)

theorem physicalTrace_injective_Ico (L : Nat) (hL : 1 ≤ L) :
    Set.InjOn (physicalTrace L) (Set.Ico 0 ((8 * L + 4 : Nat) : Real)) := by
  intro t ht s hs h
  exact trace_injective_Ico L hL ht hs (halfScale.injective h)

theorem physicalTrace_image (L : Nat) (hL : 1 ≤ L) :
    physicalTrace L '' Set.Icc 0 ((8 * L + 4 : Nat) : Real) =
      frontier (unitRegion (ClippedDiamondGeometry.clippedDomain L)) := by
  calc
    _ = halfScale '' (trace L (8 * L + 4) '' Set.Icc 0 ((8 * L + 4 : Nat) : Real)) :=
      (Set.image_image _ _ _).symm
    _ = _ := by rw [trace_image L hL, polygon_boundary_eq_frontier L hL, halfScale_frontier_region]

theorem continuous_physicalCurve (L : Nat) : Continuous (physicalCurve L) :=
  halfScale.continuous.comp (continuous_curve L)

theorem physicalCurve_closed (L : Nat) (hL : 1 ≤ L) : physicalCurve L 1 = physicalCurve L 0 :=
  congrArg halfScale (curve_closed L hL)

theorem physicalCurve_injective_Ico (L : Nat) (hL : 1 ≤ L) :
    Set.InjOn (physicalCurve L) (Set.Ico 0 1) := by
  intro t ht s hs h
  exact curve_injective_Ico L hL ht hs (halfScale.injective h)

theorem physicalCurve_image (L : Nat) (hL : 1 ≤ L) :
    physicalCurve L '' Set.Icc 0 1 = frontier (unitRegion (ClippedDiamondGeometry.clippedDomain L)) := by
  calc
    _ = halfScale '' (curve L '' Set.Icc 0 1) := (Set.image_image _ _ _).symm
    _ = _ := by rw [curve_image L hL, polygon_boundary_eq_frontier L hL, halfScale_frontier_region]

theorem euclidean_physicalTrace (L : Nat) :
    (fun t => euclideanPoint (physicalTrace L t)) = unitTrace L (8 * L + 4) := rfl

theorem physicalTrace_length (L : Nat) :
    eVariationOn (fun t => euclideanPoint (physicalTrace L t))
      (Set.Icc 0 ((8 * L + 4 : Nat) : Real)) = (8 * L + 4 : Nat) := by
  rw [euclidean_physicalTrace]
  exact unitTrace_length L

theorem physicalTrace_length_eq_minimum_rectangle (L : Nat) :
    eVariationOn (fun t => euclideanPoint (physicalTrace L t))
      (Set.Icc 0 ((8 * L + 4 : Nat) : Real)) =
      ENNReal.ofReal (2 * ((ClippedPhysicalBox.physicalExtent L -
        (-(ClippedPhysicalBox.physicalExtent L))) +
        (ClippedPhysicalBox.physicalExtent L - (-(ClippedPhysicalBox.physicalExtent L))))) := by
  rw [physicalTrace_length, ClippedPhysicalBox.rectangle_perimeter]
  have h : 8 * (L : Real) + 4 = ((8 * L + 4 : Nat) : Real) := by push_cast; ring
  rw [h, ENNReal.ofReal_natCast]

/-- The four actual geometric and cleanup conditions. No dynamic invariant,
corner count, drift or probabilistic estimate is stored in this predicate. -/
def GeometricGood (L : Nat) (S : Finset Site) : Prop :=
  S ⊆ ClippedDiamondGeometry.clippedDomain L ∧
  ClippedProtectedGeometry.innerDiamond L ⊆ S ∧ GridMajorityPeeling.cleanup S = S ∧
  ∃ a b c d : Real, a ≤ b ∧ c ≤ d ∧
    frontier (unitRegion S) ⊆ Set.Icc a b ×ˢ Set.Icc c d ∧
    (∀ a' b' c' d' : Real, frontier (unitRegion S) ⊆ Set.Icc a' b' ×ˢ Set.Icc c' d' →
      Set.Icc a b ×ˢ Set.Icc c d ⊆ Set.Icc a' b' ×ˢ Set.Icc c' d') ∧
    ∃ m : Real, 0 < m ∧ ∃ gamma : Real → Plane,
      ContinuousOn gamma (Set.Icc 0 m) ∧ gamma m = gamma 0 ∧
      Set.InjOn gamma (Set.Ico 0 m) ∧ gamma '' Set.Icc 0 m = frontier (unitRegion S) ∧
      eVariationOn (fun t => euclideanPoint (gamma t)) (Set.Icc 0 m) =
        ENNReal.ofReal (2 * ((b-a) + (d-c)))

theorem initial_geometricGood (L : Nat) (hL : 1 ≤ L) :
    GeometricGood L (ClippedDiamondGeometry.clippedDomain L) := by
  refine ⟨Finset.Subset.refl _,
    (ClippedProtectedGeometry.innerDiamond_subset_protectedSites L).trans
    (ClippedProtectedGeometry.protectedSites_subset_clippedDomain_of_pos hL),
    ClippedDiamondGeometry.cleanup_clippedDomain hL,
    -(ClippedPhysicalBox.physicalExtent L), ClippedPhysicalBox.physicalExtent L,
    -(ClippedPhysicalBox.physicalExtent L), ClippedPhysicalBox.physicalExtent L,
    ?_, ?_, ClippedPhysicalBox.frontier_subset_box L,
    ClippedPhysicalBox.minimum_frontier_rectangle L, ((8 * L + 4 : Nat) : Real),
    by positivity, physicalTrace L, (continuous_physicalTrace L).continuousOn,
    physicalTrace_closed L hL, physicalTrace_injective_Ico L hL,
    physicalTrace_image L hL, physicalTrace_length_eq_minimum_rectangle L⟩
  all_goals unfold ClippedPhysicalBox.physicalExtent ClippedRegionBox.extent
  all_goals linarith [Nat.cast_nonneg (α := Real) L]

end MathResearchAnalysis.ClippedInitialContour
