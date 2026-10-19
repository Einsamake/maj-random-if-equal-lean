module
public import MathResearchAnalysis.OrthogonalPhysicalContour
public import MathResearchAnalysis.ProtectedEvolution
set_option autoImplicit false
/-! The proved discrete Shape implies the existing original GeometricGood predicate when the actual support and inner diamond are retained. Genuine event trajectories satisfy it strictly before protected exit; no physical stopping law or probability tail is asserted. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.ProtectedGeometricGood
open GridCellBoundary (Site perimeter)
open OrthogonalGridConvexity OrthogonalPhysicalBox OrthogonalPhysicalContour
open ClippedInitialContour (GeometricGood euclideanPoint)
open ClippedDiamondGeometry (clippedDomain)
open ClippedProtectedGeometry (innerDiamond protectedSites)
open DropletDomainComparison (modifiedTrajectory exitTime stoppedTrajectory)
open DropletModifiedWord (modifiedStep Event)
open ProtectedEvolution (Shape)

theorem geometricGood_of_shape {L : Nat} {S : Finset Site} (hS : Shape S)
    (hclip : S ⊆ clippedDomain L) (hD : innerDiamond L ⊆ S) : GeometricGood L S := by
  have hne : S.Nonempty := ⟨(0,0),hD (ClippedProtectedGeometry.zero_mem_innerDiamond L)⟩
  let R := OrthogonalBoundaryCycle.ofOrthogonal S hS.1 hS.2.1 hS.2.2.1 hne
  have hclean : GridMajorityPeeling.cleanup S = S :=
    FiniteMajorityPeeling.core_eq_self GridMajorityPeeling.neighbors4 hS.2.2.2
  have hxmin : minX S hne ≤ maxX S hne :=
    Finset.min'_le _ _ (Finset.max'_mem (S.image Prod.fst) (hne.image Prod.fst))
  have hymin : minY S hne ≤ maxY S hne :=
    Finset.min'_le _ _ (Finset.max'_mem (S.image Prod.snd) (hne.image Prod.snd))
  refine ⟨hclip,hD,hclean,(minX S hne : Real)-1/2,(maxX S hne : Real)+1/2,
    (minY S hne : Real)-1/2,(maxY S hne : Real)+1/2,?_,?_,frontier_subset_box hne,
    ?_,(perimeter S : Real),?_,physicalTrace R,(continuous_physicalTrace R).continuousOn,
    physicalTrace_closed R,physicalTrace_injective_Ico R,physicalTrace_image R,
    physicalTrace_length_eq_minimum_rectangle R hS.1⟩
  · have h : (minX S hne : Real) ≤ (maxX S hne : Real) := by exact_mod_cast hxmin
    linarith
  · have h : (minY S hne : Real) ≤ (maxY S hne : Real) := by exact_mod_cast hymin
    linarith
  · intro a b c d hrect
    exact box_minimal_for_frontier hne hrect
  · exact_mod_cast OrthogonalBoundaryCycle.perimeter_pos R

theorem actual_modifiedStep_geometricGood {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} (hS : Shape S) (hD : innerDiamond L ⊆ S) (hclip : S ⊆ clippedDomain L)
    (v : Site) (tie : Bool) (hD' : innerDiamond L ⊆ modifiedStep (clippedDomain L) S v tie) :
    GeometricGood L (modifiedStep (clippedDomain L) S v tie) := by
  have h := ProtectedEvolution.actual_modifiedStep_shape hL hS hD hclip v tie
  exact geometricGood_of_shape h.1 h.2 hD'

theorem protected_preserved_before_exit {L : Nat} {S : Finset Site}
    (events : Nat → Event) (n : Nat)
    (hn : (n : ℕ∞) < exitTime (clippedDomain L) S (protectedSites L) events) :
    protectedSites L ⊆ modifiedTrajectory (clippedDomain L) S events n := by
  by_contra h
  have he := (DropletDomainComparison.exitTime_le_nat_iff _ _ _ events n).mpr ⟨n,le_rfl,h⟩
  exact (not_le_of_gt hn) he

theorem modifiedTrajectory_geometricGood_before_exit {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} (hS : Shape S) (hclip : S ⊆ clippedDomain L)
    (events : Nat → Event) (n : Nat)
    (hn : (n : ℕ∞) < exitTime (clippedDomain L) S (protectedSites L) events) :
    GeometricGood L (modifiedTrajectory (clippedDomain L) S events n) := by
  have h := ProtectedEvolution.modifiedTrajectory_shape_upto_exit hL hS hclip events n hn.le
  exact geometricGood_of_shape h.1 h.2
    ((ClippedProtectedGeometry.innerDiamond_subset_protectedSites L).trans
      (protected_preserved_before_exit events n hn))

theorem stoppedTrajectory_geometricGood_before_exit {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} (hS : Shape S) (hclip : S ⊆ clippedDomain L)
    (events : Nat → Event) (n : Nat)
    (hn : (n : ℕ∞) < exitTime (clippedDomain L) S (protectedSites L) events) :
    GeometricGood L (stoppedTrajectory (clippedDomain L) S (protectedSites L) events n) := by
  rw [DropletDomainComparison.stoppedTrajectory_before_exit _ _ _ events n hn]
  exact modifiedTrajectory_geometricGood_before_exit hL hS hclip events n hn

theorem initial_stoppedTrajectory_geometricGood_before_exit {L : Nat} (hL : 2 ≤ L)
    (events : Nat → Event) (n : Nat)
    (hn : (n : ℕ∞) < exitTime (clippedDomain L) (clippedDomain L) (protectedSites L) events) :
    GeometricGood L (stoppedTrajectory (clippedDomain L) (clippedDomain L) (protectedSites L) events n) :=
  stoppedTrajectory_geometricGood_before_exit hL (ProtectedEvolution.clipped_shape (by omega))
    (Finset.Subset.refl _) events n hn
end MathResearchAnalysis.ProtectedGeometricGood
