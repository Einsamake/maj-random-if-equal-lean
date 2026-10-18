module
public import MathResearchAnalysis.OrthogonalVacantQuadrant
public import MathResearchAnalysis.ProtectedEvolution
set_option autoImplicit false
/-! Loss of the actual CMST protected set forces a genuine quadratic number of
vacant cells of the initial clipped domain. This is deterministic deleted area,
not a corner count, stochastic drift, physical stopping law or recovery tail. -/
@[expose] public section
namespace MathResearchAnalysis.ProtectedExitArea
open GridCellBoundary (Site)
open ClippedDiamondGeometry (clippedDomain directedBlock)
open ClippedProtectedGeometry (protectedSites)
open OrthogonalGridConvexity
open DropletModifiedWord (Event)
open DropletDomainComparison (exitTime stoppedTrajectory)

theorem exists_vacant_directedBlock {L : Nat} (hL : 40 ≤ L)
    {S : Finset Site} {x : Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hconn : FourConnected S) (hx : x ∈ protectedSites L) (hxs : x ∉ S) :
    ∃ horizontal vertical : Bool, directedBlock L x horizontal vertical ⊆ clippedDomain L \ S := by
  obtain ⟨horizontal,vertical,hq⟩ := OrthogonalVacantQuadrant.exists_empty_quadrant hr hc hconn hxs
  refine ⟨!horizontal,!vertical,?_⟩
  intro u hu
  refine Finset.mem_sdiff.mpr ⟨(ClippedProtectedGeometry.directedBlock_control hL hx _ _).1 hu,?_⟩
  intro hus
  apply hq u hus
  obtain ⟨p,rfl⟩ := (ClippedDiamondGeometry.mem_directedBlock L x u (!horizontal) (!vertical)).mp hu
  cases horizontal <;> cases vertical <;> dsimp [ClippedDiamondGeometry.reflect] <;>
    constructor <;> omega

theorem quadratic_vacant_area_of_protected_missing {L : Nat} (hL : 40 ≤ L)
    {S : Finset Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hconn : FourConnected S) (hmissing : ¬ protectedSites L ⊆ S) :
    (L : Real)^2 / 1600 ≤ ((clippedDomain L \ S).card : Real) := by
  have hex : ∃ x ∈ protectedSites L, x ∉ S := by
    by_contra h
    apply hmissing
    intro x hx
    by_contra hxs
    exact h ⟨x,hx,hxs⟩
  obtain ⟨x,hx,hxs⟩ := hex
  obtain ⟨horizontal,vertical,hblock⟩ := exists_vacant_directedBlock hL hr hc hconn hx hxs
  have hcR : ((directedBlock L x horizontal vertical).card : Real) ≤
      ((clippedDomain L \ S).card : Real) := by exact_mod_cast Finset.card_le_card hblock
  exact (ClippedDiamondGeometry.real_sq_div_le_directedBlock_card hL x horizontal vertical).trans hcR

theorem actual_stopped_exit_quadratic_vacant_area {L : Nat} (hL : 40 ≤ L)
    (events : Nat → Event) (j n : Nat)
    (hj : exitTime (clippedDomain L) (clippedDomain L) (protectedSites L) events = (j : ℕ∞))
    (hjn : j ≤ n) :
    (L : Real)^2 / 1600 ≤ ((clippedDomain L \
      stoppedTrajectory (clippedDomain L) (clippedDomain L) (protectedSites L) events n).card : Real) := by
  have hshape := (ProtectedEvolution.initial_stoppedTrajectory_shape (by omega : 2 ≤ L) events n).1
  exact quadratic_vacant_area_of_protected_missing hL hshape.1 hshape.2.1 hshape.2.2.1
    (DropletDomainComparison.stoppedTrajectory_inner_missing_after_exit _ _ _ events j n hj hjn)


theorem actual_stopped_area_after_exit {L : Nat} (hL : 40 ≤ L)
    (events : Nat → Event) (n : Nat)
    (hn : exitTime (clippedDomain L) (clippedDomain L) (protectedSites L) events ≤ (n : ℕ∞)) :
    (L : Real)^2 / 1600 ≤ ((clippedDomain L \
      stoppedTrajectory (clippedDomain L) (clippedDomain L) (protectedSites L) events n).card : Real) := by
  let tau := exitTime (clippedDomain L) (clippedDomain L) (protectedSites L) events
  have hfinite : tau ≠ ⊤ := by
    intro ht
    have hbad : (⊤ : ℕ∞) ≤ (n : ℕ∞) := by simpa only [← ht] using hn
    simp at hbad
  have heq : tau = (tau.toNat : ℕ∞) := (ENat.natCast_toNat hfinite).symm
  have hbound : (tau.toNat : ℕ∞) ≤ (n : ℕ∞) := (ENat.natCast_toNat_le_self tau).trans hn
  exact actual_stopped_exit_quadratic_vacant_area hL events tau.toNat n heq
    (ENat.natCast_le_natCast.mp hbound)

theorem actual_stopped_area_card_decrease {L : Nat} (hL : 40 ≤ L)
    (events : Nat → Event) (n : Nat)
    (hn : exitTime (clippedDomain L) (clippedDomain L) (protectedSites L) events ≤ (n : ℕ∞)) :
    (L : Real)^2 / 1600 ≤ ((clippedDomain L).card : Real) -
      ((stoppedTrajectory (clippedDomain L) (clippedDomain L) (protectedSites L) events n).card : Real) := by
  have harea := actual_stopped_area_after_exit hL events n hn
  have hsub := (ProtectedEvolution.initial_stoppedTrajectory_shape (by omega : 2 ≤ L) events n).2
  rw [Finset.card_sdiff_of_subset hsub,Nat.cast_sub (Finset.card_le_card hsub)] at harea
  exact harea

end MathResearchAnalysis.ProtectedExitArea
