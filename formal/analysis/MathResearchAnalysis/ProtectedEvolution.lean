module
public import MathResearchAnalysis.ProtectedDeathConnectivity
public import MathResearchAnalysis.DropletDomainComparison
set_option autoImplicit false
/-! Actual modified trajectories preserve discrete convexity, occupied connectivity,
and cleanup stability up to and including the first loss of the protected set.
These event-index statements do not identify the full original geometric Good
predicate and do not assert physical stopping laws or probability tails. -/
@[expose] public section
namespace MathResearchAnalysis.ProtectedEvolution
open GridCellBoundary (Site)
open OrthogonalGridConvexity
open ClippedDiamondGeometry (clippedDomain)
open ClippedProtectedGeometry (innerDiamond protectedSites)
open DropletModifiedWord (modifiedStep modifiedWord Stable Event)
open DropletDomainComparison (modifiedTrajectory exitTime stoppedTrajectory)

/-- Independently checkable discrete properties, not a redefinition of geometric Good. -/
def Shape (S : Finset Site) : Prop :=
  RowConvex S ∧ ColumnConvex S ∧ FourConnected S ∧ Stable S

theorem clipped_shape {L : Nat} (hL : 1 ≤ L) : Shape (clippedDomain L) :=
  ⟨clipped_rowConvex L,clipped_columnConvex L,clipped_fourConnected L,
    ClippedDiamondGeometry.clippedDomain_stable hL⟩

theorem actual_modifiedStep_shape {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} (hS : Shape S) (hD : innerDiamond L ⊆ S)
    (hclip : S ⊆ clippedDomain L) (v : Site) (tie : Bool) :
    Shape (modifiedStep (clippedDomain L) S v tie) ∧
      modifiedStep (clippedDomain L) S v tie ⊆ clippedDomain L := by
  obtain ⟨hr,hc,hconn,hst⟩ := hS
  have hthree : RowConvex (modifiedStep (clippedDomain L) S v tie) ∧
      ColumnConvex (modifiedStep (clippedDomain L) S v tie) ∧
      FourConnected (modifiedStep (clippedDomain L) S v tie) := by
    rcases ConvexLocalUpdate.modifiedStep_classification (clippedDomain L) v tie hr hc hst with h | h | h
    · rw [h]
      exact ⟨hr,hc,hconn⟩
    · obtain ⟨_,hv,hd,_,heq⟩ := h
      rw [heq,ConvexBirthUpdate.cleanup_insert_of_stable_degree_ge_two hst (by omega)]
      exact ⟨ConvexBirthUpdate.vacant_degree_two_insert_rowConvex hr hc hv hd,
        ConvexBirthUpdate.vacant_degree_two_insert_columnConvex hr hc hv hd,
        ConvexBirthUpdate.vacant_degree_two_insert_fourConnected hr hc hv hd hconn⟩
    · obtain ⟨_,hv,hd,_,heq⟩ := h
      rw [heq]
      have hcv := ProtectedColumnGeometry.protected_cleanup_erase_convexity hL hr hc hst hv hD hclip hd
      exact ⟨hcv.1,hcv.2,ProtectedDeathConnectivity.protected_cleanup_erase_fourConnected
        hL hr hc hst hv hconn hD hclip hd⟩
  exact ⟨⟨hthree.1,hthree.2.1,hthree.2.2,DropletModifiedWord.modifiedStep_stable _ hst v tie⟩,
    DropletModifiedWord.modifiedStep_supported hclip v tie⟩

theorem modifiedTrajectory_shape_of_history {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} (hS : Shape S) (hclip : S ⊆ clippedDomain L)
    (events : Nat → Event) (n : Nat)
    (hkeep : ∀ k < n, innerDiamond L ⊆ modifiedTrajectory (clippedDomain L) S events k) :
    Shape (modifiedTrajectory (clippedDomain L) S events n) ∧
      modifiedTrajectory (clippedDomain L) S events n ⊆ clippedDomain L := by
  induction n with
  | zero => simpa only [DropletDomainComparison.modifiedTrajectory_zero] using And.intro hS hclip
  | succ n ih =>
    have hpre := ih (fun k hk => hkeep k (by omega))
    rw [DropletDomainComparison.modifiedTrajectory_succ]
    exact actual_modifiedStep_shape hL hpre.1 (hkeep n (by omega)) hpre.2 (events n).1 (events n).2

theorem inner_preserved_before_exit {L : Nat} {S : Finset Site}
    (events : Nat → Event) {k n : Nat}
    (hn : (n : ℕ∞) ≤ exitTime (clippedDomain L) S (protectedSites L) events) (hk : k < n) :
    innerDiamond L ⊆ modifiedTrajectory (clippedDomain L) S events k := by
  have hi : protectedSites L ⊆ modifiedTrajectory (clippedDomain L) S events k := by
    by_contra h
    have he := (DropletDomainComparison.exitTime_le_nat_iff _ _ _ events k).mpr ⟨k,le_rfl,h⟩
    have hkn : (k : ℕ∞) < (n : ℕ∞) := ENat.natCast_lt_natCast.mpr hk
    exact (not_le_of_gt hkn) (le_trans hn he)
  exact Finset.Subset.trans (ClippedProtectedGeometry.innerDiamond_subset_protectedSites L) hi

theorem modifiedTrajectory_shape_upto_exit {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} (hS : Shape S) (hclip : S ⊆ clippedDomain L)
    (events : Nat → Event) (n : Nat)
    (hn : (n : ℕ∞) ≤ exitTime (clippedDomain L) S (protectedSites L) events) :
    Shape (modifiedTrajectory (clippedDomain L) S events n) ∧
      modifiedTrajectory (clippedDomain L) S events n ⊆ clippedDomain L :=
  modifiedTrajectory_shape_of_history hL hS hclip events n
    (fun _ hk => inner_preserved_before_exit events hn hk)

theorem stoppedTrajectory_shape {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} (hS : Shape S) (hclip : S ⊆ clippedDomain L)
    (events : Nat → Event) (n : Nat) :
    Shape (stoppedTrajectory (clippedDomain L) S (protectedSites L) events n) ∧
      stoppedTrajectory (clippedDomain L) S (protectedSites L) events n ⊆ clippedDomain L := by
  unfold stoppedTrajectory
  split
  · exact modifiedTrajectory_shape_upto_exit hL hS hclip events _ (ENat.natCast_toNat_le_self _)
  · rename_i h
    exact modifiedTrajectory_shape_upto_exit hL hS hclip events n (le_of_not_ge h)

theorem initial_stoppedTrajectory_shape {L : Nat} (hL : 2 ≤ L)
    (events : Nat → Event) (n : Nat) :
    Shape (stoppedTrajectory (clippedDomain L) (clippedDomain L) (protectedSites L) events n) ∧
      stoppedTrajectory (clippedDomain L) (clippedDomain L) (protectedSites L) events n ⊆ clippedDomain L :=
  stoppedTrajectory_shape hL (clipped_shape (by omega)) (Finset.Subset.refl _) events n

theorem initial_stoppedTrajectory_noCheckerboard {L : Nat} (hL : 2 ≤ L)
    (events : Nat → Event) (n : Nat) :
    GridBoundaryIncidence.NoCheckerboard
      (stoppedTrajectory (clippedDomain L) (clippedDomain L) (protectedSites L) events n) := by
  have h := (initial_stoppedTrajectory_shape hL events n).1
  exact rowConvex_fourConnected_noCheckerboard _ h.1 h.2.2.1

end MathResearchAnalysis.ProtectedEvolution
