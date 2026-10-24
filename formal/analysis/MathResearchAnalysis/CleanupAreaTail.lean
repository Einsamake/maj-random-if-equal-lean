module
public import MathResearchAnalysis.PhysicalAreaTail
public import MathResearchAnalysis.CumulativeCleanupBudget
set_option autoImplicit false
/-! The true cumulative cleanup term is eliminated from the actual clipped
area/tail bound using the proved physical perimeter budget. The remaining
masked raw integral is kept explicitly; no quadratic drift bound is assumed. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.CleanupAreaTail
open MeasureTheory
open DropletClockLaw (Sample)
open PhysicalAreaTail (law missingArea exitEvent)

def rawRate (L : Nat) (p : NNReal × Sample L) : Real :=
  if ClippedProtectedGeometry.protectedSites L ⊆ ObservedPreState.beforeState L
    (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
    (ClippedDiamondGeometry.clippedDomain L) p.1 p.2
  then MaskedAreaGenerator.rawAreaRate (ClippedDiamondGeometry.clippedDomain L)
    (ObservedPreState.beforeState L (ClippedDiamondGeometry.clippedDomain L)
      (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L) p.1 p.2)
  else 0

def cleanupRate (L : Nat) (p : NNReal × Sample L) : Real :=
  CumulativeCleanupBudget.rate (ClippedDiamondGeometry.clippedDomain L)
    (ClippedProtectedGeometry.protectedSites L)
    (ObservedPreState.beforeState L (ClippedDiamondGeometry.clippedDomain L)
      (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L) p.1 p.2)

theorem rate_eq_raw_add_cleanup (L : Nat) (p : NNReal × Sample L) :
    PhysicalAreaTail.rate L p = rawRate L p + cleanupRate L p := by
  unfold PhysicalAreaTail.rate rawRate cleanupRate CumulativeCleanupBudget.rate
  rw [PhysicalAreaGenerator.actual_clipped_generator_raw_cleanup]
  split_ifs <;> ring

theorem rawRate_sample_integrable (L : Nat) (hL : 1 ≤ L) (u : NNReal) :
    Integrable (fun z : Sample L => rawRate L (u,z)) (law L) := by
  have ht := PhysicalAreaGenerator.generator_sample_integrable L
    (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
    (ClippedDiamondGeometry.clippedDomain L)
    (ClippedSquareCoordinates.clippedDomain_subset_centeredSites L hL) u
  have hc := CumulativeCleanupBudget.rate_sample_integrable L
    (I := ClippedProtectedGeometry.protectedSites L)
    (S := ClippedDiamondGeometry.clippedDomain L) (Finset.Subset.refl _)
    (ClippedSquareCoordinates.clippedDomain_subset_centeredSites L hL) u
  apply (ht.sub hc).congr
  exact Filter.Eventually.of_forall (fun z => by
    change PhysicalAreaTail.rate L (u,z) - cleanupRate L (u,z) = _
    rw [rate_eq_raw_add_cleanup]
    ring)

theorem expected_raw_eq_sub (L : Nat) (hL : 1 ≤ L) (u : NNReal) :
    (∫ z : Sample L, rawRate L (u,z) ∂law L) =
      (∫ z : Sample L, PhysicalAreaTail.rate L (u,z) ∂law L) -
      (∫ z : Sample L, cleanupRate L (u,z) ∂law L) := by
  have ht : Integrable (fun z : Sample L => PhysicalAreaTail.rate L (u,z)) (law L) :=
    PhysicalAreaGenerator.generator_sample_integrable L
      (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
      (ClippedDiamondGeometry.clippedDomain L)
      (ClippedSquareCoordinates.clippedDomain_subset_centeredSites L hL) u
  have hc : Integrable (fun z : Sample L => cleanupRate L (u,z)) (law L) :=
    CumulativeCleanupBudget.rate_sample_integrable L
      (I := ClippedProtectedGeometry.protectedSites L)
      (S := ClippedDiamondGeometry.clippedDomain L) (Finset.Subset.refl _)
      (ClippedSquareCoordinates.clippedDomain_subset_centeredSites L hL) u
  rw [← integral_sub ht hc]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun z => by
    change rawRate L (u,z) = PhysicalAreaTail.rate L (u,z) - cleanupRate L (u,z)
    rw [rate_eq_raw_add_cleanup]
    ring))

theorem rawRate_time_mean_integrable (L : Nat) (hL : 1 ≤ L) (T : NNReal) :
    Integrable (fun u : Real => ∫ z : Sample L, rawRate L (u.toNNReal,z) ∂law L)
      ((volume : Measure Real).restrict (Set.Ioc 0 (T : Real))) := by
  have ht := PhysicalAreaGenerator.generator_time_mean_integrable L
    (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
    (ClippedDiamondGeometry.clippedDomain L)
    (ClippedSquareCoordinates.clippedDomain_subset_centeredSites L hL) T
  have hc : Integrable (fun u : Real => ∫ z : Sample L, cleanupRate L (u.toNNReal,z) ∂law L)
      ((volume : Measure Real).restrict (Set.Ioc 0 (T : Real))) :=
    CumulativeCleanupBudget.time_mean_rate_integrable L
      (I := ClippedProtectedGeometry.protectedSites L)
      (S := ClippedDiamondGeometry.clippedDomain L) (Finset.Subset.refl _)
      (ClippedSquareCoordinates.clippedDomain_subset_centeredSites L hL) T
  apply (ht.sub hc).congr
  exact Filter.Eventually.of_forall (fun u => (expected_raw_eq_sub L hL u.toNNReal).symm)

theorem meanArea_le_raw_integral_add_budget (L : Nat) (hL : 1 ≤ L) (T : NNReal) :
    (∫ z : Sample L, missingArea L T z ∂law L) ≤
      (∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L,
        rawRate L (u.toNNReal,z) ∂law L) + (4 * L + 2 : Real) := by
  have hr := rawRate_time_mean_integrable L hL T
  have hc : Integrable (fun u : Real => ∫ z : Sample L, cleanupRate L (u.toNNReal,z) ∂law L)
      ((volume : Measure Real).restrict (Set.Ioc 0 (T : Real))) :=
    CumulativeCleanupBudget.time_mean_rate_integrable L
      (I := ClippedProtectedGeometry.protectedSites L)
      (S := ClippedDiamondGeometry.clippedDomain L) (Finset.Subset.refl _)
      (ClippedSquareCoordinates.clippedDomain_subset_centeredSites L hL) T
  have hs : (∫ z : Sample L, missingArea L T z ∂law L) =
      (∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L, rawRate L (u.toNNReal,z) ∂law L) +
      (∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L, cleanupRate L (u.toNNReal,z) ∂law L) := by
    rw [PhysicalAreaTail.meanArea_eq_integral_rate L hL T, ← integral_add hr hc]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u => by
      have h := expected_raw_eq_sub L hL u.toNNReal
      linarith)
  rw [hs]
  have hc := CumulativeCleanupBudget.actual_clipped_cleanup_rate_le L hL T
  change (∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L,
    cleanupRate L (u.toNNReal,z) ∂law L) ≤ (4 * L + 2 : Real) at hc
  linarith

theorem exit_probability_le_raw_integral_add_budget (L : Nat) (hL : 40 ≤ L) (T : NNReal) :
    (law L).real (exitEvent L T) ≤
      ((∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L,
        rawRate L (u.toNNReal,z) ∂law L) + (4 * L + 2 : Real)) / ((L : Real)^2 / 1600) :=
  (PhysicalAreaTail.exit_probability_le_mean L hL T).trans
    (div_le_div_of_nonneg_right (meanArea_le_raw_integral_add_budget L (by omega) T)
      (PhysicalAreaTail.threshold_pos L hL).le)

end MathResearchAnalysis.CleanupAreaTail
