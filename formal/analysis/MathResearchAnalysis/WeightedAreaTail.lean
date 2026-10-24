module

public import MathResearchAnalysis.WeightedAreaDynkin
public import MathResearchAnalysis.WeightedExitArea
public import MathResearchAnalysis.PhysicalAreaTail

set_option autoImplicit false

/-!
# Actual weighted area and early-exit bounds with only the expanded raw term left

The finite generator is decomposed into the genuine expanded weighted raw rate
and genuine cleanup. The linear weight cancels the forbidden-birth correction
exactly. Physical compensation pays cleanup by its proved perimeter budget;
the cubic geometric threshold then bounds actual physical exit probabilities.
No O(L) raw drift, quadratic recovery estimate, or finite exit is assumed.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.WeightedAreaTail

open MeasureTheory
open DropletClockLaw (Sample)
open InfiniteGridModel (Site)
open ForbiddenBirthControl (weight mass rawWeightedRate)
open ClippedDiamondGeometry (clippedDomain)
open ClippedProtectedGeometry (protectedSites)
open PhysicalAreaTail (law exitEvent)

theorem missing_eq_const_sub {L : Nat} {U : Finset Site} (hUD : U ⊆ clippedDomain L) :
    WeightedAreaDynkin.missing L U = mass (weight L) (clippedDomain L) - mass (weight L) U :=
  (WeightedAreaDynkin.mass_sub_of_subset (weight L) hUD).symm

theorem missing_generator_eq_negative_mass {L : Nat} {I U : Finset Site}
    (hUD : U ⊆ clippedDomain L) :
    MaskedAreaGenerator.frozenGenerator (clippedDomain L) I U (WeightedAreaDynkin.missing L) =
    MaskedAreaGenerator.frozenGenerator (clippedDomain L) I U (fun V => -mass (weight L) V) := by
  calc
    _ = MaskedAreaGenerator.frozenGenerator (clippedDomain L) I U
        (fun V => mass (weight L) (clippedDomain L) + -mass (weight L) V) := by
      apply ProtectedAreaPotential.frozenGenerator_congr
      · simpa only [sub_eq_add_neg] using missing_eq_const_sub hUD
      · intro v _ b
        simpa only [sub_eq_add_neg] using
          missing_eq_const_sub (ProtectedAreaPotential.stoppedStep_supported hUD (v,b))
    _ = _ := ProtectedAreaPotential.frozenGenerator_add_constant _ _ _ _ _

theorem modified_mass_diff (L : Nat) (U : Finset Site) (v : Site) (b : Bool)
    (hv : v ∈ clippedDomain L) :
    mass (weight L) U - mass (weight L) (DropletModifiedWord.modifiedStep (clippedDomain L) U v b) =
    (mass (weight L) U - mass (weight L) (DropletModifiedWord.rawStep U v b)) +
      WeightedAreaDynkin.weightedLoss L U (v,b) := by
  unfold WeightedAreaDynkin.weightedLoss
  rw [DropletModifiedWord.maskedRawStep,ite_eq_left hv]
  ring

theorem negative_mass_generator (L : Nat) (I U : Finset Site) :
    MaskedAreaGenerator.frozenGenerator (clippedDomain L) I U (fun V => -mass (weight L) V) =
    (if I ⊆ U then rawWeightedRate (weight L) (clippedDomain L) U else 0) +
      WeightedAreaDynkin.cleanupRate L I U := by
  by_cases hkeep : I ⊆ U
  · simp only [ite_eq_left hkeep,WeightedAreaDynkin.cleanupRate]
    unfold MaskedAreaGenerator.frozenGenerator rawWeightedRate
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [DropletStoppedWord.stoppedStep,ite_eq_left hkeep]
    have h0 := modified_mass_diff L U v false hv
    have h1 := modified_mass_diff L U v true hv
    linarith
  · rw [MaskedAreaGenerator.frozenGenerator_of_missing _ _ _ _ hkeep]
    simp [WeightedAreaDynkin.cleanupRate,hkeep]

theorem missing_generator_raw_cleanup {L : Nat} {I U : Finset Site}
    (hUD : U ⊆ clippedDomain L) :
    MaskedAreaGenerator.frozenGenerator (clippedDomain L) I U (WeightedAreaDynkin.missing L) =
    (if I ⊆ U then rawWeightedRate (weight L) (clippedDomain L) U else 0) +
      WeightedAreaDynkin.cleanupRate L I U := by
  rw [missing_generator_eq_negative_mass hUD,negative_mass_generator]

theorem missing_generator_expanded_raw_cleanup {L : Nat} (hL : 1 ≤ L)
    {I U : Finset Site} (hUD : U ⊆ clippedDomain L) :
    MaskedAreaGenerator.frozenGenerator (clippedDomain L) I U (WeightedAreaDynkin.missing L) =
    (if I ⊆ U then rawWeightedRate (weight L) (ClippedSquareCoordinates.centeredSites L) U else 0) +
      WeightedAreaDynkin.cleanupRate L I U := by
  rw [missing_generator_raw_cleanup hUD,
    ForbiddenBirthControl.actual_rawWeightedRate_eq_square hL hUD]

def missingArea (L : Nat) (T : NNReal) (z : Sample L) : Real :=
  WeightedAreaDynkin.missing L (DropletStoppedClockLaw.stateAt L
    (clippedDomain L) (protectedSites L) (clippedDomain L) (T : Real) z)

def rate (L : Nat) (p : NNReal × Sample L) : Real :=
  MaskedAreaGenerator.frozenGenerator (clippedDomain L) (protectedSites L)
    (ObservedPreState.beforeState L (clippedDomain L) (protectedSites L)
      (clippedDomain L) p.1 p.2) (WeightedAreaDynkin.missing L)

def rawContribution (L : Nat) (p : NNReal × Sample L) : Real :=
  if protectedSites L ⊆ ObservedPreState.beforeState L (clippedDomain L)
    (protectedSites L) (clippedDomain L) p.1 p.2
  then rawWeightedRate (weight L) (ClippedSquareCoordinates.centeredSites L)
    (ObservedPreState.beforeState L (clippedDomain L) (protectedSites L)
      (clippedDomain L) p.1 p.2)
  else 0

theorem rate_eq_raw_add_cleanup (L : Nat) (hL : 1 ≤ L) (p : NNReal × Sample L) :
    rate L p = rawContribution L p + WeightedAreaDynkin.cleanupContribution L (protectedSites L) p :=
  missing_generator_expanded_raw_cleanup hL
    (ObservedPreState.state_supported L (clippedDomain L) (protectedSites L)
      (Finset.Subset.refl _) p.1 p.2)

theorem rawContribution_sample_integrable (L : Nat) (hL : 1 ≤ L) (u : NNReal) :
    Integrable (fun z : Sample L => rawContribution L (u,z)) (law L) := by
  have ht : Integrable (fun z : Sample L => rate L (u,z)) (law L) :=
    WeightedAreaDynkin.weighted_generator_sample_integrable L hL u
  have hc : Integrable (fun z : Sample L =>
      WeightedAreaDynkin.cleanupContribution L (protectedSites L) (u,z)) (law L) :=
    WeightedAreaDynkin.cleanup_sample_integrable L (protectedSites L) u
  apply (ht.sub hc).congr
  exact Filter.Eventually.of_forall (fun z => by
    change rate L (u,z) - WeightedAreaDynkin.cleanupContribution L (protectedSites L) (u,z) =
      rawContribution L (u,z)
    rw [rate_eq_raw_add_cleanup L hL]
    ring)

theorem expected_raw_eq_sub (L : Nat) (hL : 1 ≤ L) (u : NNReal) :
    (∫ z : Sample L, rawContribution L (u,z) ∂law L) =
      (∫ z : Sample L, rate L (u,z) ∂law L) -
      (∫ z : Sample L, WeightedAreaDynkin.cleanupContribution L (protectedSites L) (u,z) ∂law L) := by
  have ht : Integrable (fun z : Sample L => rate L (u,z)) (law L) :=
    WeightedAreaDynkin.weighted_generator_sample_integrable L hL u
  have hc : Integrable (fun z : Sample L =>
      WeightedAreaDynkin.cleanupContribution L (protectedSites L) (u,z)) (law L) :=
    WeightedAreaDynkin.cleanup_sample_integrable L (protectedSites L) u
  rw [← integral_sub ht hc]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun z => by
    change rawContribution L (u,z) =
      rate L (u,z) - WeightedAreaDynkin.cleanupContribution L (protectedSites L) (u,z)
    rw [rate_eq_raw_add_cleanup L hL]
    ring))

theorem rawContribution_time_mean_integrable (L : Nat) (hL : 1 ≤ L) (T : NNReal) :
    Integrable (fun u : Real => ∫ z : Sample L, rawContribution L (u.toNNReal,z) ∂law L)
      ((volume : Measure Real).restrict (Set.Ioc 0 (T : Real))) := by
  have ht : Integrable (fun u : Real => ∫ z : Sample L, rate L (u.toNNReal,z) ∂law L)
      ((volume : Measure Real).restrict (Set.Ioc 0 (T : Real))) :=
    WeightedAreaDynkin.weighted_generator_time_mean_integrable L hL T
  have hc : Integrable (fun u : Real => ∫ z : Sample L,
      WeightedAreaDynkin.cleanupContribution L (protectedSites L) (u.toNNReal,z) ∂law L)
      ((volume : Measure Real).restrict (Set.Ioc 0 (T : Real))) :=
    WeightedAreaDynkin.cleanup_time_mean_integrable L (protectedSites L) T
  apply (ht.sub hc).congr
  exact Filter.Eventually.of_forall (fun u => (expected_raw_eq_sub L hL u.toNNReal).symm)

theorem meanArea_eq_raw_integral_add_cleanup (L : Nat) (hL : 1 ≤ L) (T : NNReal) :
    (∫ z : Sample L, missingArea L T z ∂law L) =
      (∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L, rawContribution L (u.toNNReal,z) ∂law L) +
      (∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L,
        WeightedAreaDynkin.cleanupContribution L (protectedSites L) (u.toNNReal,z) ∂law L) := by
  have hr := rawContribution_time_mean_integrable L hL T
  have hc : Integrable (fun u : Real => ∫ z : Sample L,
      WeightedAreaDynkin.cleanupContribution L (protectedSites L) (u.toNNReal,z) ∂law L)
      ((volume : Measure Real).restrict (Set.Ioc 0 (T : Real))) :=
    WeightedAreaDynkin.cleanup_time_mean_integrable L (protectedSites L) T
  change (∫ z : Sample L, WeightedAreaDynkin.missing L
    (DropletStoppedClockLaw.stateAt L (clippedDomain L) (protectedSites L)
      (clippedDomain L) (T : Real) z) ∂law L) = _
  rw [WeightedAreaDynkin.actual_weighted_area_dynkin L hL T, ← integral_add hr hc]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u => by
    have h := expected_raw_eq_sub L hL u.toNNReal
    change (∫ z : Sample L, rate L (u.toNNReal,z) ∂law L) = _
    linarith)

set_option maxHeartbeats 800000 in
theorem meanArea_le_raw_integral_add_budget (L : Nat) (hL : 1 ≤ L) (T : NNReal) :
    (∫ z : Sample L, missingArea L T z ∂law L) ≤
      (∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L,
        rawContribution L (u.toNNReal,z) ∂law L) + ((L : Real)+2)*(4*L+2) := by
  have hc : (∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L,
      WeightedAreaDynkin.cleanupContribution L (protectedSites L) (u.toNNReal,z) ∂law L) ≤
      ((L : Real)+2)*(4*L+2) :=
    WeightedAreaDynkin.actual_weighted_cleanup_le L hL T
  rw [meanArea_eq_raw_integral_add_cleanup L hL T]
  linarith only [hc]

theorem missingArea_nonnegative (L : Nat) (T : NNReal) (z : Sample L) :
    0 ≤ missingArea L T z := WeightedAreaDynkin.missing_nonnegative L _

theorem missingArea_integrable (L : Nat) (T : NNReal) :
    Integrable (missingArea L T) (law L) :=
  WeightedAreaDynkin.actual_weighted_area_integrable L T

theorem threshold_pos (L : Nat) (hL : 80 ≤ L) : 0 < (L : Real)^3 / 128000 := by
  have hp : 0 < (L : Real) := by exact_mod_cast (show 0 < L by omega)
  positivity

theorem exit_probability_mul_le_mean (L : Nat) (hL : 80 ≤ L) (T : NNReal) :
    ((L : Real)^3 / 128000) * (law L).real (exitEvent L T) ≤
      ∫ z : Sample L, missingArea L T z ∂law L := by
  have hm : (law L).real (exitEvent L T) ≤
      (law L).real {z | (L : Real)^3 / 128000 ≤ missingArea L T z} := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact WeightedExitArea.physical_exit_measure_le_cubic_weight L hL T T.coe_nonneg
  exact (mul_le_mul_of_nonneg_left hm (threshold_pos L hL).le).trans
    (mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall (missingArea_nonnegative L T)) (missingArea_integrable L T) _)

theorem exit_probability_le_mean (L : Nat) (hL : 80 ≤ L) (T : NNReal) :
    (law L).real (exitEvent L T) ≤
      (∫ z : Sample L, missingArea L T z ∂law L) / ((L : Real)^3 / 128000) := by
  apply (le_div_iff₀ (threshold_pos L hL)).mpr
  simpa only [mul_comm] using exit_probability_mul_le_mean L hL T

theorem exit_probability_le_raw_integral_add_budget (L : Nat) (hL : 80 ≤ L) (T : NNReal) :
    (law L).real (exitEvent L T) ≤
      ((∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L,
        rawContribution L (u.toNNReal,z) ∂law L) + ((L : Real)+2)*(4*L+2)) /
        ((L : Real)^3 / 128000) :=
  (exit_probability_le_mean L hL T).trans
    (div_le_div_of_nonneg_right (meanArea_le_raw_integral_add_budget L (by omega) T)
      (threshold_pos L hL).le)

/-- This conclusion concerns the original CLOCK process; no synchronous-time
conversion or quadratic estimate is hidden in the remaining raw integral. -/
theorem original_clock_extinction_le_raw_integral_add_budget (L : Nat) (hL : 80 ≤ L) (T : NNReal) :
    (law L).real {z | ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L)
      (T : Real) (fun _ => true) z = fun _ => false} ≤
      ((∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L,
        rawContribution L (u.toNNReal,z) ∂law L) + ((L : Real)+2)*(4*L+2)) /
        ((L : Real)^3 / 128000) := by
  apply le_trans _ (exit_probability_le_raw_integral_add_budget L hL T)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact FrozenPhysicalExit.original_extinction_measure_le_physical_exit L (by omega) T T.coe_nonneg

end MathResearchAnalysis.WeightedAreaTail
