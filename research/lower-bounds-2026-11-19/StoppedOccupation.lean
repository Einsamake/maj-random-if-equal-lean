module
public import AsymptoticLower
public import MathResearchAnalysis.ClockEndpointSurvival
public import MathResearchAnalysis.FiniteMachinePreState
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchLower.Occupation
open MathResearchAnalysis MeasureTheory Filter
open ClippedDiamondGeometry (clippedDomain)
open ClippedProtectedGeometry (protectedSites)
open Asymptotic (cleanup slope error)
open Triangle (cost)
open scoped ENNReal

abbrev alive (L : ℕ) := ClockRecoveryComparison.clockProbability (ClippedSquareCoordinates.parameter L)

private def protectedEvent (L : ℕ) (t : ℝ) := {z : DropletClockLaw.Sample L | protectedSites L ⊆
  DropletStoppedClockLaw.stateAt L (clippedDomain L) (protectedSites L) (clippedDomain L) t z}

private theorem protected_le_alive (L : ℕ) (hL : 40 ≤ L) (t : ℝ) :
    (PhysicalAreaTail.law L).real (protectedEvent L t) ≤ alive L t := by
  have he := ENNReal.toReal_mono (measure_ne_top _ _)
    (DropletStoppedClockLaw.original_extinction_measure_le_frozen_protected_missing L hL t)
  have hm := DropletStoppedClockLaw.measurableSet_actual_protected_survival L hL (clippedDomain L) t
  change (PhysicalAreaTail.law L).real _ ≤ (PhysicalAreaTail.law L).real (protectedEvent L t)ᶜ at he
  change MeasurableSet (protectedEvent L t) at hm
  rw [measureReal_compl hm,probReal_univ] at he
  rw [alive,SynchronousQuadraticTail.clockProbability_eq_one_sub_extinction]
  change (PhysicalAreaTail.law L).real (protectedEvent L t) ≤ 1-(PhysicalAreaTail.law L).real {z | ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L) t (fun _ => true) z = fun _ => false}
  linarith

/-- The conditional vanishing after protected loss is retained inside the time integral. -/
theorem mean_raw_le_alive (L : ℕ) (hL : 40 ≤ L) : ∀ᵐ t : ℝ ∂volume, 0 ≤ t →
    (∫ z, WeightedAreaTail.rawContribution L (t.toNNReal,z) ∂PhysicalAreaTail.law L) ≤
    (6*(L : ℝ)+6)*alive L t := by
  filter_upwards [ClockTimeNullGraph.clock_time_sample_ae_no_event (ClippedSquareCoordinates.parameter L)] with t hnone
  intro ht
  let D := clippedDomain L
  let I := protectedSites L
  let E := protectedEvent L t
  let A : ℝ := 6*(L : ℝ)+6
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : MeasurableSet E := DropletStoppedClockLaw.measurableSet_actual_protected_survival L hL D t
  have hpoint : ∀ᵐ z ∂PhysicalAreaTail.law L,
      WeightedAreaTail.rawContribution L (t.toNNReal,z) ≤ E.indicator (fun _ => A) z := by
    filter_upwards [hnone,ClockWordConsistency.marked_sample_good_ae L,
      ActualPreState.beforeState_all_times_ae L D I D,PhysicalWeightedDrift.beforeState_shape_all_times_ae L (by omega)] with z hn hg he hs
    have hbefore : ObservedPreState.beforeState L D I D t.toNNReal z = DropletStoppedClockLaw.stateAt L D I D t z := by
      rw [he t.toNNReal,Real.coe_toNNReal _ ht]
      unfold ActualPreState.strictStateAt DropletStoppedClockLaw.stateAt
      rw [FiniteMachinePreState.strictWord_eq_word_of_no_event _ _ (hg _) hn]
    have hiff : I ⊆ ObservedPreState.beforeState L D I D t.toNNReal z ↔ z ∈ E := by rw [hbefore]; rfl
    unfold WeightedAreaTail.rawContribution
    by_cases h : I ⊆ ObservedPreState.beforeState L D I D t.toNNReal z
    · rw [ite_eq_left h,Set.indicator_of_mem (hiff.mp h)]
      exact raw_drift_le_six (by omega) (hs t.toNNReal)
        ((ClippedProtectedGeometry.innerDiamond_subset_protectedSites L).trans h)
        (ObservedPreState.state_supported L D I (Finset.Subset.refl D) t.toNNReal z)
    · rw [ite_eq_right h,Set.indicator_of_notMem (fun hz => h (hiff.mpr hz))]
  have h := integral_mono_ae (WeightedAreaTail.rawContribution_sample_integrable L (by omega) t.toNNReal)
    ((integrable_const A).indicator hE) hpoint
  rw [integral_indicator hE,setIntegral_const,smul_eq_mul] at h
  exact h.trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (protected_le_alive L hL t) hA)

theorem weighted_occupation (L : ℕ) (hL : 40 ≤ L) (T : NNReal) :
    cost L*(1-alive L T) ≤ (6*(L : ℝ)+6)*(∫ t in (0 : ℝ)..(T : ℝ), alive L t)+cleanup L := by
  have hmono := ClockEndpointSurvival.clockProbability_antitone (ClippedSquareCoordinates.parameter L)
  have hint : IntervalIntegrable (alive L) volume 0 (T : ℝ) := hmono.intervalIntegrable
  have htime := integral_mono_ae (WeightedAreaTail.rawContribution_time_mean_integrable L (by omega) T)
    ((hint.1).const_mul (6*(L : ℝ)+6)) (μ := (volume : Measure ℝ).restrict (Set.Ioc 0 (T : ℝ))) (by
      filter_upwards [ae_restrict_of_ae (mean_raw_le_alive L hL),ae_restrict_mem measurableSet_Ioc] with t h ht
      exact h ht.1.le)
  rw [integral_const_mul] at htime
  have hmean := WeightedAreaTail.meanArea_le_raw_integral_add_budget L (by omega) T
  have he := (ENNReal.toReal_mono (measure_ne_top _ _)
    (FrozenPhysicalExit.original_extinction_measure_le_physical_exit L hL T T.coe_nonneg))
  change (PhysicalAreaTail.law L).real _ ≤ (PhysicalAreaTail.law L).real (PhysicalAreaTail.exitEvent L T) at he
  have hex : (PhysicalAreaTail.law L).real (PhysicalAreaTail.exitEvent L T) ≤
      (PhysicalAreaTail.law L).real {z | cost L ≤ WeightedAreaTail.missingArea L T z} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae (Triangle.physical_loss L (by omega) T))
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (WeightedAreaTail.missingArea_nonnegative L T))
    (WeightedAreaTail.missingArea_integrable L T) (cost L)
  have hp := mul_le_mul_of_nonneg_left (he.trans hex) (show 0 ≤ cost L by unfold cost; positivity)
  rw [intervalIntegral.integral_of_le T.coe_nonneg,alive,SynchronousQuadraticTail.clockProbability_eq_one_sub_extinction,sub_sub_cancel]
  exact hp.trans (hmark.trans (hmean.trans (add_le_add htime le_rfl)))

end MathResearchLower.Occupation
