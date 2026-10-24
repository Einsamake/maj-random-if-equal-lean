module

public import MathResearchAnalysis.WeightedAreaTail
public import MathResearchAnalysis.WeightedRawRate

set_option autoImplicit false

/-!
# The actual weighted physical drift and a quadratic lower-tail scale

The geometric weighted raw estimate is instantiated on the genuine strict
pre-event frozen trajectory. Both probability and time integrals use the
original clock/mark law and true elapsed Lebesgue time. No raw drift or tail
bound is a premise. The last conclusion is for the original CLOCK process;
there is no synchronous-time conversion or recovery upper bound here.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.PhysicalWeightedDrift

open MeasureTheory
open InfiniteGridModel (Site)
open DropletClockLaw (Sample)
open ClippedDiamondGeometry (clippedDomain)
open ClippedProtectedGeometry (protectedSites innerDiamond)
open PhysicalAreaTail (law exitEvent)

theorem stoppedWord_shape {L : Nat} (hL : 2 ≤ L)
    (w : List DropletModifiedWord.Event) :
    ProtectedEvolution.Shape (DropletStoppedWord.stoppedWord (clippedDomain L)
      (protectedSites L) (clippedDomain L) w) := by
  let fallback : DropletModifiedWord.Event := ((0,0),false)
  rw [DropletStoppedWord.stoppedWord_eq_stoppedTrajectory _ _ _ w fallback]
  exact (ProtectedEvolution.initial_stoppedTrajectory_shape hL _ _).1

theorem strictStateAt_shape {L : Nat} (hL : 2 ≤ L) (t : Real) (z : Sample L) :
    ProtectedEvolution.Shape (ActualPreState.strictStateAt L (clippedDomain L)
      (protectedSites L) (clippedDomain L) t z) :=
  stoppedWord_shape hL _

/-- One original-law exceptional set works simultaneously at every time. -/
theorem beforeState_shape_all_times_ae (L : Nat) (hL : 2 ≤ L) :
    ∀ᵐ z ∂law L, ∀ t : NNReal,
      ProtectedEvolution.Shape (ObservedPreState.beforeState L (clippedDomain L)
        (protectedSites L) (clippedDomain L) t z) := by
  filter_upwards [ActualPreState.beforeState_all_times_ae L (clippedDomain L)
    (protectedSites L) (clippedDomain L)] with z hz
  intro t
  rw [hz t]
  exact strictStateAt_shape hL _ _

/-- The proved geometric rate bound applies to the actual strict past, with
first-loss freezing retained. It is not an input probability hypothesis. -/
theorem rawContribution_le_linear_all_times_ae (L : Nat) (hL : 2 ≤ L) :
    ∀ᵐ z ∂law L, ∀ t : NNReal,
      WeightedAreaTail.rawContribution L (t,z) ≤ (18 * L + 12 : Real) := by
  filter_upwards [beforeState_shape_all_times_ae L hL] with z hz
  intro t
  unfold WeightedAreaTail.rawContribution
  by_cases hI : protectedSites L ⊆ ObservedPreState.beforeState L (clippedDomain L)
      (protectedSites L) (clippedDomain L) t z
  · rw [ite_eq_left hI]
    exact WeightedRawRate.actual_raw_le_linear hL (hz t)
      ((ClippedProtectedGeometry.innerDiamond_subset_protectedSites L).trans hI)
      (ObservedPreState.state_supported L (clippedDomain L) (protectedSites L)
        (Finset.Subset.refl _) t z)
  · rw [ite_eq_right hI]
    positivity

theorem expected_raw_le_linear (L : Nat) (hL : 2 ≤ L) (t : NNReal) :
    (∫ z : Sample L, WeightedAreaTail.rawContribution L (t,z) ∂law L) ≤ (18 * L + 12 : Real) := by
  have hi := WeightedAreaTail.rawContribution_sample_integrable L (by omega : 1 ≤ L) t
  have hpoint : ∀ᵐ z ∂law L,
      WeightedAreaTail.rawContribution L (t,z) ≤ (18 * L + 12 : Real) :=
    (rawContribution_le_linear_all_times_ae L hL).mono (fun _ hz => hz t)
  have h := integral_mono_ae hi (integrable_const (18 * L + 12 : Real)) hpoint
  simpa only [integral_const,probReal_univ,one_smul] using h

/-- A true elapsed-time integral; no count of marked rings is substituted. -/
theorem integral_time_const (T : NNReal) (c : Real) :
    (∫ _u : Real in Set.Ioc 0 (T : Real), c) = (T : Real) * c := by
  rw [integral_const]
  change (((volume : Measure Real).restrict (Set.Ioc 0 (T : Real))) Set.univ).toReal * c = _
  rw [Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero,
    ENNReal.toReal_ofReal T.coe_nonneg]

theorem raw_integral_le_linear_time (L : Nat) (hL : 2 ≤ L) (T : NNReal) :
    (∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L,
      WeightedAreaTail.rawContribution L (u.toNNReal,z) ∂law L) ≤
        (18 * L + 12 : Real) * (T : Real) := by
  have hi := WeightedAreaTail.rawContribution_time_mean_integrable L (by omega : 1 ≤ L) T
  have hc : Integrable (fun _u : Real => (18 * L + 12 : Real))
      ((volume : Measure Real).restrict (Set.Ioc 0 (T : Real))) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have h := integral_mono_ae hi hc
    (Filter.Eventually.of_forall (fun u : Real => expected_raw_le_linear L hL u.toNNReal))
  rw [integral_time_const] at h
  simpa only [mul_comm] using h

theorem actual_mean_weighted_area_le (L : Nat) (hL : 2 ≤ L) (T : NNReal) :
    (∫ z : Sample L, WeightedAreaTail.missingArea L T z ∂law L) ≤
      (18 * L + 12 : Real) * (T : Real) + ((L : Real)+2)*(4*L+2) := by
  exact (WeightedAreaTail.meanArea_le_raw_integral_add_budget L (by omega) T).trans
    (add_le_add (raw_integral_le_linear_time L hL T) le_rfl)

theorem actual_exit_probability_le_linear_time (L : Nat) (hL : 80 ≤ L) (T : NNReal) :
    (law L).real (exitEvent L T) ≤
      ((18 * L + 12 : Real) * (T : Real) + ((L : Real)+2)*(4*L+2)) /
        ((L : Real)^3/128000) :=
  (WeightedAreaTail.exit_probability_le_mean L hL T).trans
    (div_le_div_of_nonneg_right (actual_mean_weighted_area_le L (by omega) T)
      (WeightedAreaTail.threshold_pos L hL).le)

/-- The endpoint event is for the original finite CLOCK model. -/
theorem original_clock_extinction_le_linear_time (L : Nat) (hL : 80 ≤ L) (T : NNReal) :
    (law L).real {z | ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L)
      (T : Real) (fun _ => true) z = fun _ => false} ≤
      ((18 * L + 12 : Real) * (T : Real) + ((L : Real)+2)*(4*L+2)) /
        ((L : Real)^3/128000) := by
  apply le_trans _ (actual_exit_probability_le_linear_time L hL T)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact FrozenPhysicalExit.original_extinction_measure_le_physical_exit L (by omega) T T.coe_nonneg

/-- An explicit finite horizon, with no assumption on whether exit is finite. -/
def quadraticHorizon (L : Nat) : NNReal :=
  ⟨(L : Real)^2/12288000, by positivity⟩

theorem quadratic_bound_le_half_threshold (L : Nat) (hL : 12288000 ≤ L) :
    (18 * L + 12 : Real) * (quadraticHorizon L : Real) + ((L : Real)+2)*(4*L+2) ≤
      ((L : Real)^3/128000) / 2 := by
  have hlarge : (12288000 : Real) ≤ (L : Real) := by exact_mod_cast hL
  have hL1 : (1 : Real) ≤ L := by linarith
  have hL0 : (0 : Real) ≤ L := Nat.cast_nonneg L
  have hcoef : (18 * L + 12 : Real) ≤ 30 * (L : Real) := by linarith
  have hclean : ((L : Real)+2)*(4*L+2) ≤ 18 * (L : Real)^2 := by
    nlinarith [sq_nonneg ((L : Real)-1)]
  have hraw : (18 * L + 12 : Real) * ((L : Real)^2/12288000) ≤
      30 * (L : Real) * ((L : Real)^2/12288000) :=
    mul_le_mul_of_nonneg_right hcoef (by positivity)
  have hcubic := mul_le_mul_of_nonneg_right hlarge (sq_nonneg (L : Real))
  change (18 * L + 12 : Real) * ((L : Real)^2/12288000) + ((L : Real)+2)*(4*L+2) ≤ _
  nlinarith

/-- At this explicit quadratic horizon, actual protected exit has probability
at most one half, for an explicit sufficiently large original half-side. -/
theorem actual_exit_at_quadraticHorizon_le_half (L : Nat) (hL : 12288000 ≤ L) :
    (law L).real (exitEvent L (quadraticHorizon L)) ≤ (1/2 : Real) := by
  have hp := WeightedAreaTail.threshold_pos L (by omega : 80 ≤ L)
  apply (actual_exit_probability_le_linear_time L (by omega) (quadraticHorizon L)).trans
  apply (div_le_iff₀ hp).mpr
  have h := quadratic_bound_le_half_threshold L hL
  nlinarith

/-- A concrete slow-extinction bound for the original CLOCK law, before any
remaining synchronous scheduling conversion. -/
theorem original_clock_extinction_at_quadraticHorizon_le_half (L : Nat) (hL : 12288000 ≤ L) :
    (law L).real {z | ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L)
      (quadraticHorizon L : Real) (fun _ => true) z = fun _ => false} ≤ (1/2 : Real) := by
  apply le_trans _ (actual_exit_at_quadraticHorizon_le_half L hL)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact FrozenPhysicalExit.original_extinction_measure_le_physical_exit L (by omega)
    (quadraticHorizon L) (quadraticHorizon L).coe_nonneg

end MathResearchAnalysis.PhysicalWeightedDrift
