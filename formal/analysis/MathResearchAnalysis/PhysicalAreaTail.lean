module

public import MathResearchAnalysis.PhysicalAreaGenerator
public import MathResearchAnalysis.FrozenPhysicalExit

set_option autoImplicit false

/-!
# Actual physical early-exit probabilities from the proved area formula

The geometric threshold and the original law are instantiated, not assumed.
All bounds retain the actual mean area or its exact generator integral. No
quadratic-scale bound on that mean, synchronous recovery bound or finiteness
of an unbounded recovery/exit time is asserted.
-/

@[expose] public noncomputable section
namespace MathResearchAnalysis.PhysicalAreaTail

open MeasureTheory
open DropletClockLaw (Sample)

abbrev law (L : Nat) := ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)

def missingArea (L : Nat) (T : NNReal) (z : Sample L) : Real :=
  (((ClippedDiamondGeometry.clippedDomain L) \
    DropletStoppedClockLaw.stateAt L (ClippedDiamondGeometry.clippedDomain L)
      (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L)
      (T : Real) z).card : Real)

def exitEvent (L : Nat) (T : NNReal) : Set (Sample L) :=
  {z | FrozenPhysicalExit.physicalExit L (ClippedDiamondGeometry.clippedDomain L)
    (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L) z
      ≤ ENNReal.ofReal (T : Real)}

def rate (L : Nat) (p : NNReal × Sample L) : Real :=
  MaskedAreaGenerator.frozenGenerator (ClippedDiamondGeometry.clippedDomain L)
    (ClippedProtectedGeometry.protectedSites L)
    (ObservedPreState.beforeState L (ClippedDiamondGeometry.clippedDomain L)
      (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L)
      p.1 p.2)
    (fun U => (((ClippedDiamondGeometry.clippedDomain L) \ U).card : Real))

theorem missingArea_nonneg (L : Nat) (T : NNReal) (z : Sample L) :
    0 ≤ missingArea L T z := Nat.cast_nonneg _

theorem missingArea_integrable (L : Nat) (T : NNReal) :
    Integrable (missingArea L T) (law L) :=
  ActualAreaDynkin.area_integrable L _ _ _ T

theorem threshold_pos (L : Nat) (hL : 40 ≤ L) : 0 < (L : Real)^2 / 1600 := by
  have hp : 0 < (L : Real) := by exact_mod_cast (show 0 < L by omega)
  positivity

theorem exit_probability_mul_le_mean (L : Nat) (hL : 40 ≤ L) (T : NNReal) :
    ((L : Real)^2 / 1600) * (law L).real (exitEvent L T) ≤
      ∫ z : Sample L, missingArea L T z ∂law L := by
  have hm : (law L).real (exitEvent L T) ≤
      (law L).real {z | (L : Real)^2 / 1600 ≤ missingArea L T z} := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact FrozenPhysicalExit.physical_exit_measure_le_quadratic_area L hL T T.coe_nonneg
  exact (mul_le_mul_of_nonneg_left hm (threshold_pos L hL).le).trans
    (mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall (missingArea_nonneg L T)) (missingArea_integrable L T) _)

theorem exit_probability_le_mean (L : Nat) (hL : 40 ≤ L) (T : NNReal) :
    (law L).real (exitEvent L T) ≤
      (∫ z : Sample L, missingArea L T z ∂law L) / ((L : Real)^2 / 1600) := by
  apply (le_div_iff₀ (threshold_pos L hL)).mpr
  simpa only [mul_comm] using exit_probability_mul_le_mean L hL T

theorem meanArea_eq_integral_rate (L : Nat) (hL : 1 ≤ L) (T : NNReal) :
    (∫ z : Sample L, missingArea L T z ∂law L) =
      ∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L, rate L (u.toNNReal,z) ∂law L :=
  PhysicalAreaGenerator.actual_clipped_area_dynkin L hL T

theorem exit_probability_le_integral_rate (L : Nat) (hL : 40 ≤ L) (T : NNReal) :
    (law L).real (exitEvent L T) ≤
      (∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L, rate L (u.toNNReal,z) ∂law L) /
        ((L : Real)^2 / 1600) := by
  rw [← meanArea_eq_integral_rate L (by omega) T]
  exact exit_probability_le_mean L hL T

/-- This is the original CLOCK process; no synchronous time conversion is hidden. -/
theorem original_clock_extinction_le_integral_rate (L : Nat) (hL : 40 ≤ L) (T : NNReal) :
    (law L).real {z | ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L)
      (T : Real) (fun _ => true) z = fun _ => false} ≤
      (∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L, rate L (u.toNNReal,z) ∂law L) /
        ((L : Real)^2 / 1600) := by
  apply le_trans _ (exit_probability_le_integral_rate L hL T)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact FrozenPhysicalExit.original_extinction_measure_le_physical_exit L hL T T.coe_nonneg

end MathResearchAnalysis.PhysicalAreaTail
