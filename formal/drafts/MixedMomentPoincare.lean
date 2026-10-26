module
public import MathResearchAnalysis.FiniteSlotPoincare
public import MathResearchAnalysis.MixedMomentEnergy
public import Mathlib.Tactic
set_option autoImplicit false
/-! Poincare control for the actual centered one-point expectations.
The zero-sum hypothesis is discharged by the original-law particle mass. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MixedMomentPoincare
open scoped BigOperators
open DropletClockLaw (Config)
open ClippedSquareCoordinates (parameter)
open MixedExclusionGenerator (Slot pathEdges)
open MixedMomentEnergy (centered squareMass edgeEnergy)

theorem squareMass_le_edgeEnergy (L : Nat) (initial : Config L)
    (hinit : Monotone initial) (t : Real) :
    squareMass L initial t ≤ (2 * (parameter L+2) : Real)^2 * edgeEnergy L initial t := by
  have h := FiniteSlotPoincare.poincare (2*(parameter L+2)) (centered L initial t)
    (MixedMomentEnergy.centered_total_zero L initial hinit t)
  have he : (∑ e ∈ FiniteSlotPoincare.pathEdges (2*(parameter L+2)),
      (centered L initial t e.1-centered L initial t e.2)^2) = edgeEnergy L initial t := by
    apply Finset.sum_congr rfl
    intro e _
    unfold centered
    ring
  rw [he] at h
  simpa only [squareMass, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using h
end MathResearchAnalysis.MixedMomentPoincare
