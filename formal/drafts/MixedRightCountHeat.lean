module
public import MathResearchAnalysis.MixedHeatDecay
public import MathResearchAnalysis.MixedRightCountMoments
public import Mathlib.Tactic
set_option autoImplicit false
/-! The actual right-half mean is bounded using actual heat decay.
The subset Cauchy estimate is applied to the literal right M slots. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MixedRightCountHeat
open scoped BigOperators
open DropletClockLaw (Config)
open ClippedSquareCoordinates (parameter)
open MixedExclusionGenerator (Slot)
open MixedMomentEnergy (centered squareMass)
open MixedRightCountMoments (mean rightSlots)

theorem centered_right_sum (L : Nat) (initial : Config L) (t : Real) :
    (∑ i ∈ rightSlots (parameter L+2), centered L initial t i) =
      mean L initial t-(parameter L+2 : Real)/2 := by
  unfold centered
  rw [Finset.sum_sub_distrib,← MixedRightCountMoments.mean_eq_sum_rho]
  simp [MixedRightCountMoments.rightSlots_card]
  ring

theorem mean_square_error_le_energy (L : Nat) (initial : Config L) (t : Real) :
    (mean L initial t-(parameter L+2 : Real)/2)^2 ≤
      (parameter L+2 : Real)*squareMass L initial t := by
  have hcs := FinitePathPoincare.cauchy_sum (rightSlots (parameter L+2)) (centered L initial t)
  rw [centered_right_sum,MixedRightCountMoments.rightSlots_card] at hcs
  have hs : (∑ i ∈ rightSlots (parameter L+2), (centered L initial t i)^2) ≤
      squareMass L initial t := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.subset_univ _
    · intro i _ _
      exact sq_nonneg _
  have hh := hcs.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (parameter L+2)))
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hh

/-- True expectation of right-half occupancy at a real physical time 16M². -/
theorem mean_at_mixingTime (L : Nat) (initial : Config L) (hinit : Monotone initial) :
    (parameter L+2 : Real)/4 ≤ mean L initial (MixedHeatDecay.mixingTime L) := by
  have hcs := mean_square_error_le_energy L initial (MixedHeatDecay.mixingTime L)
  have hheat := MixedHeatDecay.squareMass_at_mixingTime L initial hinit
  have hp := MixedHeatDecay.side_pos L
  have hb : (mean L initial (MixedHeatDecay.mixingTime L)-(parameter L+2 : Real)/2)^2 ≤
      (parameter L+2 : Real)^2/16 := by
    nlinarith [mul_le_mul_of_nonneg_left hheat hp.le]
  by_contra h
  have hl : mean L initial (MixedHeatDecay.mixingTime L)<(parameter L+2 : Real)/4 := lt_of_not_ge h
  have hprod : 0<((parameter L+2 : Real)/2-mean L initial (MixedHeatDecay.mixingTime L)-
      (parameter L+2 : Real)/4)*((parameter L+2 : Real)/2-
        mean L initial (MixedHeatDecay.mixingTime L)+(parameter L+2 : Real)/4) := by
    apply mul_pos <;> linarith
  nlinarith
end MathResearchAnalysis.MixedRightCountHeat
