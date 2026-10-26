module
public import MathResearchAnalysis.ScalarHeatDecay
public import MathResearchAnalysis.MixedMomentPoincare
public import Mathlib.Tactic
set_option autoImplicit false
/-! Actual physical-time heat decay for the mixed clock first moments.
The ODE, zero mass and path Poincare inputs are proved for the original law.
This does not yet compare clocks of different square sizes. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MixedHeatDecay
open Set
open DropletClockLaw (Config)
open ClippedSquareCoordinates (parameter)
open MixedMomentEnergy (squareMass edgeEnergy)

def mixingTime (L : Nat) : Real := 16*(parameter L+2 : Real)^2

theorem side_pos (L : Nat) : 0<(parameter L+2 : Real) := by positivity

theorem mixingTime_nonneg (L : Nat) : 0≤mixingTime L := by unfold mixingTime; positivity

theorem squareMass_differential_bound (L : Nat) (initial : Config L)
    (hinit : Monotone initial) (t : Real) :
    -edgeEnergy L initial t+(1/(4*(parameter L+2 : Real)^2))*squareMass L initial t ≤ 0 := by
  have hp := MixedMomentPoincare.squareMass_le_edgeEnergy L initial hinit t
  have hden : 0<4*(parameter L+2 : Real)^2 := by positivity
  have hdiv : squareMass L initial t/(4*(parameter L+2 : Real)^2) ≤ edgeEnergy L initial t := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  rw [one_div_mul_eq_div]
  linarith

theorem squareMass_le_exponential (L : Nat) (initial : Config L)
    (hinit : Monotone initial) (t : Real) (ht : 0≤t) :
    squareMass L initial t ≤ (parameter L+2 : Real)/2*
      Real.exp (-t/(4*(parameter L+2 : Real)^2)) := by
  have h := ScalarHeatDecay.exponential_decay (squareMass L initial)
    (fun u => -edgeEnergy L initial u) (1/(4*(parameter L+2 : Real)^2))
    (MixedMomentEnergy.squareMass_continuousOn L initial hinit)
    (MixedMomentEnergy.squareMass_hasDerivAt L initial hinit)
    (fun u _ => squareMass_differential_bound L initial hinit u) t ht
  rw [MixedMomentEnergy.squareMass_zero] at h
  have he : -(1/(4*(parameter L+2 : Real)^2))*t = -t/(4*(parameter L+2 : Real)^2) := by ring
  rw [he] at h
  exact h

/-- At a fixed multiple of the side squared, the actual mean field has small
centered square mass. The time is real physical clock time. -/
theorem squareMass_at_mixingTime (L : Nat) (initial : Config L)
    (hinit : Monotone initial) :
    squareMass L initial (mixingTime L) ≤ (parameter L+2 : Real)/16 := by
  have h := squareMass_le_exponential L initial hinit (mixingTime L) (mixingTime_nonneg L)
  have hm : (parameter L+2 : Real)≠0 := ne_of_gt (side_pos L)
  have he : -mixingTime L/(4*(parameter L+2 : Real)^2)=(-4 : Real) := by
    unfold mixingTime
    field_simp [hm]; ring
  rw [he] at h
  calc
    _ ≤ (parameter L+2 : Real)/2*Real.exp (-4) := h
    _ ≤ (parameter L+2 : Real)/2*(1/8) :=
      mul_le_mul_of_nonneg_left ScalarHeatDecay.exp_neg_four_le_eighth (by positivity)
    _ = _ := by ring
end MathResearchAnalysis.MixedHeatDecay
