module
public import MathResearchAnalysis.MixedMomentEvolution
public import MathResearchAnalysis.FiniteExclusionEnergy
public import Mathlib.Tactic
set_option autoImplicit false
/-! Actual centered first-moment energy under the original mixed-clock law.
The ODE and mass are discharged by the actual process, not assumed. No
Poincare-to-decay estimate, concentration or recovery probability is asserted. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MixedMomentEnergy
open MeasureTheory Set
open scoped BigOperators
open DropletClockLaw (Config)
open ClippedSquareCoordinates (parameter)
open MixedExclusionGenerator (Slot pathEdges slotState)
open MixedClockMoments (rho)
open FiniteExclusionGenerator (oneParticle density)

def centered (L : Nat) (initial : Config L) (t : Real) (i : Slot (parameter L)) : Real :=
  rho L initial t i - 1/2

def squareMass (L : Nat) (initial : Config L) (t : Real) : Real :=
  ∑ i : Slot (parameter L), (centered L initial t i)^2

def edgeEnergy (L : Nat) (initial : Config L) (t : Real) : Real :=
  ∑ e ∈ pathEdges (parameter L), (rho L initial t e.1-rho L initial t e.2)^2

theorem centered_total_zero (L : Nat) (initial : Config L) (hinit : Monotone initial) (t : Real) :
    (∑ i : Slot (parameter L), centered L initial t i) = 0 := by
  unfold centered
  rw [Finset.sum_sub_distrib, MixedMomentEvolution.rho_total_mass L initial hinit t]
  simp only [Finset.sum_const, Finset.card_univ, Slot, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem centered_hasDerivAt (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (t : Real) (ht : 0<t) (i : Slot (parameter L)) :
    HasDerivAt (fun s => centered L initial s i)
      (oneParticle (pathEdges (parameter L)) (centered L initial t) i) t := by
  change HasDerivAt (fun s => rho L initial s i-1/2)
    (oneParticle (pathEdges (parameter L)) (fun j => rho L initial t j-1/2) i) t
  rw [FiniteExclusionEnergy.oneParticle_sub, FiniteExclusionEnergy.oneParticle_const, sub_zero]
  exact (MixedMomentEvolution.rho_hasDerivAt L initial hinit t ht i).sub_const _

theorem squareMass_nonneg (L : Nat) (initial : Config L) (t : Real) :
    0 ≤ squareMass L initial t := Finset.sum_nonneg (fun i _ => sq_nonneg (centered L initial t i))

theorem edgeEnergy_nonneg (L : Nat) (initial : Config L) (t : Real) :
    0 ≤ edgeEnergy L initial t := Finset.sum_nonneg (fun e _ => sq_nonneg (rho L initial t e.1-rho L initial t e.2))

theorem squareMass_continuousOn (L : Nat) (initial : Config L) (hinit : Monotone initial) :
    ContinuousOn (squareMass L initial) (Ici 0) := by
  unfold squareMass centered
  exact continuousOn_finsetSum _ (fun i _ =>
    ((MixedMomentEvolution.rho_continuousOn L initial hinit i).sub continuousOn_const).pow 2)

/-- The physical-time derivative is minus one energy contribution per listed
adjacent bond, with no extra factor of two from fair marks or orientation. -/
theorem squareMass_hasDerivAt (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (t : Real) (ht : 0<t) :
    HasDerivAt (squareMass L initial) (-edgeEnergy L initial t) t := by
  have h := FiniteExclusionEnergy.hasDerivAt_squareMass (pathEdges (parameter L))
    (centered L initial) t (centered_hasDerivAt L initial hinit t ht)
  have hs : (∑ e ∈ pathEdges (parameter L),
      (centered L initial t e.1-centered L initial t e.2)^2) = edgeEnergy L initial t := by
    apply Finset.sum_congr rfl
    intro e _
    unfold centered
    ring
  rw [hs] at h
  exact h

/-- Every deterministic Boolean initial field gives centered square mass M/2.
No independent-occupation or stochastic-initial-state hypothesis is used. -/
theorem squareMass_zero (L : Nat) (initial : Config L) :
    squareMass L initial 0 = (parameter L+2 : Real)/2 := by
  have hv (i : Slot (parameter L)) : (centered L initial 0 i)^2 = (1/4 : Real) := by
    unfold centered
    rw [MixedClockMoments.rho_zero_eq_initial]
    cases h : slotState initial i <;> norm_num [density,h]
  unfold squareMass
  simp_rw [hv]
  simp only [Finset.sum_const, Finset.card_univ, Slot, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  ring
end MathResearchAnalysis.MixedMomentEnergy
