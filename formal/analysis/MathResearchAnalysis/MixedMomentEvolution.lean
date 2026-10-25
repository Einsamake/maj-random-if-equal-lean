module

public import MathResearchAnalysis.MixedClockMoments
public import MathResearchAnalysis.FiniteMomentRegularity

set_option autoImplicit false

/-!
# Actual mixed-clock moment continuity, evolution, and literal particle mass

The integral equations and compact-time integrability are the proved results
for the original marked-clock process. This module derives, rather than
assumes, its one- and two-point ODEs. Total mass comes independently from
samplewise actual particle cardinality and a justified finite integral sum.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.MixedMomentEvolution

open MeasureTheory Set
open scoped BigOperators
open DropletClockLaw (Sample Config)
open ClippedSquareCoordinates (parameter)
open MixedExclusionGenerator (Slot slotState pathEdges)
open MixedClockMoments (occupation rho g)
open FiniteExclusionGenerator (density totalDensity oneParticle twoParticle)

/-- Genuine one-point moments are continuous up to physical time zero. -/
theorem rho_continuousOn (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (i : Slot (parameter L)) : ContinuousOn (fun t => rho L initial t i) (Ici 0) :=
  FiniteMomentRegularity.oneParticle_system_continuous (pathEdges (parameter L))
    (rho L initial) (rho L initial 0)
    (MixedClockMoments.rho_rhs_integrable L initial hinit)
    (MixedClockMoments.rho_integral L initial hinit) i

/-- Genuine simultaneous two-point moments are continuous, including equal indices. -/
theorem g_continuousOn (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (i j : Slot (parameter L)) : ContinuousOn (fun t => g L initial t i j) (Ici 0) :=
  FiniteMomentRegularity.twoParticle_system_continuous (pathEdges (parameter L))
    (g L initial) (g L initial 0)
    (MixedClockMoments.g_rhs_integrable L initial hinit)
    (MixedClockMoments.g_integral L initial hinit) i j

theorem rho_rhs_continuousOn (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (i : Slot (parameter L)) :
    ContinuousOn (fun t => oneParticle (pathEdges (parameter L)) (rho L initial t) i) (Ici 0) :=
  FiniteMomentRegularity.oneParticle_continuousOn _ _ (rho_continuousOn L initial hinit) i

theorem g_rhs_continuousOn (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (i j : Slot (parameter L)) :
    ContinuousOn (fun t => twoParticle (pathEdges (parameter L)) (g L initial t) i j) (Ici 0) :=
  FiniteMomentRegularity.twoParticle_continuousOn _ _ (g_continuousOn L initial hinit) i j

/-- The actual positive-time one-point ODE, without a stochastic or regularity premise. -/
theorem rho_hasDerivAt (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (t : Real) (ht : 0 < t) (i : Slot (parameter L)) :
    HasDerivAt (fun s => rho L initial s i)
      (oneParticle (pathEdges (parameter L)) (rho L initial t) i) t :=
  FiniteMomentRegularity.oneParticle_system_hasDerivAt (pathEdges (parameter L))
    (rho L initial) (rho L initial 0)
    (MixedClockMoments.rho_rhs_integrable L initial hinit)
    (MixedClockMoments.rho_integral L initial hinit) t ht i

/-- The actual simultaneous two-point ODE under the same original law. -/
theorem g_hasDerivAt (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (t : Real) (ht : 0 < t) (i j : Slot (parameter L)) :
    HasDerivAt (fun s => g L initial s i j)
      (twoParticle (pathEdges (parameter L)) (g L initial t) i j) t :=
  FiniteMomentRegularity.twoParticle_system_hasDerivAt (pathEdges (parameter L))
    (g L initial) (g L initial 0)
    (MixedClockMoments.g_rhs_integrable L initial hinit)
    (MixedClockMoments.g_integral L initial hinit) t ht i j

/-- A literal Boolean occupation sum is exactly the actual particle-set cardinality. -/
theorem totalDensity_slotState_eq_card {n : Nat} (f : SquareSpin.Config n) :
    totalDensity (slotState f) = ((YoungParticles.particles f).card : Real) := by
  classical
  unfold totalDensity
  calc
    _ = ∑ s : Slot n, if s ∈ YoungParticles.particles f then (1 : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hmem : s ∈ YoungParticles.particles f <;> simp [density,slotState,hmem]
    _ = _ := by rw [Finset.sum_boole]; simp

/-- Every actual sample keeps precisely one particle per reversed row. -/
theorem occupation_totalDensity (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (t : Real) (z : Sample L) : totalDensity (occupation L initial t z) = (parameter L+2 : Real) := by
  unfold occupation
  rw [totalDensity_slotState_eq_card]
  exact_mod_cast YoungParticles.particles_card
    (MixedSquareClockLaw.endpoint_monotone_shape (parameter L) t initial hinit z)

/-- Genuine mean mass, derived from pointwise mass and finite integral linearity. -/
theorem rho_total_mass (L : Nat) (initial : Config L) (hinit : Monotone initial) (t : Real) :
    (∑ i : Slot (parameter L), rho L initial t i) = (parameter L+2 : Real) := by
  unfold rho
  rw [←integral_finsetSum _ (fun i _ => MixedClockMoments.density_integrable L initial t i)]
  calc
    _ = ∫ _z : Sample L, (parameter L+2 : Real) ∂ClockWordMarks.measure (parameter L) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (occupation_totalDensity L initial hinit t)
    _ = _ := by simp

end MathResearchAnalysis.MixedMomentEvolution

