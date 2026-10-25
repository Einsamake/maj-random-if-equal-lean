module

public import MathResearchAnalysis.MixedMomentEvolution
public import MathResearchAnalysis.FinitePermutationComparison

set_option autoImplicit false

/-!
# Nonpositive covariance for distinct slots of the actual mixed clock process

Only distinct ordered slot pairs are states of the comparison system. Every
listed physical edge acts by a genuine permutation of this finite state set.
Continuity, derivatives and initial values come from the true mixed-clock
moments; the forcing sign is the proved finite swap product-defect identity.
No covariance sign, moment equation or stochastic law is a supplied premise.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.MixedClockCovariance

open Set
open DropletClockLaw (Config)
open ClippedSquareCoordinates (parameter)
open MixedExclusionGenerator (Slot pathEdges)
open MixedClockMoments (rho g)
open FiniteExclusionGenerator (oneParticle twoParticle)

/-- The diagonal is excluded from the comparison state space. -/
abbrev Pair (L : Nat) := {p : Slot (parameter L) × Slot (parameter L) // p.1 ≠ p.2}

/-- Simultaneously swapping both indices preserves distinctness and is an
actual finite permutation, not a partially defined transition. -/
def pairSwap (L : Nat) (e : Slot (parameter L) × Slot (parameter L)) : Pair L ≃ Pair L :=
  (Equiv.prodCongr (Equiv.swap e.1 e.2) (Equiv.swap e.1 e.2)).subtypeEquiv (by
    intro q
    change (q.1 ≠ q.2) ↔
      (Equiv.swap e.1 e.2 q.1 ≠ Equiv.swap e.1 e.2 q.2)
    constructor
    · intro h he
      exact h ((Equiv.swap e.1 e.2).injective he)
    · intro h he
      exact h (congrArg (Equiv.swap e.1 e.2) he))

@[simp] theorem pairSwap_val (L : Nat) (e : Slot (parameter L) × Slot (parameter L)) (p : Pair L) :
    (pairSwap L e p).1 = (Equiv.swap e.1 e.2 p.1.1,Equiv.swap e.1 e.2 p.1.2) := rfl

/-- The actual off-diagonal covariance under the original probability law. -/
def covariance (L : Nat) (initial : Config L) (t : Real) (p : Pair L) : Real :=
  g L initial t p.1.1 p.1.2-rho L initial t p.1.1*rho L initial t p.1.2

/-- The source is the actual first-moment field's finite swap product defect. -/
def source (L : Nat) (initial : Config L) (t : Real) (p : Pair L) : Real :=
  (oneParticle (pathEdges (parameter L)) (rho L initial t) p.1.1)*rho L initial t p.1.2 +
    rho L initial t p.1.1*(oneParticle (pathEdges (parameter L)) (rho L initial t) p.1.2) -
    twoParticle (pathEdges (parameter L))
      (fun a b => rho L initial t a*rho L initial t b) p.1.1 p.1.2

theorem source_eq_square (L : Nat) (initial : Config L) (t : Real) (p : Pair L) :
    source L initial t p = ((rho L initial t p.1.1-rho L initial t p.1.2)^2/2)*
      (((pathEdges (parameter L)).filter (fun e =>
        (e.1=p.1.1 ∧ e.2=p.1.2) ∨ (e.1=p.1.2 ∧ e.2=p.1.1))).card : Real) :=
  FiniteExclusionGenerator.product_defect _ _ _ _ p.2

theorem source_nonneg (L : Nat) (initial : Config L) (t : Real) (p : Pair L) :
    0 ≤ source L initial t p :=
  FiniteExclusionGenerator.product_defect_nonneg _ _ _ _ p.2

/-- The pair-domain permutation rate agrees exactly with the two-index rate,
with no transition into the diagonal and no discarded contribution. -/
theorem rate_covariance (L : Nat) (initial : Config L) (t : Real) (p : Pair L) :
    FinitePermutationComparison.rate (pathEdges (parameter L)) (pairSwap L) (covariance L initial t) p =
      twoParticle (pathEdges (parameter L)) (g L initial t) p.1.1 p.1.2 -
        twoParticle (pathEdges (parameter L))
          (fun a b => rho L initial t a*rho L initial t b) p.1.1 p.1.2 := by
  unfold FinitePermutationComparison.rate covariance twoParticle
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e he
  simp only [pairSwap_val]
  ring

theorem covariance_zero (L : Nat) (initial : Config L) (p : Pair L) :
    covariance L initial 0 p = 0 := by
  simp only [covariance,MixedClockMoments.g_zero_eq_initial,MixedClockMoments.rho_zero_eq_initial,sub_self]

theorem covariance_continuousOn (L : Nat) (initial : Config L) (hinit : Monotone initial) (p : Pair L) :
    ContinuousOn (fun t => covariance L initial t p) (Ici 0) := by
  exact (MixedMomentEvolution.g_continuousOn L initial hinit p.1.1 p.1.2).sub
    ((MixedMomentEvolution.rho_continuousOn L initial hinit p.1.1).mul
      (MixedMomentEvolution.rho_continuousOn L initial hinit p.1.2))

/-- This derivative is derived from the actual moment derivatives, rather
than supplied as a covariance equation hypothesis. -/
theorem covariance_hasDerivAt (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (t : Real) (ht : 0 < t) (p : Pair L) :
    HasDerivAt (fun s => covariance L initial s p)
      (FinitePermutationComparison.rate (pathEdges (parameter L)) (pairSwap L) (covariance L initial t) p -
        source L initial t p) t := by
  have hr : FinitePermutationComparison.rate (pathEdges (parameter L)) (pairSwap L)
      (covariance L initial t) p-source L initial t p =
      twoParticle (pathEdges (parameter L)) (g L initial t) p.1.1 p.1.2 -
        ((oneParticle (pathEdges (parameter L)) (rho L initial t) p.1.1)*rho L initial t p.1.2 +
          rho L initial t p.1.1*(oneParticle (pathEdges (parameter L)) (rho L initial t) p.1.2)) := by
    rw [rate_covariance]
    unfold source
    ring
  rw [hr]
  exact (MixedMomentEvolution.g_hasDerivAt L initial hinit t ht p.1.1 p.1.2).sub
    ((MixedMomentEvolution.rho_hasDerivAt L initial hinit t ht p.1.1).mul
      (MixedMomentEvolution.rho_hasDerivAt L initial hinit t ht p.1.2))

/-- True off-diagonal covariance is nonpositive at all nonnegative physical times. -/
theorem covariance_nonpos (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (t : Real) (ht : 0 ≤ t) (p : Pair L) : covariance L initial t p ≤ 0 :=
  FinitePermutationComparison.nonpos (pathEdges (parameter L)) (pairSwap L)
    (covariance L initial) (source L initial)
    (covariance_continuousOn L initial hinit)
    (fun s hs => covariance_hasDerivAt L initial hinit s hs)
    (fun s _ => source_nonneg L initial s)
    (fun q => (covariance_zero L initial q).le) t ht p

/-- The actual two-point moment factors from above only for distinct slots.
The diagonal Bernoulli variance is not included in this assertion. -/
theorem offdiag_moment_le_product (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (t : Real) (ht : 0 ≤ t) (i j : Slot (parameter L)) (hij : i ≠ j) :
    g L initial t i j ≤ rho L initial t i*rho L initial t j :=
  sub_nonpos.mp (covariance_nonpos L initial hinit t ht ⟨(i,j),hij⟩)

end MathResearchAnalysis.MixedClockCovariance
