module
public import MathResearchAnalysis.FiniteExclusionGenerator
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic
set_option autoImplicit false
/-! Exact mass conservation and Dirichlet energy for the actual finite
rate-one-half swap operator. Each listed edge is counted once, including
self-loops (zero contribution). No stochastic moment equation is assumed
here; later actual moments must discharge the displayed derivative premise. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.FiniteExclusionEnergy
open scoped BigOperators
open FiniteExclusionGenerator
universe u
variable {V : Type u} [DecidableEq V]

theorem oneParticle_add (E : Finset (V × V)) (f g : V → Real) (i : V) :
    oneParticle E (fun j => f j+g j) i = oneParticle E f i + oneParticle E g i := by
  unfold oneParticle
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem oneParticle_sub (E : Finset (V × V)) (f g : V → Real) (i : V) :
    oneParticle E (fun j => f j-g j) i = oneParticle E f i - oneParticle E g i := by
  unfold oneParticle
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

@[simp] theorem oneParticle_const (E : Finset (V × V)) (c : Real) (i : V) :
    oneParticle E (fun _ => c) i = 0 := by simp [oneParticle]

theorem oneParticle_mul_const (E : Finset (V × V)) (f : V → Real) (c : Real) (i : V) :
    oneParticle E (fun j => c*f j) i = c*oneParticle E f i := by
  unfold oneParticle
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- Exactly zero total flux, with no boundary or graph-connectedness premise. -/
theorem sum_oneParticle [Fintype V] (E : Finset (V × V)) (f : V → Real) :
    (∑ i : V, oneParticle E f i) = 0 := by
  unfold oneParticle
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  rw [Equiv.sum_comp (Equiv.swap e.1 e.2) f, sub_self, zero_div]

/-- An edge flux pairs only its two actual endpoints. -/
theorem one_edge_flux [Fintype V] (f w : V → Real) (a b : V) :
    (∑ i : V, w i*(f (Equiv.swap a b i)-f i)) =
      -(w a-w b)*(f a-f b) := by
  classical
  by_cases hab : a=b
  · subst b
    simp
  · have hterm (i : V) : w i*(f (Equiv.swap a b i)-f i) =
        (if i=a then w a*(f b-f a) else 0) +
        (if i=b then w b*(f a-f b) else 0) := by
      by_cases hia : i=a <;> by_cases hib : i=b <;>
        simp_all [Equiv.swap_apply_def]
    simp_rw [hterm,Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring

/-- Discrete integration by parts at the original one-half edge rate. -/
theorem integration_by_parts [Fintype V] (E : Finset (V × V)) (f w : V → Real) :
    (∑ i : V, w i*oneParticle E f i) =
      -(∑ e ∈ E, (w e.1-w e.2)*(f e.1-f e.2))/2 := by
  unfold oneParticle
  simp_rw [Finset.mul_sum, ← mul_div_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_div, one_edge_flux]
  simp only [neg_mul, neg_div, Finset.sum_neg_distrib, Finset.sum_div]

/-- The energy derivative uses each listed edge once, without an extra half. -/
theorem dirichlet_identity [Fintype V] (E : Finset (V × V)) (f : V → Real) :
    (∑ i : V, 2*f i*oneParticle E f i) =
      -(∑ e ∈ E, (f e.1-f e.2)^2) := by
  have h := integration_by_parts E f f
  have hleft : (∑ i : V, 2*f i*oneParticle E f i) =
      2*(∑ i : V, f i*oneParticle E f i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hleft,h]
  have hs : (∑ e ∈ E, (f e.1-f e.2)*(f e.1-f e.2)) =
      ∑ e ∈ E, (f e.1-f e.2)^2 := by
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hs]
  ring

/-- Generic finite heat trajectories inherit a genuinely proved energy identity.
The actual-clock derivative hypothesis is discharged in a separate module. -/
theorem hasDerivAt_squareMass [Fintype V] (E : Finset (V × V)) (f : Real → V → Real) (t : Real)
    (hf : ∀ i : V, HasDerivAt (fun s => f s i) (oneParticle E (f t) i) t) :
    HasDerivAt (fun s => ∑ i : V, (f s i)^2)
      (-(∑ e ∈ E, (f t e.1-f t e.2)^2)) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hf i).pow 2)
  convert h using 1
  simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using (dirichlet_identity E (f t)).symm

theorem hasDerivAt_total [Fintype V] (E : Finset (V × V)) (f : Real → V → Real) (t : Real)
    (hf : ∀ i : V, HasDerivAt (fun s => f s i) (oneParticle E (f t) i) t) :
    HasDerivAt (fun s => ∑ i : V, f s i) 0 t := by
  convert HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hf i) using 1
  exact (sum_oneParticle E (f t)).symm
end MathResearchAnalysis.FiniteExclusionEnergy
