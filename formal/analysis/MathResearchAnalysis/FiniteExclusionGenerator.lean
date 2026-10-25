module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Bool.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Pure finite adjacent-swap generator algebra

An edge in the supplied finite set is counted once with coefficient one half.
Supplying both directed versions counts twice. Self-loops act as the identity.
The observable identities are deterministic finite sums; no process law,
Kolmogorov equation or covariance sign is assumed.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace MathResearchAnalysis.FiniteExclusionGenerator

universe u
variable {V : Type u} [DecidableEq V]

abbrev Config (V : Type u) := V → Bool

/-- Actual pullback of a Boolean occupation field by the two-site swap. -/
def swapConfig (η : Config V) (a b : V) : Config V := η ∘ Equiv.swap a b

/-- One occupied slot contributes one, viewed as a real number. -/
def density (η : Config V) (i : V) : Real := (η i).toNat

/-- Total number of occupied sites, retaining its literal finite-sum meaning. -/
def totalDensity [Fintype V] (η : Config V) : Real := ∑ i : V, density η i

/-- The genuine finite swap rule, with rate one half for each listed edge. -/
def generator (E : Finset (V × V)) (F : Config V → Real) (η : Config V) : Real :=
  ∑ e ∈ E, (F (swapConfig η e.1 e.2)-F η)/2

/-- The same edge rule acting on one index of a real field. -/
def oneParticle (E : Finset (V × V)) (ρ : V → Real) (i : V) : Real :=
  ∑ e ∈ E, (ρ (Equiv.swap e.1 e.2 i)-ρ i)/2

/-- Both indices see the same edge swap, including when the indices coincide. -/
def twoParticle (E : Finset (V × V)) (h : V → V → Real) (i j : V) : Real :=
  ∑ e ∈ E, (h (Equiv.swap e.1 e.2 i) (Equiv.swap e.1 e.2 j)-h i j)/2

@[simp] theorem density_swapConfig (η : Config V) (a b i : V) :
    density (swapConfig η a b) i = density η (Equiv.swap a b i) := rfl

@[simp] theorem generator_const (E : Finset (V × V)) (c : Real) (η : Config V) :
    generator E (fun _ => c) η = 0 := by
  simp [generator]

theorem generator_add (E : Finset (V × V)) (F G : Config V → Real) (η : Config V) :
    generator E (fun ξ => F ξ+G ξ) η = generator E F η+generator E G η := by
  unfold generator
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem generator_mul_const (E : Finset (V × V)) (c : Real) (F : Config V → Real) (η : Config V) :
    generator E (fun ξ => c*F ξ) η = c*generator E F η := by
  unfold generator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem generator_sub (E : Finset (V × V)) (F G : Config V → Real) (η : Config V) :
    generator E (fun ξ => F ξ-G ξ) η = generator E F η-generator E G η := by
  unfold generator
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e he
  ring

/-- Swapping sites preserves the literal total number of occupied sites. -/
theorem totalDensity_swapConfig [Fintype V] (η : Config V) (a b : V) :
    totalDensity (swapConfig η a b) = totalDensity η := by
  unfold totalDensity
  simp only [density_swapConfig]
  exact Equiv.sum_comp (Equiv.swap a b) (density η)

theorem generator_totalDensity [Fintype V] (E : Finset (V × V)) (η : Config V) :
    generator E totalDensity η = 0 := by
  simp only [generator,totalDensity_swapConfig,sub_self,zero_div,Finset.sum_const_zero]

/-- The actual one-point Boolean observable is acted on by the one-index rule. -/
theorem generator_density (E : Finset (V × V)) (η : Config V) (i : V) :
    generator E (fun ξ => density ξ i) η = oneParticle E (density η) i := rfl

/-- The actual product observable is acted on by the simultaneous two-index rule. -/
theorem generator_density_product (E : Finset (V × V)) (η : Config V) (i j : V) :
    generator E (fun ξ => density ξ i*density ξ j) η =
      twoParticle E (fun a b => density η a*density η b) i j := rfl

/-- The one-edge product defect vanishes unless that edge connects the distinct
indices. A connecting edge contributes their squared difference divided by two. -/
theorem one_edge_product_defect (ρ : V → Real) (i j a b : V) (hij : i ≠ j) :
    ((ρ (Equiv.swap a b i)-ρ i)/2)*ρ j +
      ρ i*((ρ (Equiv.swap a b j)-ρ j)/2) -
      (ρ (Equiv.swap a b i)*ρ (Equiv.swap a b j)-ρ i*ρ j)/2 =
      if (a=i ∧ b=j) ∨ (a=j ∧ b=i) then (ρ i-ρ j)^2/2 else 0 := by
  by_cases hia : i = a <;> by_cases hib : i = b <;>
    by_cases hja : j = a <;> by_cases hjb : j = b <;>
    simp_all [Equiv.swap_apply_def,eq_comm] <;> ring

/-- Exact finite two-point defect. The filter counts both orientations if both
are supplied, while self-loops contribute nothing. -/
theorem product_defect (E : Finset (V × V)) (ρ : V → Real) (i j : V) (hij : i ≠ j) :
    (oneParticle E ρ i)*ρ j + ρ i*(oneParticle E ρ j) -
      twoParticle E (fun a b => ρ a*ρ b) i j =
      ((ρ i-ρ j)^2/2)*
        ((E.filter (fun e => (e.1=i ∧ e.2=j) ∨ (e.1=j ∧ e.2=i))).card : Real) := by
  unfold oneParticle twoParticle
  rw [Finset.sum_mul,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
  simp_rw [one_edge_product_defect ρ i j _ _ hij]
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const]
  ring



/-- The explicit source term is nonnegative; this is an algebraic sign,
not a covariance theorem for a stochastic process. -/
theorem product_defect_nonneg (E : Finset (V × V)) (ρ : V → Real) (i j : V) (hij : i ≠ j) :
    0 ≤ (oneParticle E ρ i)*ρ j + ρ i*(oneParticle E ρ j) -
      twoParticle E (fun a b => ρ a*ρ b) i j := by
  rw [product_defect E ρ i j hij]
  exact mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) (Nat.cast_nonneg _)

end MathResearchAnalysis.FiniteExclusionGenerator
