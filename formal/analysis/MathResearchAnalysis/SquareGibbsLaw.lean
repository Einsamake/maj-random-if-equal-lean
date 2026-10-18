module

public import MathResearchAnalysis.SquareGibbs

set_option autoImplicit false

/-!
# Normalized finite-square Gibbs probabilities and actual heat-bath balance

The configuration space is the actual finite Bool-valued square. The strictly
positive weights are normalized by their finite partition sum. The one-site
kernel is defined by the two actual Gibbs weights and is proved equal to the
existing heat-bath logistic update. Its detailed balance and stationarity are
proved for these probabilities, without balance or stationarity assumptions.
No Peres--Winkler inequality is asserted here.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace MathResearchAnalysis.SquareGibbsLaw

abbrev Site (n : Nat) := SquareTasks.Vertex n
abbrev Config (n : Nat) := SquareSpin.Config n

def partition (n : Nat) (β : ℝ) : ℝ := ∑ f : Config n, SquareGibbs.weight β f

theorem partition_pos (n : Nat) (β : ℝ) : 0 < partition n β := by
  exact Finset.sum_pos (fun f _ => SquareGibbs.weight_pos β f) Finset.univ_nonempty

/-- Actual normalized probability mass of every finite square configuration. -/
def mass {n : Nat} (β : ℝ) (f : Config n) : ℝ :=
  SquareGibbs.weight β f / partition n β

theorem mass_pos {n : Nat} (β : ℝ) (f : Config n) : 0 < mass β f :=
  div_pos (SquareGibbs.weight_pos β f) (partition_pos n β)

theorem mass_nonneg {n : Nat} (β : ℝ) (f : Config n) : 0 ≤ mass β f :=
  (mass_pos β f).le

theorem sum_mass (n : Nat) (β : ℝ) : ∑ f : Config n, mass β f = 1 := by
  unfold mass
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos n β))

def SameOutside {n : Nat} (v : Site n) (f g : Config n) : Prop :=
  ∀ u, u ≠ v → f u = g u

theorem sameOutside_symmetric {n : Nat} {v : Site n} {f g : Config n}
    (h : SameOutside v f g) : SameOutside v g f := fun u hu => (h u hu).symm

theorem sameOutside_update {n : Nat} (f : Config n) (v : Site n) (b : Bool) :
    SameOutside v f (Function.update f v b) := by
  intro u hu
  simp [Function.update, hu]

theorem sameOutside_eq_update {n : Nat} {v : Site n} {f g : Config n}
    (h : SameOutside v f g) : g = Function.update f v (g v) := by
  funext u
  by_cases hu : u = v
  · subst u
    simp
  · simpa only [Function.update_of_ne hu] using (h u hu).symm

theorem sameOutside_update_eq {n : Nat} {v : Site n} {f g : Config n}
    (h : SameOutside v f g) (b : Bool) :
    Function.update f v b = Function.update g v b := by
  funext u
  by_cases hu : u = v
  · subst u
    simp
  · simpa only [Function.update_of_ne hu] using h u hu

/-- The single-site Gibbs resampling kernel, written directly as a two-weight ratio. -/
def kernel {n : Nat} (β : ℝ) (v : Site n) (f g : Config n) : ℝ := by
  classical
  exact if SameOutside v f g then
    SquareGibbs.weight β g /
      (SquareGibbs.weight β (Function.update f v true) +
        SquareGibbs.weight β (Function.update f v false))
  else 0

theorem kernel_nonneg {n : Nat} (β : ℝ) (v : Site n) (f g : Config n) :
    0 ≤ kernel β v f g := by
  classical
  unfold kernel
  split_ifs
  · exact (div_pos (SquareGibbs.weight_pos β g)
      (add_pos (SquareGibbs.weight_pos β _) (SquareGibbs.weight_pos β _))).le
  · exact le_rfl

theorem kernel_update_true {n : Nat} (β : ℝ) (v : Site n) (f : Config n) :
    kernel β v f (Function.update f v true) = SquareGibbs.conditionalTrue β f v := by
  classical
  simp only [kernel, ite_eq_left (sameOutside_update f v true), SquareGibbs.conditionalTrue]

theorem kernel_update_false {n : Nat} (β : ℝ) (v : Site n) (f : Config n) :
    kernel β v f (Function.update f v false) = 1 - SquareGibbs.conditionalTrue β f v := by
  classical
  simp only [kernel, ite_eq_left (sameOutside_update f v false), SquareGibbs.conditionalTrue]
  have hp : 0 < SquareGibbs.weight β (Function.update f v true) +
      SquareGibbs.weight β (Function.update f v false) :=
    add_pos (SquareGibbs.weight_pos β _) (SquareGibbs.weight_pos β _)
  field_simp
  ring

private theorem update_true_ne_false {n : Nat} (f : Config n) (v : Site n) :
    Function.update f v true ≠ Function.update f v false := by
  intro h
  have hv := congrFun h v
  simp [Function.update] at hv

/-- This weight-based kernel is the actual finite-temperature heat-bath kernel. -/
theorem kernel_eq_warmProbability {n : Nat} (β : ℝ) (v : Site n) (f g : Config n) :
    kernel β v f g =
      ZeroTemperature.warmProbability β (ZeroTemperature.field f v) *
        (if Function.update f v true = g then 1 else 0) +
      (1 - ZeroTemperature.warmProbability β (ZeroTemperature.field f v)) *
        (if Function.update f v false = g then 1 else 0) := by
  classical
  by_cases h : SameOutside v f g
  · have heq := sameOutside_eq_update h
    cases hvalue : g v with
    | false =>
      rw [hvalue] at heq
      rw [heq, kernel_update_false, ← SquareGibbs.conditionalTrue_eq_warmProbability]
      simp only [update_true_ne_false, ite_false, ite_true, mul_zero, mul_one, zero_add]
    | true =>
      rw [hvalue] at heq
      rw [heq, kernel_update_true, ← SquareGibbs.conditionalTrue_eq_warmProbability]
      simp only [Ne.symm (update_true_ne_false f v), ite_true, ite_false, mul_one,
        mul_zero, add_zero]
  · have ht : Function.update f v true ≠ g := by
      intro heq
      apply h
      rw [← heq]
      exact sameOutside_update f v true
    have hf : Function.update f v false ≠ g := by
      intro heq
      apply h
      rw [← heq]
      exact sameOutside_update f v false
    simp only [kernel, ite_eq_right h, ite_eq_right ht, ite_eq_right hf, mul_zero, add_zero]

theorem kernel_sum_one {n : Nat} (β : ℝ) (v : Site n) (f : Config n) :
    ∑ g : Config n, kernel β v f g = 1 := by
  classical
  simp_rw [kernel_eq_warmProbability]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp

/-- Detailed balance follows from the actual common two-state conditional denominator. -/
theorem detailed_balance {n : Nat} (β : ℝ) (v : Site n) (f g : Config n) :
    mass β f * kernel β v f g = mass β g * kernel β v g f := by
  classical
  by_cases h : SameOutside v f g
  · have ht := sameOutside_update_eq h true
    have hf := sameOutside_update_eq h false
    simp only [kernel, ite_eq_left h, ite_eq_left (sameOutside_symmetric h), mass]
    rw [← ht, ← hf]
    ring
  · have hr : ¬ SameOutside v g f := fun hr => h (sameOutside_symmetric hr)
    simp only [kernel, ite_eq_right h, ite_eq_right hr, mul_zero]

/-- The proved heat-bath kernel preserves the actual normalized Gibbs probabilities. -/
theorem stationary {n : Nat} (β : ℝ) (v : Site n) (g : Config n) :
    ∑ f : Config n, mass β f * kernel β v f g = mass β g := by
  calc
    _ = ∑ f : Config n, mass β g * kernel β v g f :=
      Finset.sum_congr rfl (fun f _ => detailed_balance β v f g)
    _ = mass β g * ∑ f : Config n, kernel β v g f := (Finset.mul_sum _ _ _).symm
    _ = mass β g := by rw [kernel_sum_one, mul_one]

end MathResearchAnalysis.SquareGibbsLaw
