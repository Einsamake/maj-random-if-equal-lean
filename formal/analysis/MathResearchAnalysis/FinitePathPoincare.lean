module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
# A quantitative finite-path Poincare inequality

Only nearest-neighbour differences on the actual n-vertex path enter energy.
No spectral gap, random-process estimate or differential equation is assumed.
The deliberately loose constant n^2 also covers the empty path.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace MathResearchAnalysis.FinitePathPoincare

def energy (n : Nat) (u : Nat → Real) : Real :=
  ∑ k ∈ Finset.range (n-1), (u (k+1)-u k)^2

def squareMass (n : Nat) (u : Nat → Real) : Real :=
  ∑ i ∈ Finset.range n, (u i)^2

theorem energy_nonneg (n : Nat) (u : Nat → Real) : 0 ≤ energy n u := by
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem cauchy_sum {α : Type*} (s : Finset α) (g : α → Real) :
    (∑ i ∈ s, g i)^2 ≤ (s.card : Real) * ∑ i ∈ s, (g i)^2 := by
  simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] using
    Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : Real)) g

theorem telescope (u : Nat → Real) (i j : Nat) (hij : i ≤ j) :
    (∑ k ∈ Finset.Ico i j, (u (k+1)-u k)) = u j-u i := by
  exact Finset.sum_Ico_sub (f := u) hij

theorem interval_energy_le (n : Nat) (u : Nat → Real) (i j : Nat)
    (hj : j < n) :
    (∑ k ∈ Finset.Ico i j, (u (k+1)-u k)^2) ≤ energy n u := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    have hkj := (Finset.mem_Ico.mp hk).2
    rw [Finset.mem_range]
    omega
  · intro k _ _
    exact sq_nonneg _

theorem ordered_difference_sq_le (n : Nat) (u : Nat → Real) (i j : Nat)
    (hij : i ≤ j) (hj : j < n) :
    (u j-u i)^2 ≤ (n : Real) * energy n u := by
  have hcs := cauchy_sum (Finset.Ico i j) (fun k => u (k+1)-u k)
  rw [telescope u i j hij] at hcs
  have he := interval_energy_le n u i j hj
  have hc : ((Finset.Ico i j).card : Real) ≤ (n : Real) := by
    rw [Nat.card_Ico]
    exact_mod_cast (show j-i ≤ n by omega)
  exact hcs.trans ((mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_right hc (energy_nonneg n u)))

theorem difference_sq_le (n : Nat) (u : Nat → Real) (i j : Nat)
    (hi : i < n) (hj : j < n) :
    (u i-u j)^2 ≤ (n : Real) * energy n u := by
  rcases le_total i j with hij | hji
  · have h := ordered_difference_sq_le n u i j hij hj
    nlinarith
  · exact ordered_difference_sq_le n u j i hji hi

theorem centered_difference_sum (n : Nat) (u : Nat → Real)
    (hzero : ∑ j ∈ Finset.range n, u j = 0) (i : Nat) :
    (∑ j ∈ Finset.range n, (u i-u j)) = (n : Real)*u i := by
  rw [Finset.sum_sub_distrib,hzero,sub_zero]
  simp

theorem centered_point_sq_le (n : Nat) (hn : 0 < n) (u : Nat → Real)
    (hzero : ∑ j ∈ Finset.range n, u j = 0) (i : Nat) (hi : i < n) :
    (u i)^2 ≤ (n : Real)*energy n u := by
  have hcs := cauchy_sum (Finset.range n) (fun j => u i-u j)
  rw [centered_difference_sum n u hzero,Finset.card_range] at hcs
  have hsum : (∑ j ∈ Finset.range n, (u i-u j)^2) ≤
      (n : Real)^2*energy n u := by
    have h := Finset.sum_le_sum (fun j hj =>
      difference_sq_le n u i j hi (Finset.mem_range.mp hj))
    calc
      _ ≤ ∑ _j ∈ Finset.range n, (n : Real)*energy n u := h
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring
  have hscaled := hcs.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg n))
  have hnreal : (0 : Real) < n := by exact_mod_cast hn
  have hpos : 0 < (n : Real)^2 := sq_pos_of_pos hnreal
  apply (mul_le_mul_iff_of_pos_left hpos).mp
  nlinarith [hscaled]

/-- A finite path with mean-zero values has explicit inverse-square gap control. -/
theorem poincare (n : Nat) (u : Nat → Real)
    (hzero : ∑ i ∈ Finset.range n, u i = 0) :
    squareMass n u ≤ (n : Real)^2 * energy n u := by
  by_cases hn : n = 0
  · subst n
    simp [squareMass,energy]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have h := Finset.sum_le_sum (fun i hi =>
      centered_point_sq_le n hnpos u hzero i (Finset.mem_range.mp hi))
    unfold squareMass
    calc
      _ ≤ ∑ _i ∈ Finset.range n, (n : Real)*energy n u := h
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

end MathResearchAnalysis.FinitePathPoincare

