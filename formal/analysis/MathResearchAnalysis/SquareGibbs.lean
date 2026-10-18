module

public import MathResearchAnalysis.ZeroTemperature

set_option autoImplicit false

/-!
# Actual finite-square Gibbs energy and one-site heat-bath probability

The interaction counts each interior edge twice and divides by two. Every
missing directional neighbor contributes the fixed spin -1. Boundary counts
are cast to real numbers before subtraction. The local field and logistic
identity follow from this actual energy, without an energy-difference input.
No censoring inequality is asserted here.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace MathResearchAnalysis.SquareGibbs

abbrev Site (n : Nat) := SquareTasks.Vertex n
abbrev Config (n : Nat) := SquareSpin.Config n

def spin (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem spin_true : spin true = 1 := rfl
@[simp] theorem spin_false : spin false = -1 := rfl

theorem spin_eq_bool_count (b : Bool) : spin b = 2 * (b.toNat : ℝ) - 1 := by
  cases b <;> norm_num [spin]

def neighborSum {n : Nat} (f : Config n) (v : Site n) : ℝ :=
  ∑ u ∈ SquareTasks.neighbors n v, spin (f u)

/-- Missing directions are counted in real numbers, without natural subtraction. -/
def boundaryCount {n : Nat} (v : Site n) : ℝ :=
  4 - (SquareTasks.neighbors n v).card

theorem boundaryCount_nonneg {n : Nat} (v : Site n) : 0 ≤ boundaryCount v := by
  have hc := SquareTasks.neighbors_card_le_four n v
  unfold boundaryCount
  exact sub_nonneg.mpr (by exact_mod_cast hc)

def interaction {n : Nat} (f : Config n) : ℝ :=
  ∑ v : Site n, ∑ u ∈ SquareTasks.neighbors n v, spin (f v) * spin (f u)

def boundary {n : Nat} (f : Config n) : ℝ :=
  ∑ v : Site n, boundaryCount v * spin (f v)

/-- Ferromagnetic alignment score with the actual fixed false boundary. -/
def energy {n : Nat} (f : Config n) : ℝ := (1 / 2 : ℝ) * interaction f - boundary f

theorem neighborSum_eq_ones {n : Nat} (f : Config n) (v : Site n) :
    neighborSum f v = 2 * (SquareSpin.ones f v : ℝ) -
      (SquareTasks.neighbors n v).card := by
  simp only [neighborSum, spin_eq_bool_count, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  simp [SquareSpin.ones, Nat.cast_sum]

theorem field_eq_neighbor_boundary {n : Nat} (f : Config n) (v : Site n) :
    ZeroTemperature.field f v = neighborSum f v - boundaryCount v := by
  rw [neighborSum_eq_ones]
  unfold ZeroTemperature.field boundaryCount
  ring

private theorem edge_update_difference {n : Nat} (f : Config n) (v a b : Site n)
    (hab : SquareTasks.Adjacent a b) :
    spin (Function.update f v true a) * spin (Function.update f v true b) -
      spin (Function.update f v false a) * spin (Function.update f v false b) =
        (if a = v then 2 * spin (f b) else 0) +
        (if b = v then 2 * spin (f a) else 0) := by
  have hne : a ≠ b := by
    intro heq
    subst b
    exact SquareTasks.not_adjacent_self n a hab
  by_cases ha : a = v
  · subst a
    have hb : b ≠ v := Ne.symm hne
    simp [Function.update, hb]
    ring
  · by_cases hb : b = v
    · subst b
      simp [Function.update, ha]
      ring
    · simp [Function.update, ha, hb]

/-- Both orientations of every edge give the same one-site interaction change. -/
theorem interaction_update_difference {n : Nat} (f : Config n) (v : Site n) :
    interaction (Function.update f v true) - interaction (Function.update f v false) =
      4 * neighborSum f v := by
  unfold interaction
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  have he : ∑ a : Site n, ∑ b ∈ SquareTasks.neighbors n a,
      (spin (Function.update f v true a) * spin (Function.update f v true b) -
        spin (Function.update f v false a) * spin (Function.update f v false b)) =
      ∑ a : Site n, ∑ b ∈ SquareTasks.neighbors n a,
        ((if a = v then 2 * spin (f b) else 0) +
          (if b = v then 2 * spin (f a) else 0)) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b hb
    exact edge_update_difference f v a b ((SquareTasks.mem_neighbors_iff n a b).mp hb)
  rw [he]
  simp_rw [Finset.sum_add_distrib]
  have hleft : (∑ a : Site n, ∑ b ∈ SquareTasks.neighbors n a,
      if a = v then 2 * spin (f b) else 0) = 2 * neighborSum f v := by
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    exact (Finset.mul_sum _ _ _).symm
  have hright : (∑ a : Site n, ∑ b ∈ SquareTasks.neighbors n a,
      if b = v then 2 * spin (f a) else 0) = 2 * neighborSum f v := by
    simp only [Finset.sum_ite_eq', SquareTasks.neighbors_symmetric n]
    change (∑ a : Site n, if a ∈ SquareTasks.neighbors n v then 2 * spin (f a) else 0) = _
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact (Finset.mul_sum _ _ _).symm
  rw [hleft, hright]
  ring

theorem boundary_update_difference {n : Nat} (f : Config n) (v : Site n) :
    boundary (Function.update f v true) - boundary (Function.update f v false) =
      2 * boundaryCount v := by
  unfold boundary
  rw [← Finset.sum_sub_distrib]
  have he : ∀ a : Site n,
      boundaryCount a * spin (Function.update f v true a) -
        boundaryCount a * spin (Function.update f v false a) =
          if a = v then 2 * boundaryCount v else 0 := by
    intro a
    by_cases ha : a = v <;> simp [Function.update, ha]
    ring
  simp_rw [he]
  simp

/-- The actual energy difference is twice the actual four-input local field. -/
theorem energy_update_difference {n : Nat} (f : Config n) (v : Site n) :
    energy (Function.update f v true) - energy (Function.update f v false) =
      2 * ZeroTemperature.field f v := by
  have hi := interaction_update_difference f v
  have hb := boundary_update_difference f v
  rw [field_eq_neighbor_boundary]
  unfold energy
  linarith

theorem energy_update_difference_eq_ones {n : Nat} (f : Config n) (v : Site n) :
    energy (Function.update f v true) - energy (Function.update f v false) =
      4 * (SquareSpin.ones f v : ℝ) - 8 := by
  rw [energy_update_difference]
  unfold ZeroTemperature.field
  ring

def weight {n : Nat} (β : ℝ) (f : Config n) : ℝ := Real.exp (β * energy f)

theorem weight_pos {n : Nat} (β : ℝ) (f : Config n) : 0 < weight β f := Real.exp_pos _

/-- The conditional probability defined directly from the two actual Gibbs weights. -/
def conditionalTrue {n : Nat} (β : ℝ) (f : Config n) (v : Site n) : ℝ :=
  weight β (Function.update f v true) /
    (weight β (Function.update f v true) + weight β (Function.update f v false))

/-- The weight-based conditional is exactly the existing heat-bath logistic kernel. -/
theorem conditionalTrue_eq_warmProbability {n : Nat} (β : ℝ) (f : Config n)
    (v : Site n) : conditionalTrue β f v =
      ZeroTemperature.warmProbability β (ZeroTemperature.field f v) := by
  have hd := energy_update_difference f v
  have he : Real.exp ((-2 * ZeroTemperature.field f v) * β) =
      weight β (Function.update f v false) / weight β (Function.update f v true) := by
    unfold weight
    rw [← Real.exp_sub]
    congr 1
    rw [← mul_sub]
    have hneg : energy (Function.update f v false) - energy (Function.update f v true) =
        -2 * ZeroTemperature.field f v := by linarith
    rw [hneg]
    ring
  rw [conditionalTrue, ZeroTemperature.warmProbability, he]
  have ht := weight_pos β (Function.update f v true)
  have hf := weight_pos β (Function.update f v false)
  field_simp

end MathResearchAnalysis.SquareGibbs
