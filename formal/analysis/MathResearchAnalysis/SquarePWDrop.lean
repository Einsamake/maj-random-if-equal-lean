module

public import MathResearchAnalysis.SquarePWMeasure

set_option autoImplicit false

/-!
# A single actual heat-bath update decreases increasing expectations

The reference law is the positive finite-square Gibbs mass, and the transition
is the actual single-site Gibbs kernel. Detailed balance gives a finite
Dirichlet identity. Every supported transition changes only one Boolean site,
so its two endpoint configurations are comparable in the pointwise order.
Consequently an increasing Gibbs density decreases every increasing test
expectation after one update. No censoring inequality is an input, and the
single-update statement does not require the inverse temperature to be
nonnegative.
-/

@[expose] public noncomputable section

open scoped BigOperators
open MathResearchAnalysis.SquarePWMeasure

namespace MathResearchAnalysis.SquarePWDrop

abbrev Config (n : Nat) := SquareSpin.Config n
abbrev Site (n : Nat) := SquareTasks.Vertex n

/-- Configurations agreeing away from one Boolean site are comparable. -/
theorem sameOutside_comparable {n : Nat} {v : Site n} {f g : Config n}
    (h : SquareGibbsLaw.SameOutside v f g) : f ≤ g ∨ g ≤ f := by
  rcases le_total (f v) (g v) with hfg | hgf
  · left
    intro u
    by_cases hu : u = v
    · simpa only [hu] using hfg
    · exact le_of_eq (h u hu)
  · right
    intro u
    by_cases hu : u = v
    · simpa only [hu] using hgf
    · exact le_of_eq (h u hu).symm

private theorem mass_mul_density {n : Nat} (β : ℝ) (ρ : Config n → ℝ)
    (f : Config n) : SquareGibbsLaw.mass β f * density β ρ f = ρ f := by
  unfold density
  exact mul_div_cancel₀ _ (ne_of_gt (SquareGibbsLaw.mass_pos β f))

/-- The reversible pair identity for the actual square Gibbs kernel. -/
theorem pairwise_dirichlet_identity {n : Nat} (β : ℝ) (v : Site n)
    (ρ φ : Config n → ℝ) (f g : Config n) :
    ρ f * SquareGibbsLaw.kernel β v f g * (φ f - φ g) +
        ρ g * SquareGibbsLaw.kernel β v g f * (φ g - φ f) =
      SquareGibbsLaw.mass β f * SquareGibbsLaw.kernel β v f g *
        (density β ρ f - density β ρ g) * (φ f - φ g) := by
  calc
    _ = (SquareGibbsLaw.mass β f * SquareGibbsLaw.kernel β v f g) *
            density β ρ f * (φ f - φ g) +
          (SquareGibbsLaw.mass β g * SquareGibbsLaw.kernel β v g f) *
            density β ρ g * (φ g - φ f) := by
      rw [← mass_mul_density β ρ f, ← mass_mul_density β ρ g]
      ring
    _ = _ := by
      rw [← SquareGibbsLaw.detailed_balance β v f g]
      ring

/-- The expectation loss as an ordered sum over actual one-site transitions. -/
theorem expect_sub_expect_step_eq_sum {n : Nat} (β : ℝ) (v : Site n)
    (ρ φ : Config n → ℝ) :
    expect ρ φ - expect (step β v ρ) φ =
      ∑ f : Config n, ∑ g : Config n,
        ρ f * SquareGibbsLaw.kernel β v f g * (φ f - φ g) := by
  classical
  unfold expect step
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro f _
  calc
    _ = (∑ g : Config n, ρ f * SquareGibbsLaw.kernel β v f g * φ f) -
        ∑ g : Config n, ρ f * SquareGibbsLaw.kernel β v f g * φ g := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, SquareGibbsLaw.kernel_sum_one]
      simp
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro g _
      ring

/-- The exact finite Dirichlet identity, without any order assumptions. -/
theorem dirichlet_identity {n : Nat} (β : ℝ) (v : Site n)
    (ρ φ : Config n → ℝ) :
    2 * (expect ρ φ - expect (step β v ρ) φ) =
      ∑ f : Config n, ∑ g : Config n,
        SquareGibbsLaw.mass β f * SquareGibbsLaw.kernel β v f g *
          (density β ρ f - density β ρ g) * (φ f - φ g) := by
  classical
  rw [expect_sub_expect_step_eq_sum]
  simp_rw [← pairwise_dirichlet_identity, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun f g =>
    ρ g * SquareGibbsLaw.kernel β v g f * (φ g - φ f))]
  ring

/-- With increasing Gibbs density, one actual site update decreases every
increasing expectation. This is the single-update deletion inequality. -/
theorem expect_step_le_expect {n : Nat} (β : ℝ) (v : Site n)
    (ρ : Config n → ℝ) (hd : Monotone (density β ρ))
    (φ : Config n → ℝ) (hφ : Monotone φ) :
    expect (step β v ρ) φ ≤ expect ρ φ := by
  classical
  have hsum : 0 ≤ ∑ f : Config n, ∑ g : Config n,
      SquareGibbsLaw.mass β f * SquareGibbsLaw.kernel β v f g *
        (density β ρ f - density β ρ g) * (φ f - φ g) := by
    apply Finset.sum_nonneg
    intro f _
    apply Finset.sum_nonneg
    intro g _
    by_cases h : SquareGibbsLaw.SameOutside v f g
    · have hproduct : 0 ≤ (density β ρ f - density β ρ g) * (φ f - φ g) := by
        rcases sameOutside_comparable h with hfg | hgf
        · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hd hfg))
            (sub_nonpos.mpr (hφ hfg))
        · exact mul_nonneg (sub_nonneg.mpr (hd hgf))
            (sub_nonneg.mpr (hφ hgf))
      rw [mul_assoc]
      exact mul_nonneg (mul_nonneg (SquareGibbsLaw.mass_nonneg β f)
        (SquareGibbsLaw.kernel_nonneg β v f g)) hproduct
    · simp only [SquareGibbsLaw.kernel, ite_eq_right h, mul_zero, zero_mul, le_refl]
  rw [← dirichlet_identity] at hsum
  linarith

end MathResearchAnalysis.SquarePWDrop
