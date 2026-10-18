module

public import MathResearchAnalysis.SquareGibbsLaw

set_option autoImplicit false

/-!
# Actual finite-square mass evolution and Gibbs densities

Finite sums identify forward heat-bath mass evolution with the existing
backward heat-bath operators. Detailed balance identifies the evolved density
relative to the actual positive Gibbs mass. This module does not assume a
censoring inequality.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace MathResearchAnalysis.SquarePWMeasure

abbrev Config (n : Nat) := SquareSpin.Config n
abbrev Site (n : Nat) := SquareTasks.Vertex n

def expect {n : Nat} (ρ : Config n → ℝ) (φ : Config n → ℝ) : ℝ :=
  ∑ f, ρ f * φ f

def step {n : Nat} (β : ℝ) (v : Site n) (ρ : Config n → ℝ) (g : Config n) : ℝ :=
  ∑ f, ρ f * SquareGibbsLaw.kernel β v f g

def density {n : Nat} (β : ℝ) (ρ : Config n → ℝ) (f : Config n) : ℝ :=
  ρ f / SquareGibbsLaw.mass β f

def topConfig (n : Nat) : Config n := fun _ => true

def topMass (n : Nat) (f : Config n) : ℝ := by
  classical
  exact if f = topConfig n then 1 else 0

def runMass {n : Nat} (β : ℝ) : List (Site n) → (Config n → ℝ) → Config n → ℝ
  | [], ρ => ρ
  | v :: rest, ρ => runMass β rest (step β v ρ)

theorem kernel_expect {n : Nat} (β : ℝ) (v : Site n) (φ : Config n → ℝ)
    (f : Config n) :
    (∑ g, SquareGibbsLaw.kernel β v f g * φ g) =
      ZeroTemperature.warmStep β v φ f := by
  classical
  simp [SquareGibbsLaw.kernel_eq_warmProbability, ZeroTemperature.warmStep,
    add_mul, mul_ite, ite_mul, Finset.sum_add_distrib]

theorem expect_step {n : Nat} (β : ℝ) (v : Site n) (ρ φ : Config n → ℝ) :
    expect (step β v ρ) φ = expect ρ (ZeroTemperature.warmStep β v φ) := by
  unfold expect step
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  rw [← Finset.mul_sum, kernel_expect]

/-- Reversibility identifies the density evolution without a density-law premise. -/
theorem density_step {n : Nat} (β : ℝ) (v : Site n) (ρ : Config n → ℝ)
    (g : Config n) :
    density β (step β v ρ) g =
      ZeroTemperature.warmStep β v (density β ρ) g := by
  rw [← kernel_expect]
  unfold density step
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro f _
  have hf := ne_of_gt (SquareGibbsLaw.mass_pos β f)
  have hg := ne_of_gt (SquareGibbsLaw.mass_pos β g)
  have hb := congrArg (fun z : ℝ => ρ f * z)
    (SquareGibbsLaw.detailed_balance β v f g)
  field_simp [hf, hg]
  nlinarith [hb]

theorem expect_topMass (n : Nat) (φ : Config n → ℝ) :
    expect (topMass n) φ = φ (topConfig n) := by
  classical
  simp [expect, topMass, ite_mul]

theorem topMass_nonneg (n : Nat) (f : Config n) : 0 ≤ topMass n f := by
  classical
  simp only [topMass]
  split_ifs <;> norm_num

theorem sum_topMass (n : Nat) : (∑ f, topMass n f) = 1 := by
  classical
  simp [topMass]

theorem topMass_density_monotone (n : Nat) (β : ℝ) :
    Monotone (density β (topMass n)) := by
  classical
  intro f g hfg
  by_cases hf : f = topConfig n
  · have hg : g = topConfig n := by
      apply le_antisymm
      · intro v
        simp [topConfig]
      · simpa [hf] using hfg
    subst f
    subst g
    exact le_rfl
  · by_cases hg : g = topConfig n
    · simp only [density, topMass, ite_eq_right hf, ite_eq_left hg, zero_div]
      exact (div_pos zero_lt_one (SquareGibbsLaw.mass_pos β g)).le
    · simp only [density, topMass, ite_eq_right hf, ite_eq_right hg, zero_div, le_refl]

theorem step_nonneg {n : Nat} (β : ℝ) (v : Site n) (ρ : Config n → ℝ)
    (hρ : ∀ f, 0 ≤ ρ f) (g : Config n) : 0 ≤ step β v ρ g := by
  exact Finset.sum_nonneg (fun f _ => mul_nonneg (hρ f)
    (SquareGibbsLaw.kernel_nonneg β v f g))

theorem sum_step {n : Nat} (β : ℝ) (v : Site n) (ρ : Config n → ℝ) :
    (∑ g, step β v ρ g) = ∑ f, ρ f := by
  unfold step
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, SquareGibbsLaw.kernel_sum_one, mul_one]

theorem expect_runMass {n : Nat} (β : ℝ) (word : List (Site n))
    (ρ φ : Config n → ℝ) :
    expect (runMass β word ρ) φ = expect ρ (ZeroTemperature.warmWord β word φ) := by
  induction word generalizing ρ with
  | nil => rfl
  | cons v rest ih =>
    rw [runMass, ih, expect_step]
    rfl

end MathResearchAnalysis.SquarePWMeasure
