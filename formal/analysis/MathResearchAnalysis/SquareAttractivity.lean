module

public import MathResearchAnalysis.SquareGibbsLaw

set_option autoImplicit false

/-!
# Attractivity of the actual finite-temperature square heat-bath kernels

The field uses the four fixed-zero boundary inputs of `SquareSpin`. For
nonnegative inverse temperature the genuine logistic update preserves monotone
test functions. Pointwise order between arbitrary real test functions is
preserved at every real temperature, since both heat-bath weights are positive.
These are local kernel facts; no censoring inequality is asserted here.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.SquareAttractivity

abbrev Config (n : ℕ) := SquareSpin.Config n
abbrev Site (n : ℕ) := SquareTasks.Vertex n

theorem field_mono {n : ℕ} {f g : Config n} (h : f ≤ g) (v : Site n) :
    ZeroTemperature.field f v ≤ ZeroTemperature.field g v := by
  have hones : (SquareSpin.ones f v : ℝ) ≤ (SquareSpin.ones g v : ℝ) := by
    exact_mod_cast SquareSpin.ones_mono h v
  unfold ZeroTemperature.field
  linarith

theorem warmProbability_mono (β : ℝ) (hβ : 0 ≤ β) :
    Monotone (ZeroTemperature.warmProbability β) := by
  intro a b hab
  unfold ZeroTemperature.warmProbability
  apply inv_anti₀ (by positivity)
  exact add_le_add le_rfl (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (by linarith : -2 * b ≤ -2 * a) hβ))

theorem warmProbability_config_mono {n : ℕ} (β : ℝ) (hβ : 0 ≤ β) (v : Site n) :
    Monotone (fun f : Config n =>
      ZeroTemperature.warmProbability β (ZeroTemperature.field f v)) := by
  intro f g hfg
  exact warmProbability_mono β hβ (field_mono hfg v)

/-- Pointwise order in the test function, without any monotonicity assumption. -/
theorem warmStep_mono {n : ℕ} (β : ℝ) (v : Site n)
    {φ ψ : Config n → ℝ} (h : φ ≤ ψ) :
    ZeroTemperature.warmStep β v φ ≤ ZeroTemperature.warmStep β v ψ := by
  intro f
  unfold ZeroTemperature.warmStep
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (h _) (ZeroTemperature.warmProbability_pos _ _).le
  · exact mul_le_mul_of_nonneg_left (h _)
      (sub_nonneg.mpr (ZeroTemperature.warmProbability_lt_one _ _).le)

/-- The actual one-site heat bath is attractive when the inverse temperature is nonnegative. -/
theorem warmStep_monotone {n : ℕ} (β : ℝ) (hβ : 0 ≤ β) (v : Site n)
    {φ : Config n → ℝ} (hφ : Monotone φ) :
    Monotone (ZeroTemperature.warmStep β v φ) := by
  intro f g hfg
  have hup : φ (Function.update f v true) ≤ φ (Function.update g v true) :=
    hφ (update_le_update_iff.mpr ⟨le_rfl, fun u _ => hfg u⟩)
  have hdown : φ (Function.update f v false) ≤ φ (Function.update g v false) :=
    hφ (update_le_update_iff.mpr ⟨le_rfl, fun u _ => hfg u⟩)
  have hdu : φ (Function.update g v false) ≤ φ (Function.update g v true) :=
    hφ (update_le_update_iff'.mpr (by decide))
  have hp := (ZeroTemperature.warmProbability_pos β (ZeroTemperature.field f v)).le
  have hpc := sub_nonneg.mpr
    (ZeroTemperature.warmProbability_lt_one β (ZeroTemperature.field f v)).le
  have hpq := warmProbability_config_mono β hβ v hfg
  unfold ZeroTemperature.warmStep
  calc
    _ ≤ ZeroTemperature.warmProbability β (ZeroTemperature.field f v) *
          φ (Function.update g v true) +
        (1 - ZeroTemperature.warmProbability β (ZeroTemperature.field f v)) *
          φ (Function.update g v false) :=
      add_le_add (mul_le_mul_of_nonneg_left hup hp) (mul_le_mul_of_nonneg_left hdown hpc)
    _ ≤ _ := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hdu)]

/-- Every genuine finite heat-bath word preserves pointwise order of real tests. -/
theorem warmWord_mono {n : ℕ} (β : ℝ) (word : List (Site n))
    {φ ψ : Config n → ℝ} (h : φ ≤ ψ) :
    ZeroTemperature.warmWord β word φ ≤ ZeroTemperature.warmWord β word ψ := by
  induction word with
  | nil => exact h
  | cons v rest ih =>
    exact warmStep_mono β v ih

/-- At nonnegative inverse temperature, every genuine finite word is attractive. -/
theorem warmWord_monotone {n : ℕ} (β : ℝ) (hβ : 0 ≤ β) (word : List (Site n))
    {φ : Config n → ℝ} (hφ : Monotone φ) :
    Monotone (ZeroTemperature.warmWord β word φ) := by
  induction word with
  | nil => exact hφ
  | cons v rest ih => exact warmStep_monotone β hβ v ih

end MathResearchAnalysis.SquareAttractivity
