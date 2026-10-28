module
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.ExponentialMean
open MeasureTheory ProbabilityTheory Real Set

theorem weighted_density_eq (r : ℝ) (hr : 0 < r) :
    (fun x : ℝ => (exponentialPDF r x).toReal * x) =
      (fun x : ℝ => (1 / r) * (gammaPDF 2 r x).toReal) := by
  funext x
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx, gammaPDF_of_nonneg hx]
    norm_num only [Real.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num,
      Real.rpow_one, Real.Gamma_ofNat_eq_factorial, Nat.factorial_one,
      Nat.cast_one, div_one]
    rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
    field_simp [ne_of_gt hr]
  · simp [exponentialPDF_of_neg (lt_of_not_ge hx),
      gammaPDF_of_neg (lt_of_not_ge hx)]

theorem gamma_density_integrable (r : ℝ) (hr : 0 < r) :
    Integrable (fun x : ℝ => (gammaPDF 2 r x).toReal) volume := by
  apply integrable_toReal_of_lintegral_ne_top
    (measurable_gammaPDFReal 2 r).ennreal_ofReal.aemeasurable
  rw [lintegral_gammaPDF_eq_one (by norm_num) hr]
  exact ENNReal.one_ne_top

theorem gamma_density_integral (r : ℝ) (hr : 0 < r) :
    (∫ x : ℝ, (gammaPDF 2 r x).toReal) = 1 := by
  rw [integral_toReal (measurable_gammaPDFReal 2 r).ennreal_ofReal.aemeasurable
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  rw [lintegral_gammaPDF_eq_one (by norm_num) hr]
  simp

theorem integrable_id (r : ℝ) (hr : 0 < r) :
    Integrable id (expMeasure r) := by
  change Integrable (fun x : ℝ => x) (volume.withDensity (exponentialPDF r))
  rw [integrable_withDensity_iff_integrable_smul' (f := exponentialPDF r)
    (measurable_exponentialPDFReal r).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul]
  rw [weighted_density_eq r hr]
  exact (gamma_density_integrable r hr).const_mul (1 / r)

theorem integral_id (r : ℝ) (hr : 0 < r) :
    (∫ x : ℝ, x ∂expMeasure r) = 1 / r := by
  change (∫ x : ℝ, x ∂volume.withDensity (exponentialPDF r)) = _
  rw [integral_withDensity_eq_integral_toReal_smul (f := exponentialPDF r)
    (measurable_exponentialPDFReal r).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul]
  rw [weighted_density_eq r hr, integral_const_mul, gamma_density_integral r hr, mul_one]

end MathExploration.ExponentialMean
#print axioms MathExploration.ExponentialMean.weighted_density_eq
#print axioms MathExploration.ExponentialMean.gamma_density_integrable
#print axioms MathExploration.ExponentialMean.gamma_density_integral
#print axioms MathExploration.ExponentialMean.integrable_id
#print axioms MathExploration.ExponentialMean.integral_id
