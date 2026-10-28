module
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.ExponentialCdfConvolution
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- This identity comes from the product-measure convolution and a bounded event indicator. -/
theorem cdf_conv_eq_integral (nu mu : Measure Real)
    [IsProbabilityMeasure nu] [IsProbabilityMeasure mu] (t : Real) :
    cdf (nu ∗ mu) t = ∫ u, cdf mu (t-u) ∂ nu := by
  have hint : Integrable ((Iic t).indicator (1 : Real → Real)) (nu ∗ mu) :=
    (integrable_const (1 : Real)).indicator measurableSet_Iic
  rw [cdf_eq_real, ← integral_indicator_one measurableSet_Iic,
    integral_conv (μ := nu) (ν := mu) hint]
  congr 1
  funext u
  have hfun : (fun y : Real => (Iic t).indicator (1 : Real → Real) (u+y)) =
      (Iic (t-u)).indicator (1 : Real → Real) := by
    funext y
    by_cases hy : y ≤ t-u
    · have hsum : u+y ≤ t := by linarith
      simp [indicator_of_mem, hy, hsum]
    · have hsum : ¬ u+y ≤ t := by linarith
      simp [indicator_of_notMem, hy, hsum]
  rw [hfun, integral_indicator_one, ← cdf_eq_real]

/-- The actual CDF of an independent exponential convolution, with the clock as variable. -/
theorem cdf_exp_conv_eq_integral_clock (c : Real) (hc : 0<c) (mu : Measure Real)
    [IsProbabilityMeasure mu] (hneg : ∀ x : Real, x<0 → cdf mu x=0)
    (t : Real) (ht : 0≤ t) :
    cdf (expMeasure c ∗ mu) t =
      ∫ u in 0..t, c*Real.exp (-(c*u))*cdf mu (t-u) := by
  letI : IsProbabilityMeasure (expMeasure c) := isProbabilityMeasure_expMeasure hc
  rw [cdf_conv_eq_integral]
  change (∫ u : Real, cdf mu (t-u) ∂ volume.withDensity (exponentialPDF c)) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := exponentialPDF c) ((measurable_exponentialPDFReal c).ennreal_ofReal)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul]
  have hfun : (fun u : Real => (exponentialPDF c u).toReal*cdf mu (t-u)) =
      (Icc 0 t).indicator (fun u => c*Real.exp (-(c*u))*cdf mu (t-u)) := by
    funext u
    by_cases hu : 0≤ u
    · by_cases hut : u≤ t
      · rw [indicator_of_mem (show u ∈ Icc 0 t from ⟨hu,hut⟩),
          exponentialPDF_of_nonneg hu, ENNReal.toReal_ofReal]
        exact mul_nonneg hc.le (Real.exp_pos _).le
      · have htu : t-u<0 := by linarith
        rw [indicator_of_notMem (show u ∉ Icc 0 t from fun h => hut h.2),
          hneg (t-u) htu]
        simp
    · rw [exponentialPDF_of_neg (lt_of_not_ge hu)]
      simp [indicator_of_notMem (show u ∉ Icc 0 t from fun h => hu h.1)]
  rw [hfun, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht]

/-- The same probability identity in the usual response-kernel order. -/
theorem cdf_exp_conv_eq_integral (c : Real) (hc : 0<c) (mu : Measure Real)
    [IsProbabilityMeasure mu] (hneg : ∀ x : Real, x<0 → cdf mu x=0)
    (t : Real) (ht : 0≤ t) :
    cdf (expMeasure c ∗ mu) t =
      ∫ s in 0..t, c*Real.exp (-(c*(t-s)))*cdf mu s := by
  rw [cdf_exp_conv_eq_integral_clock c hc mu hneg t ht]
  simpa using (intervalIntegral.integral_comp_sub_left
    (fun u : Real => c*Real.exp (-(c*u))*cdf mu (t-u)) (a := 0) (b := t) t).symm

end MathExploration.ExponentialCdfConvolution

#print axioms MathExploration.ExponentialCdfConvolution.cdf_conv_eq_integral
#print axioms MathExploration.ExponentialCdfConvolution.cdf_exp_conv_eq_integral_clock
#print axioms MathExploration.ExponentialCdfConvolution.cdf_exp_conv_eq_integral
