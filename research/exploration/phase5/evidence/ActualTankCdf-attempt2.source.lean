module
public import LinearResponseKernel
public import ExponentialCdfConvolution
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.ActualTankCdf
open MeasureTheory ProbabilityTheory Set Real
open MathExploration.LinearResponseKernel
open MathExploration.ExponentialCdfConvolution
open MathExploration.ConstantInletCounterexample

 theorem cdf_exp_one_negative (t : Real) (ht : t<0) :
    cdf (expMeasure 1) t=0 := by
  rw [cdf_expMeasure_eq (by norm_num : (0 : Real)<1)]
  simp [not_le.mpr ht]

 theorem cdf_exp_one_nonnegative (t : Real) (ht : 0≤t) :
    cdf (expMeasure 1) t=lowState t 0 := by
  rw [cdf_expMeasure_eq (by norm_num : (0 : Real)<1), if_pos ht, low_zero_exp]
  simp

 theorem cdf_middle_negative (t : Real) (ht : t<0) :
    cdf (expMeasure (1/2) ∗ expMeasure 1) t=0 := by
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0 : Real)<1)
  exact cdf_exp_conv_eq_zero_of_neg (1/2) (by norm_num)
    (expMeasure 1) cdf_exp_one_negative t ht

 theorem cdf_middle_low (t : Real) (ht : 0≤t) :
    cdf (expMeasure (1/2) ∗ expMeasure 1) t=lowState t 1 := by
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0 : Real)<1)
  rw [cdf_exp_conv_eq_integral (1/2) (by norm_num) (expMeasure 1)
    cdf_exp_one_negative t ht, low_middle_kernel, kernel_eq_negative]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  dsimp only
  rw [cdf_exp_one_nonnegative s hs.1]
  simp only [neg_mul]
  ring

 theorem cdf_direct_kernel (c : Real) (hc : 0<c) (t : Real) (ht : 0≤t) :
    cdf (expMeasure c ∗ expMeasure 1) t=
      kernel c (fun s => c*lowState s 0) t := by
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0 : Real)<1)
  rw [cdf_exp_conv_eq_integral c hc (expMeasure 1)
    cdf_exp_one_negative t ht, kernel_eq_negative]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  dsimp only
  rw [cdf_exp_one_nonnegative s hs.1]
  simp only [neg_mul]
  ring

 theorem cdf_via_kernel (c : Real) (hc : 0<c) (t : Real) (ht : 0≤t) :
    cdf (expMeasure c ∗ (expMeasure (1/2) ∗ expMeasure 1)) t=
      kernel c (fun s => c*lowState s 1) t := by
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0 : Real)<1)
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0 : Real)<1/2)
  rw [cdf_exp_conv_eq_integral c hc (expMeasure (1/2) ∗ expMeasure 1)
    cdf_middle_negative t ht, kernel_eq_negative]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  dsimp only
  rw [cdf_middle_low s hs.1]
  simp only [neg_mul]
  ring

 theorem weighted_kernels (c e f : Real) (hc : 0<c) (F G : Real → Real)
    (hF : Continuous F) (hG : Continuous G) (t : Real) :
    (e/c)*kernel c (fun s => c*F s) t+
      (f/c)*kernel c (fun s => c*G s) t=
      kernel c (fun s => e*F s+f*G s) t := by
  have hI1 : IntervalIntegrable
      (fun s : Real => (e/c)*(exp (c*(s-t))*(c*F s))) volume 0 t := by
    have hct : Continuous (fun s : Real => (e/c)*(exp (c*(s-t))*(c*F s))) := by
      fun_prop
    exact hct.intervalIntegrable 0 t
  have hI2 : IntervalIntegrable
      (fun s : Real => (f/c)*(exp (c*(s-t))*(c*G s))) volume 0 t := by
    have hct : Continuous (fun s : Real => (f/c)*(exp (c*(s-t))*(c*G s))) := by
      fun_prop
    exact hct.intervalIntegrable 0 t
  unfold kernel
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add hI1 hI2]
  apply intervalIntegral.integral_congr
  intro s _
  field_simp [ne_of_gt hc]
  <;> ring

 theorem low_mixture_is_outlet (t : Real) (ht : 0≤t) :
    (2/(5/2 : Real))*cdf (expMeasure (5/2) ∗ expMeasure 1) t+
      ((1/2)/(5/2 : Real))*
        cdf (expMeasure (5/2) ∗ (expMeasure (1/2) ∗ expMeasure 1)) t=
      lowState t 2 := by
  rw [cdf_direct_kernel (5/2) (by norm_num) t ht,
    cdf_via_kernel (5/2) (by norm_num) t ht,
    weighted_kernels (5/2) 2 (1/2) (by norm_num)
      (fun s => lowState s 0) (fun s => lowState s 1)
      (low_continuous 0) (low_continuous 1), low_outlet_kernel]

 theorem high_mixture_is_outlet (t : Real) (ht : 0≤t) :
    (2/3 : Real)*cdf (expMeasure 3 ∗ expMeasure 1) t+
      (1/3 : Real)*cdf (expMeasure 3 ∗ (expMeasure (1/2) ∗ expMeasure 1)) t=
      highState t 2 := by
  rw [cdf_direct_kernel 3 (by norm_num) t ht,
    cdf_via_kernel 3 (by norm_num) t ht,
    weighted_kernels 3 2 1 (by norm_num)
      (fun s => lowState s 0) (fun s => lowState s 1)
      (low_continuous 0) (low_continuous 1), high_outlet_kernel]
  congr 1
  funext s
  rw [(same_upstream s).1, (same_upstream s).2]
  ring

end MathExploration.ActualTankCdf

#print axioms MathExploration.ActualTankCdf.cdf_exp_one_negative
#print axioms MathExploration.ActualTankCdf.cdf_exp_one_nonnegative
#print axioms MathExploration.ActualTankCdf.cdf_middle_negative
#print axioms MathExploration.ActualTankCdf.cdf_middle_low
#print axioms MathExploration.ActualTankCdf.cdf_direct_kernel
#print axioms MathExploration.ActualTankCdf.cdf_via_kernel
#print axioms MathExploration.ActualTankCdf.weighted_kernels
#print axioms MathExploration.ActualTankCdf.low_mixture_is_outlet
#print axioms MathExploration.ActualTankCdf.high_mixture_is_outlet

