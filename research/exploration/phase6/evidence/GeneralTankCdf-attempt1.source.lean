module
public import TankResponse
public import ExponentialCdfConvolution
public import BranchedCdfMixture
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.GeneralTankCdf
open MeasureTheory ProbabilityTheory Set Real
open scoped Topology
open MathExploration.LinearResponseKernel
open MathExploration.ExponentialCdfConvolution
open MathExploration.TankResponse

 theorem cdf_exp_negative (a : Real) (ha : 0<a) (t : Real) (ht : t<0) :
    cdf (expMeasure a) t=0 := by
  rw [cdf_expMeasure_eq ha]
  simp [not_le.mpr ht]

 theorem cdf_exp_eq_x0 (a : Real) (ha : 0<a) (t : Real) (ht : 0≤t) :
    cdf (expMeasure a) t=x0 a t := by
  rw [cdf_expMeasure_eq ha, if_pos ht]
  simp only [x0, neg_mul]

 theorem cdf_middle_negative (a b : Real) (ha : 0<a) (hb : 0<b)
    (t : Real) (ht : t<0) :
    cdf (expMeasure b ∗ expMeasure a) t=0 := by
  letI := isProbabilityMeasure_expMeasure ha
  exact cdf_exp_conv_eq_zero_of_neg b hb (expMeasure a)
    (cdf_exp_negative a ha) t ht

 theorem cdf_middle_eq_x1 (a b : Real) (ha : 0<a) (hb : 0<b)
    (t : Real) (ht : 0≤t) :
    cdf (expMeasure b ∗ expMeasure a) t=x1 a b t := by
  letI := isProbabilityMeasure_expMeasure ha
  rw [cdf_exp_conv_eq_integral b hb (expMeasure a)
    (cdf_exp_negative a ha) t ht, x1, kernel_eq_negative]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  dsimp only
  rw [cdf_exp_eq_x0 a ha s hs.1]
  simp only [neg_mul]
  ring

 theorem cdf_direct_kernel (a c : Real) (ha : 0<a) (hc : 0<c)
    (t : Real) (ht : 0≤t) :
    cdf (expMeasure c ∗ expMeasure a) t=
      kernel c (fun s => c*x0 a s) t := by
  letI := isProbabilityMeasure_expMeasure ha
  rw [cdf_exp_conv_eq_integral c hc (expMeasure a)
    (cdf_exp_negative a ha) t ht, kernel_eq_negative]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  dsimp only
  rw [cdf_exp_eq_x0 a ha s hs.1]
  simp only [neg_mul]
  ring

 theorem cdf_via_kernel (a b c : Real) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (t : Real) (ht : 0≤t) :
    cdf (expMeasure c ∗ (expMeasure b ∗ expMeasure a)) t=
      kernel c (fun s => c*x1 a b s) t := by
  letI := isProbabilityMeasure_expMeasure ha
  letI := isProbabilityMeasure_expMeasure hb
  rw [cdf_exp_conv_eq_integral c hc (expMeasure b ∗ expMeasure a)
    (cdf_middle_negative a b ha hb) t ht, kernel_eq_negative]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  dsimp only
  rw [cdf_middle_eq_x1 a b ha hb s hs.1]
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

 theorem cdf_totalMeasure_negative (a b e f : Real) (ha : 0<a) (hb : 0<b)
    (he : 0≤e) (hf : 0≤f) (hc : 0<e+f) (t : Real) (ht : t<0) :
    cdf (BranchedLaw.totalMeasure a b e f he hf hc) t=0 := by
  letI := isProbabilityMeasure_expMeasure ha
  letI := isProbabilityMeasure_expMeasure hb
  rw [BranchedCdfMixture.cdf_totalMeasure_eq_rates a b e f ha hb he hf hc t,
    cdf_exp_conv_eq_zero_of_neg (e+f) hc (expMeasure a)
      (cdf_exp_negative a ha) t ht,
    cdf_exp_conv_eq_zero_of_neg (e+f) hc (expMeasure b ∗ expMeasure a)
      (cdf_middle_negative a b ha hb) t ht]
  ring

 theorem cdf_totalMeasure_eq_x2 (a b e f : Real) (ha : 0<a) (hb : 0<b)
    (he : 0≤e) (hf : 0≤f) (hc : 0<e+f) (t : Real) (ht : 0≤t) :
    cdf (BranchedLaw.totalMeasure a b e f he hf hc) t=x2 a b e f t := by
  rw [BranchedCdfMixture.cdf_totalMeasure_eq_rates a b e f ha hb he hf hc t,
    cdf_direct_kernel a (e+f) ha hc t ht,
    cdf_via_kernel a b (e+f) ha hb hc t ht,
    weighted_kernels (e+f) e f hc (x0 a) (x1 a b)
      (x0_continuous a) (x1_continuous a b)]
  rfl

 theorem cdf_totalMeasure_eq_x2_all_real (a b e f : Real) (ha : 0<a) (hb : 0<b)
    (he : 0≤e) (hf : 0≤f) (hc : 0<e+f) (t : Real) :
    cdf (BranchedLaw.totalMeasure a b e f he hf hc) t=
      if 0≤t then x2 a b e f t else 0 := by
  by_cases ht : 0≤t
  · rw [if_pos ht]
    exact cdf_totalMeasure_eq_x2 a b e f ha hb he hf hc t ht
  · rw [if_neg ht]
    exact cdf_totalMeasure_negative a b e f ha hb he hf hc t (lt_of_not_ge ht)

 theorem cdf_totalMeasure_hasDerivAt_of_pos (a b e f : Real) (ha : 0<a) (hb : 0<b)
    (he : 0≤e) (hf : 0≤f) (hc : 0<e+f) (t : Real) (ht : 0<t) :
    HasDerivAt (cdf (BranchedLaw.totalMeasure a b e f he hf hc))
      (e*x0 a t+f*x1 a b t-
        (e+f)*cdf (BranchedLaw.totalMeasure a b e f he hf hc) t) t := by
  have hlocal : cdf (BranchedLaw.totalMeasure a b e f he hf hc) =ᶠ[𝓝 t]
      x2 a b e f := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact cdf_totalMeasure_eq_x2 a b e f ha hb he hf hc s hs.le
  have hd := (x2_hasDerivAt a b e f t).congr_of_eventuallyEq hlocal
  apply hd.congr_deriv
  rw [cdf_totalMeasure_eq_x2 a b e f ha hb he hf hc t ht.le]
  ring
 theorem total_event_eq_cdf (a b e f : Real) (ha : 0<a) (hb : 0<b)
    (he : 0≤e) (hf : 0≤f) (hc : 0<e+f) (t : Real) :
    (BranchedLaw.law a b e f he hf hc).real {ω | BranchedLaw.total ω≤t}=
      cdf (BranchedLaw.totalMeasure a b e f he hf hc) t := by
  letI := BranchedLaw.totalMeasure_probability a b e f ha hb he hf hc
  rw [cdf_eq_real]
  change _=((BranchedLaw.law a b e f he hf hc).map BranchedLaw.total).real (Iic t)
  rw [map_measureReal_apply BranchedLaw.total_measurable measurableSet_Iic]
  rfl

 theorem total_event_eq_x2 (a b e f : Real) (ha : 0<a) (hb : 0<b)
    (he : 0≤e) (hf : 0≤f) (hc : 0<e+f) (t : Real) (ht : 0≤t) :
    (BranchedLaw.law a b e f he hf hc).real {ω | BranchedLaw.total ω≤t}=
      x2 a b e f t := by
  rw [total_event_eq_cdf a b e f ha hb he hf hc,
    cdf_totalMeasure_eq_x2 a b e f ha hb he hf hc t ht]

 theorem total_event_eq_x2_all_real (a b e f : Real) (ha : 0<a) (hb : 0<b)
    (he : 0≤e) (hf : 0≤f) (hc : 0<e+f) (t : Real) :
    (BranchedLaw.law a b e f he hf hc).real {ω | BranchedLaw.total ω≤t}=
      if 0≤t then x2 a b e f t else 0 := by
  rw [total_event_eq_cdf a b e f ha hb he hf hc,
    cdf_totalMeasure_eq_x2_all_real a b e f ha hb he hf hc t]

end MathExploration.GeneralTankCdf

#print axioms MathExploration.GeneralTankCdf.cdf_exp_negative
#print axioms MathExploration.GeneralTankCdf.cdf_exp_eq_x0
#print axioms MathExploration.GeneralTankCdf.cdf_middle_negative
#print axioms MathExploration.GeneralTankCdf.cdf_middle_eq_x1
#print axioms MathExploration.GeneralTankCdf.cdf_direct_kernel
#print axioms MathExploration.GeneralTankCdf.cdf_via_kernel
#print axioms MathExploration.GeneralTankCdf.weighted_kernels
#print axioms MathExploration.GeneralTankCdf.cdf_totalMeasure_negative
#print axioms MathExploration.GeneralTankCdf.cdf_totalMeasure_eq_x2
#print axioms MathExploration.GeneralTankCdf.cdf_totalMeasure_eq_x2_all_real
#print axioms MathExploration.GeneralTankCdf.cdf_totalMeasure_hasDerivAt_of_pos
#print axioms MathExploration.GeneralTankCdf.total_event_eq_cdf
#print axioms MathExploration.GeneralTankCdf.total_event_eq_x2
#print axioms MathExploration.GeneralTankCdf.total_event_eq_x2_all_real
