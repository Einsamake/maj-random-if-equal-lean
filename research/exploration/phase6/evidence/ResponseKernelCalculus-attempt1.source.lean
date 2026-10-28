module
public import LinearResponseKernel
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.ResponseKernelCalculus
open MeasureTheory Real Set
open MathExploration.LinearResponseKernel

theorem kernel_zero (c : Real) (F : Real → Real) : kernel c F 0=0 := by
  simp [kernel]

theorem kernel_eq_factor (c : Real) (F : Real → Real) (t : Real) :
    kernel c F t=exp (-c*t)*(∫ s in (0 : Real)..t, exp (c*s)*F s) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  change exp (c*(s-t))*F s=exp (-c*t)*(exp (c*s)*F s)
  rw [← mul_assoc, ← exp_add]
  congr 1
  congr 1
  ring

theorem kernel_hasDerivAt (c : Real) (F : Real → Real) (hF : Continuous F) (t : Real) :
    HasDerivAt (kernel c F) (F t-c*kernel c F t) t := by
  have hcf : Continuous (fun s : Real => exp (c*s)*F s) := by
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hF
  have hi := (hcf.integral_hasStrictDerivAt (0 : Real) t).hasDerivAt
  have he : HasDerivAt (fun u : Real => exp (-c*u)) ((-c)*exp (-c*t)) t := by
    simpa only [mul_one] using ((hasDerivAt_id t).const_mul (-c)).exp
  convert he.mul hi using 1
  · funext u
    exact kernel_eq_factor c F u
  · rw [kernel_eq_factor]
    have hcancel : exp (-c*t)*exp (c*t)=1 := by
      rw [← exp_add]
      ring_nf
      exact Real.exp_zero
    calc
      F t-c*(exp (-c*t)*(∫ s in (0 : Real)..t, exp (c*s)*F s))
        = (-c*exp (-c*t))*(∫ s in (0 : Real)..t, exp (c*s)*F s)+
            (exp (-c*t)*exp (c*t))*F t := by rw [hcancel]; ring
      _ = (-c*exp (-c*t))*(∫ s in (0 : Real)..t, exp (c*s)*F s)+
            exp (-c*t)*(exp (c*t)*F t) := by ring

theorem kernel_continuous (c : Real) (F : Real → Real) (hF : Continuous F) :
    Continuous (kernel c F) :=
  continuous_iff_continuousAt.mpr (fun t => (kernel_hasDerivAt c F hF t).continuousAt)

theorem kernel_nonneg (c : Real) (F : Real → Real) (t : Real) (ht : 0≤t)
    (hF : ∀ s : Real, s∈Icc 0 t → 0≤F s) : 0≤kernel c F t := by
  apply intervalIntegral.integral_nonneg ht
  intro s hs
  exact mul_nonneg (exp_pos _).le (hF s hs)

theorem kernel_nonpos (c : Real) (F : Real → Real) (t : Real) (ht : 0≤t)
    (hF : ∀ s : Real, s∈Icc 0 t → F s≤0) : kernel c F t≤0 := by
  have h : 0≤kernel c (fun s => -F s) t :=
    kernel_nonneg c (fun s => -F s) t ht (fun s hs => neg_nonneg.mpr (hF s hs))
  have heq : kernel c (fun s => -F s) t= -(kernel c F t) := by
    unfold kernel
    simp_rw [mul_neg]
    exact intervalIntegral.integral_neg
  rw [heq] at h
  exact neg_nonneg.mp h

end MathExploration.ResponseKernelCalculus
#print axioms MathExploration.ResponseKernelCalculus.kernel_zero
#print axioms MathExploration.ResponseKernelCalculus.kernel_eq_factor
#print axioms MathExploration.ResponseKernelCalculus.kernel_hasDerivAt
#print axioms MathExploration.ResponseKernelCalculus.kernel_continuous
#print axioms MathExploration.ResponseKernelCalculus.kernel_nonneg
#print axioms MathExploration.ResponseKernelCalculus.kernel_nonpos
