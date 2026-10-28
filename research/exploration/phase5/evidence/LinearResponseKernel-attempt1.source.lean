module
public import ConstantInletCounterexample
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.LinearResponseKernel
open MeasureTheory Set Real
open MathExploration.RobustNetworkBounds MathExploration.RobustTankCertificate
open MathExploration.ConstantInletCounterexample

def kernel (c : Real) (F : Real → Real) (t : Real) : Real :=
  ∫ s in (0 : Real)..t, exp (c*(s-t))*F s

theorem ode_to_kernel (c : Real) (Y F : Real → Real)
    (hF : Continuous F) (hz : Y 0=0)
    (hd : ∀ s, HasDerivAt Y (F s-c*Y s) s) (t : Real) :
    Y t=kernel c F t := by
  have hE (s : Real) : HasDerivAt (fun u : Real => exp (c*(u-t)))
      (c*exp (c*(s-t))) s := by
    simpa only [id_eq,one_mul,mul_one,mul_comm] using
      (((hasDerivAt_id s).sub_const t).const_mul c).exp
  have hG (s : Real) : HasDerivAt (fun u : Real => exp (c*(u-t))*Y u)
      (exp (c*(s-t))*F s) s := by
    convert (hE s).mul (hd s) using 1
    ring
  have hI : IntervalIntegrable (fun s : Real => exp (c*(s-t))*F s) volume 0 t :=
    (((continuous_const.mul (continuous_id.sub continuous_const)).exp).mul hF).intervalIntegrable 0 t
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : Real)) (b := t) (fun s _ => hG s) hI
  simpa [kernel,hz] using h.symm

theorem kernel_eq_negative (c : Real) (F : Real → Real) (t : Real) :
    kernel c F t=∫ s in (0 : Real)..t, exp (-c*(t-s))*F s := by
  apply intervalIntegral.integral_congr
  intro s _
  congr 1
  congr 1
  ring

theorem low_continuous (i : Fin 3) : Continuous (fun t => lowState t i) :=
  continuous_iff_continuousAt.mpr (fun t => (lowState_hasDerivAt t i).continuousAt)

theorem high_continuous (i : Fin 3) : Continuous (fun t => highState t i) :=
  continuous_iff_continuousAt.mpr (fun t => (highState_hasDerivAt t i).continuousAt)

theorem low_zero_exp (t : Real) : lowState t 0=1-exp (-t) := by
  change 1-(r t)^2=1-exp (-t)
  congr 1
  unfold r
  rw [← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

theorem high_zero_exp (t : Real) : highState t 0=1-exp (-t) := by
  rw [← (same_upstream t).1]
  exact low_zero_exp t

theorem low_middle_kernel (t : Real) :
    lowState t 1=kernel (1/2) (fun s => (1/2 : Real)*lowState s 0) t := by
  apply ode_to_kernel (1/2) _ _ ((low_continuous 0).const_mul _) (lowState_zero 1)
  intro s
  convert lowState_hasDerivAt s 1 using 1
  norm_num [linear,actualMatrix,inlet,Fin.sum_univ_three]
  ring

theorem high_middle_kernel (t : Real) :
    highState t 1=kernel (1/2) (fun s => (1/2 : Real)*highState s 0) t := by
  apply ode_to_kernel (1/2) _ _ ((high_continuous 0).const_mul _) (highState_zero 1)
  intro s
  convert highState_hasDerivAt s 1 using 1
  norm_num [linear,actualMatrix,inlet,Fin.sum_univ_three]
  ring

theorem low_outlet_kernel (t : Real) :
    lowState t 2=kernel (5/2)
      (fun s => 2*lowState s 0+(1/2 : Real)*lowState s 1) t := by
  apply ode_to_kernel (5/2) _ _ (((low_continuous 0).const_mul 2).add
    ((low_continuous 1).const_mul (1/2))) (lowState_zero 2)
  intro s
  convert lowState_hasDerivAt s 2 using 1
  norm_num [linear,actualMatrix,inlet,Fin.sum_univ_three]
  ring

theorem high_outlet_kernel (t : Real) :
    highState t 2=kernel 3
      (fun s => 2*highState s 0+highState s 1) t := by
  apply ode_to_kernel 3 _ _ (((high_continuous 0).const_mul 2).add
    (high_continuous 1)) (highState_zero 2)
  intro s
  convert highState_hasDerivAt s 2 using 1
  norm_num [linear,actualMatrix,inlet,Fin.sum_univ_three]
  ring

end MathExploration.LinearResponseKernel

#print axioms MathExploration.LinearResponseKernel.kernel
#print axioms MathExploration.LinearResponseKernel.ode_to_kernel
#print axioms MathExploration.LinearResponseKernel.kernel_eq_negative
#print axioms MathExploration.LinearResponseKernel.low_continuous
#print axioms MathExploration.LinearResponseKernel.high_continuous
#print axioms MathExploration.LinearResponseKernel.low_zero_exp
#print axioms MathExploration.LinearResponseKernel.high_zero_exp
#print axioms MathExploration.LinearResponseKernel.low_middle_kernel
#print axioms MathExploration.LinearResponseKernel.high_middle_kernel
#print axioms MathExploration.LinearResponseKernel.low_outlet_kernel
#print axioms MathExploration.LinearResponseKernel.high_outlet_kernel
