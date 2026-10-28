module
public import ResponseKernelCalculus
public import TankResponse
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.KernelUniformBounds
open MeasureTheory Real Set
open MathExploration.LinearResponseKernel MathExploration.ResponseKernelCalculus

theorem kernel_neg (c : Real) (F : Real → Real) (t : Real) :
    kernel c (fun s => -F s) t= -(kernel c F t) := by
  unfold kernel
  simp_rw [mul_neg]
  exact intervalIntegral.integral_neg

theorem kernel_mono (c : Real) (F G : Real → Real) (hF : Continuous F)
    (hG : Continuous G) (t : Real) (ht : 0≤t)
    (hFG : ∀ s, s∈Icc 0 t → F s≤G s) : kernel c F t≤kernel c G t := by
  have hE : Continuous (fun s : Real => exp (c*(s-t))) := by fun_prop
  exact intervalIntegral.integral_mono_on ht
    ((hE.mul hF).intervalIntegrable 0 t) ((hE.mul hG).intervalIntegrable 0 t)
    (fun s hs => mul_le_mul_of_nonneg_left (hFG s hs) (exp_pos _).le)

theorem kernel_const (c K t : Real) (hc : c≠0) :
    kernel c (fun _ => K) t=(K/c)*(1-exp(-c*t)) := by
  symm
  apply ode_to_kernel c (fun s => (K/c)*(1-exp(-c*s))) (fun _ => K)
    continuous_const
  · simp
  · intro s
    have hd := (TankResponse.x0_hasDerivAt c s).const_mul (K/c)
    convert hd using 1
    · rfl
    · dsimp [TankResponse.x0]
      field_simp
      <;> ring

theorem kernel_const_le (c K t : Real) (hc : 0<c) (hK : 0≤K) :
    kernel c (fun _ => K) t≤K/c := by
  rw [kernel_const c K t hc.ne']
  have h := mul_nonneg (div_nonneg hK hc.le) (exp_pos (-c*t)).le
  nlinarith

theorem kernel_le_of_le (c : Real) (F : Real → Real) (K : Real)
    (hc : 0<c) (hK : 0≤K) (hF : Continuous F) (t : Real) (ht : 0≤t)
    (hbound : ∀ s, s∈Icc 0 t → F s≤K) : kernel c F t≤K/c := by
  exact le_trans (kernel_mono c F (fun _ => K) hF continuous_const t ht hbound)
    (kernel_const_le c K t hc hK)

theorem abs_kernel_le (c : Real) (F : Real → Real) (K : Real)
    (hc : 0<c) (hK : 0≤K) (hF : Continuous F) (t : Real) (ht : 0≤t)
    (hbound : ∀ s, s∈Icc 0 t → |F s|≤K) : |kernel c F t|≤K/c := by
  apply abs_le.mpr
  constructor
  · have h := kernel_le_of_le c (fun s => -F s) K hc hK hF.neg t ht
      (fun s hs => le_trans (neg_le_abs (F s)) (hbound s hs))
    rw [kernel_neg] at h
    linarith
  · exact kernel_le_of_le c F K hc hK hF t ht
      (fun s hs => le_trans (le_abs_self (F s)) (hbound s hs))

end MathExploration.KernelUniformBounds
#print axioms MathExploration.KernelUniformBounds.kernel_neg
#print axioms MathExploration.KernelUniformBounds.kernel_mono
#print axioms MathExploration.KernelUniformBounds.kernel_const
#print axioms MathExploration.KernelUniformBounds.kernel_const_le
#print axioms MathExploration.KernelUniformBounds.kernel_le_of_le
#print axioms MathExploration.KernelUniformBounds.abs_kernel_le
