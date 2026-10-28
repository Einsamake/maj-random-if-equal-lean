module
public import TankResponse
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.TankResponse
open Real Set
open MathExploration.LinearResponseKernel MathExploration.ResponseKernelCalculus

theorem gap02_kernel (a b e f t : Real) :
    x0 a t-x2 a b e f t =
      kernel (e+f) (fun s => a*exp (-a*s)+f*(x0 a s-x1 a b s)) t := by
  apply ode_to_kernel (e+f) (fun s => x0 a s-x2 a b e f s)
    (fun s => a*exp (-a*s)+f*(x0 a s-x1 a b s))
    (by fun_prop)
  · simp [x0_zero,x2_zero]
  · intro s
    convert (x0_hasDerivAt a s).sub (x2_hasDerivAt a b e f s) using 1
    dsimp [x0]
    ring

theorem x0_sub_x2_nonneg (a b e f : Real) (ha : 0≤a) (hf : 0≤f)
    (t : Real) (ht : 0≤t) : 0≤x0 a t-x2 a b e f t := by
  rw [gap02_kernel]
  apply kernel_nonneg (e+f) _ t ht
  intro s hs
  exact add_nonneg (mul_nonneg ha (exp_pos _).le)
    (mul_nonneg hf (x0_sub_x1_nonneg a b ha s hs.1))

theorem x0_mono_a (alo ahi : Real) (haa : alo≤ahi) (t : Real) (ht : 0≤t) :
    x0 alo t≤x0 ahi t := by
  unfold x0
  have h : exp (-ahi*t)≤exp (-alo*t) := Real.exp_le_exp.mpr (by nlinarith)
  linarith

theorem delta1_a_kernel (alo ahi b t : Real) :
    x1 ahi b t-x1 alo b t =
      kernel b (fun s => b*(x0 ahi s-x0 alo s)) t := by
  apply ode_to_kernel b (fun s => x1 ahi b s-x1 alo b s)
    (fun s => b*(x0 ahi s-x0 alo s))
    (((x0_continuous ahi).sub (x0_continuous alo)).const_mul b)
  · simp [x1_zero]
  · intro s
    convert (x1_hasDerivAt ahi b s).sub (x1_hasDerivAt alo b s) using 1 <;> ring

theorem x1_mono_a (alo ahi b : Real) (hb : 0≤b) (haa : alo≤ahi)
    (t : Real) (ht : 0≤t) : x1 alo b t≤x1 ahi b t := by
  apply sub_nonneg.mp
  rw [delta1_a_kernel]
  apply kernel_nonneg b _ t ht
  intro s hs
  exact mul_nonneg hb (sub_nonneg.mpr (x0_mono_a alo ahi haa s hs.1))

theorem delta2_a_kernel (alo ahi b e f t : Real) :
    x2 ahi b e f t-x2 alo b e f t =
      kernel (e+f) (fun s => e*(x0 ahi s-x0 alo s)+f*(x1 ahi b s-x1 alo b s)) t := by
  apply ode_to_kernel (e+f) (fun s => x2 ahi b e f s-x2 alo b e f s)
    (fun s => e*(x0 ahi s-x0 alo s)+f*(x1 ahi b s-x1 alo b s))
    ((((x0_continuous ahi).sub (x0_continuous alo)).const_mul e).add
      (((x1_continuous ahi b).sub (x1_continuous alo b)).const_mul f))
  · simp [x2_zero]
  · intro s
    convert (x2_hasDerivAt ahi b e f s).sub (x2_hasDerivAt alo b e f s) using 1 <;> ring

theorem x2_mono_a (alo ahi b e f : Real) (hb : 0≤b) (he : 0≤e)
    (hf : 0≤f) (haa : alo≤ahi) (t : Real) (ht : 0≤t) :
    x2 alo b e f t≤x2 ahi b e f t := by
  apply sub_nonneg.mp
  rw [delta2_a_kernel]
  apply kernel_nonneg (e+f) _ t ht
  intro s hs
  exact add_nonneg
    (mul_nonneg he (sub_nonneg.mpr (x0_mono_a alo ahi haa s hs.1)))
    (mul_nonneg hf (sub_nonneg.mpr (x1_mono_a alo ahi b hb haa s hs.1)))

theorem delta1_b_kernel (a blo bhi t : Real) :
    x1 a bhi t-x1 a blo t =
      kernel bhi (fun s => (bhi-blo)*(x0 a s-x1 a blo s)) t := by
  apply ode_to_kernel bhi (fun s => x1 a bhi s-x1 a blo s)
    (fun s => (bhi-blo)*(x0 a s-x1 a blo s))
    (((x0_continuous a).sub (x1_continuous a blo)).const_mul (bhi-blo))
  · simp [x1_zero]
  · intro s
    convert (x1_hasDerivAt a bhi s).sub (x1_hasDerivAt a blo s) using 1 <;> ring

theorem x1_mono_b (a blo bhi : Real) (ha : 0≤a) (hbb : blo≤bhi)
    (t : Real) (ht : 0≤t) : x1 a blo t≤x1 a bhi t := by
  apply sub_nonneg.mp
  rw [delta1_b_kernel]
  apply kernel_nonneg bhi _ t ht
  intro s hs
  exact mul_nonneg (sub_nonneg.mpr hbb) (x0_sub_x1_nonneg a blo ha s hs.1)

theorem delta2_b_kernel (a blo bhi e f t : Real) :
    x2 a bhi e f t-x2 a blo e f t =
      kernel (e+f) (fun s => f*(x1 a bhi s-x1 a blo s)) t := by
  apply ode_to_kernel (e+f) (fun s => x2 a bhi e f s-x2 a blo e f s)
    (fun s => f*(x1 a bhi s-x1 a blo s))
    (((x1_continuous a bhi).sub (x1_continuous a blo)).const_mul f)
  · simp [x2_zero]
  · intro s
    convert (x2_hasDerivAt a bhi e f s).sub (x2_hasDerivAt a blo e f s) using 1 <;> ring

theorem x2_mono_b (a blo bhi e f : Real) (ha : 0≤a) (hf : 0≤f)
    (hbb : blo≤bhi) (t : Real) (ht : 0≤t) :
    x2 a blo e f t≤x2 a bhi e f t := by
  apply sub_nonneg.mp
  rw [delta2_b_kernel]
  apply kernel_nonneg (e+f) _ t ht
  intro s hs
  exact mul_nonneg hf (sub_nonneg.mpr (x1_mono_b a blo bhi ha hbb s hs.1))

theorem delta2_e_kernel (a b elo ehi f t : Real) :
    x2 a b ehi f t-x2 a b elo f t =
      kernel (ehi+f) (fun s => (ehi-elo)*(x0 a s-x2 a b elo f s)) t := by
  apply ode_to_kernel (ehi+f) (fun s => x2 a b ehi f s-x2 a b elo f s)
    (fun s => (ehi-elo)*(x0 a s-x2 a b elo f s))
    (((x0_continuous a).sub (x2_continuous a b elo f)).const_mul (ehi-elo))
  · simp [x2_zero]
  · intro s
    convert (x2_hasDerivAt a b ehi f s).sub (x2_hasDerivAt a b elo f s) using 1 <;> ring

theorem x2_mono_e (a b elo ehi f : Real) (ha : 0≤a) (hf : 0≤f)
    (hee : elo≤ehi) (t : Real) (ht : 0≤t) :
    x2 a b elo f t≤x2 a b ehi f t := by
  apply sub_nonneg.mp
  rw [delta2_e_kernel]
  apply kernel_nonneg (ehi+f) _ t ht
  intro s hs
  exact mul_nonneg (sub_nonneg.mpr hee) (x0_sub_x2_nonneg a b elo f ha hf s hs.1)

end MathExploration.TankResponse
#print axioms MathExploration.TankResponse.gap02_kernel
#print axioms MathExploration.TankResponse.x0_sub_x2_nonneg
#print axioms MathExploration.TankResponse.x0_mono_a
#print axioms MathExploration.TankResponse.delta1_a_kernel
#print axioms MathExploration.TankResponse.x1_mono_a
#print axioms MathExploration.TankResponse.delta2_a_kernel
#print axioms MathExploration.TankResponse.x2_mono_a
#print axioms MathExploration.TankResponse.delta1_b_kernel
#print axioms MathExploration.TankResponse.x1_mono_b
#print axioms MathExploration.TankResponse.delta2_b_kernel
#print axioms MathExploration.TankResponse.x2_mono_b
#print axioms MathExploration.TankResponse.delta2_e_kernel
#print axioms MathExploration.TankResponse.x2_mono_e
