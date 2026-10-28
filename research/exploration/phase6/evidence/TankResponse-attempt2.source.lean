module
public import ResponseKernelCalculus
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.TankResponse
open Real Set
open MathExploration.LinearResponseKernel MathExploration.ResponseKernelCalculus

def x0 (a t : Real) : Real := 1-exp (-a*t)
def x1 (a b t : Real) : Real := kernel b (fun s => b*x0 a s) t
def x2 (a b e f t : Real) : Real :=
  kernel (e+f) (fun s => e*x0 a s+f*x1 a b s) t

theorem x0_continuous (a : Real) : Continuous (x0 a) := by
  unfold x0
  fun_prop

theorem x0_zero (a : Real) : x0 a 0=0 := by simp [x0]

theorem x0_hasDerivAt (a t : Real) : HasDerivAt (x0 a) (a*(1-x0 a t)) t := by
  have h := (((hasDerivAt_id t).const_mul (-a)).exp).const_sub 1
  convert h using 1
  · funext u
    simp only [x0,id_eq,neg_mul]
  · dsimp [x0]
    ring

theorem x1_continuous (a b : Real) : Continuous (x1 a b) :=
  kernel_continuous b (fun s => b*x0 a s) ((x0_continuous a).const_mul b)

theorem x1_zero (a b : Real) : x1 a b 0=0 := by
  exact kernel_zero b (fun s => b*x0 a s)

theorem x1_hasDerivAt (a b t : Real) :
    HasDerivAt (x1 a b) (b*(x0 a t-x1 a b t)) t := by
  convert kernel_hasDerivAt b (fun s => b*x0 a s)
    ((x0_continuous a).const_mul b) t using 1 <;> ring

theorem x2_continuous (a b e f : Real) : Continuous (x2 a b e f) :=
  kernel_continuous (e+f) (fun s => e*x0 a s+f*x1 a b s)
    (((x0_continuous a).const_mul e).add ((x1_continuous a b).const_mul f))

theorem x2_zero (a b e f : Real) : x2 a b e f 0=0 := by
  exact kernel_zero (e+f) (fun s => e*x0 a s+f*x1 a b s)

theorem x2_hasDerivAt (a b e f t : Real) :
    HasDerivAt (x2 a b e f)
      (e*(x0 a t-x2 a b e f t)+f*(x1 a b t-x2 a b e f t)) t := by
  convert kernel_hasDerivAt (e+f) (fun s => e*x0 a s+f*x1 a b s)
    (((x0_continuous a).const_mul e).add ((x1_continuous a b).const_mul f)) t
    using 1 <;> ring

theorem gap01_kernel (a b t : Real) :
    x0 a t-x1 a b t=kernel b (fun s => a*(1-x0 a s)) t := by
  apply ode_to_kernel b (fun s => x0 a s-x1 a b s) (fun s => a*(1-x0 a s))
    ((continuous_const.sub (x0_continuous a)).const_mul a)
  · simp [x0_zero,x1_zero]
  · intro s
    convert (x0_hasDerivAt a s).sub (x1_hasDerivAt a b s) using 1 <;> ring

theorem x0_sub_x1_nonneg (a b : Real) (ha : 0≤a) (t : Real) (ht : 0≤t) :
    0≤x0 a t-x1 a b t := by
  rw [gap01_kernel]
  apply kernel_nonneg b (fun s => a*(1-x0 a s)) t ht
  intro s hs
  apply mul_nonneg ha
  dsimp [x0]
  have h := exp_pos (-a*s)
  linarith

theorem gap12_kernel (a b e f t : Real) :
    x1 a b t-x2 a b e f t=
      kernel (e+f) (fun s => (b-e)*(x0 a s-x1 a b s)) t := by
  apply ode_to_kernel (e+f) (fun s => x1 a b s-x2 a b e f s)
    (fun s => (b-e)*(x0 a s-x1 a b s))
    (((x0_continuous a).sub (x1_continuous a b)).const_mul (b-e))
  · simp [x1_zero,x2_zero]
  · intro s
    convert (x1_hasDerivAt a b s).sub (x2_hasDerivAt a b e f s) using 1 <;> ring

theorem x1_sub_x2_nonneg (a b e f : Real) (ha : 0≤a) (heb : e≤b)
    (t : Real) (ht : 0≤t) : 0≤x1 a b t-x2 a b e f t := by
  rw [gap12_kernel]
  apply kernel_nonneg (e+f) (fun s => (b-e)*(x0 a s-x1 a b s)) t ht
  intro s hs
  exact mul_nonneg (sub_nonneg.mpr heb) (x0_sub_x1_nonneg a b ha s hs.1)

theorem x1_sub_x2_nonpos (a b e f : Real) (ha : 0≤a) (hbe : b≤e)
    (t : Real) (ht : 0≤t) : x1 a b t-x2 a b e f t≤0 := by
  rw [gap12_kernel]
  apply kernel_nonpos (e+f) (fun s => (b-e)*(x0 a s-x1 a b s)) t ht
  intro s hs
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbe)
    (x0_sub_x1_nonneg a b ha s hs.1)

theorem delta_kernel (a b e flo fhi t : Real) :
    x2 a b e fhi t-x2 a b e flo t=
      kernel (e+fhi) (fun s => (fhi-flo)*(x1 a b s-x2 a b e flo s)) t := by
  apply ode_to_kernel (e+fhi) (fun s => x2 a b e fhi s-x2 a b e flo s)
    (fun s => (fhi-flo)*(x1 a b s-x2 a b e flo s))
    (((x1_continuous a b).sub (x2_continuous a b e flo)).const_mul (fhi-flo))
  · simp [x2_zero]
  · intro s
    convert (x2_hasDerivAt a b e fhi s).sub (x2_hasDerivAt a b e flo s) using 1 <;> ring

theorem x2_mono_f_of_e_le_b (a b e flo fhi : Real) (ha : 0≤a)
    (heb : e≤b) (hff : flo≤fhi) (t : Real) (ht : 0≤t) :
    x2 a b e flo t≤x2 a b e fhi t := by
  apply sub_nonneg.mp
  rw [delta_kernel]
  apply kernel_nonneg (e+fhi)
    (fun s => (fhi-flo)*(x1 a b s-x2 a b e flo s)) t ht
  intro s hs
  exact mul_nonneg (sub_nonneg.mpr hff)
    (x1_sub_x2_nonneg a b e flo ha heb s hs.1)

theorem x2_antitone_f_of_b_le_e (a b e flo fhi : Real) (ha : 0≤a)
    (hbe : b≤e) (hff : flo≤fhi) (t : Real) (ht : 0≤t) :
    x2 a b e fhi t≤x2 a b e flo t := by
  apply sub_nonpos.mp
  rw [delta_kernel]
  apply kernel_nonpos (e+fhi)
    (fun s => (fhi-flo)*(x1 a b s-x2 a b e flo s)) t ht
  intro s hs
  exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hff)
    (x1_sub_x2_nonpos a b e flo ha hbe s hs.1)

theorem x2_eq_of_b_eq_e (a b e flo fhi : Real) (ha : 0≤a)
    (hbe : b=e) (t : Real) (ht : 0≤t) :
    x2 a b e flo t=x2 a b e fhi t := by
  rcases le_total flo fhi with hff | hff
  · exact le_antisymm
      (x2_mono_f_of_e_le_b a b e flo fhi ha (le_of_eq hbe.symm) hff t ht)
      (x2_antitone_f_of_b_le_e a b e flo fhi ha (le_of_eq hbe) hff t ht)
  · exact le_antisymm
      (x2_antitone_f_of_b_le_e a b e fhi flo ha (le_of_eq hbe) hff t ht)
      (x2_mono_f_of_e_le_b a b e fhi flo ha (le_of_eq hbe.symm) hff t ht)
end MathExploration.TankResponse

#print axioms MathExploration.TankResponse.x0
#print axioms MathExploration.TankResponse.x1
#print axioms MathExploration.TankResponse.x2
#print axioms MathExploration.TankResponse.x0_continuous
#print axioms MathExploration.TankResponse.x0_zero
#print axioms MathExploration.TankResponse.x0_hasDerivAt
#print axioms MathExploration.TankResponse.x1_continuous
#print axioms MathExploration.TankResponse.x1_zero
#print axioms MathExploration.TankResponse.x1_hasDerivAt
#print axioms MathExploration.TankResponse.x2_continuous
#print axioms MathExploration.TankResponse.x2_zero
#print axioms MathExploration.TankResponse.x2_hasDerivAt
#print axioms MathExploration.TankResponse.gap01_kernel
#print axioms MathExploration.TankResponse.x0_sub_x1_nonneg
#print axioms MathExploration.TankResponse.gap12_kernel
#print axioms MathExploration.TankResponse.x1_sub_x2_nonneg
#print axioms MathExploration.TankResponse.x1_sub_x2_nonpos
#print axioms MathExploration.TankResponse.delta_kernel
#print axioms MathExploration.TankResponse.x2_mono_f_of_e_le_b
#print axioms MathExploration.TankResponse.x2_antitone_f_of_b_le_e
#print axioms MathExploration.TankResponse.x2_eq_of_b_eq_e
