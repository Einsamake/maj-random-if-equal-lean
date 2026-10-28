module
public import KernelUniformBounds
public import TankResponse
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.UniformCdfBound
open Real Set
open MathExploration.TankResponse MathExploration.LinearResponseKernel
open MathExploration.ResponseKernelCalculus MathExploration.KernelUniformBounds

theorem x0_nonneg (a t : Real) (ha : 0≤a) (ht : 0≤t) : 0≤x0 a t := by
  have h : exp (-a*t)≤1 := by
    calc
      exp (-a*t)≤exp 0 := exp_le_exp.mpr (by nlinarith)
      _=1 := exp_zero
  dsimp [x0]
  linarith

theorem x0_le_one (a t : Real) : x0 a t≤1 := by
  dsimp [x0]
  have h := exp_pos (-a*t)
  linarith

theorem x1_nonneg (a b : Real) (ha : 0≤a) (hb : 0≤b)
    (t : Real) (ht : 0≤t) : 0≤x1 a b t := by
  unfold x1
  apply kernel_nonneg b _ t ht
  intro s hs
  exact mul_nonneg hb (x0_nonneg a s ha hs.1)

theorem gap01_abs_le_one (a b : Real) (ha : 0≤a) (hb : 0≤b)
    (t : Real) (ht : 0≤t) : |x0 a t-x1 a b t|≤1 := by
  rw [abs_of_nonneg (x0_sub_x1_nonneg a b ha t ht)]
  have hx1 := x1_nonneg a b ha hb t ht
  have hx0 := x0_le_one a t
  linarith

theorem gap12_abs_le (a b e f : Real) (ha : 0≤a) (hb : 0≤b)
    (hc : 0<e+f) (t : Real) (ht : 0≤t) :
    |x1 a b t-x2 a b e f t|≤|b-e|/(e+f) := by
  rw [gap12_kernel]
  apply abs_kernel_le (e+f) _ |b-e| hc (abs_nonneg _)
    (((x0_continuous a).sub (x1_continuous a b)).const_mul (b-e)) t ht
  intro s hs
  rw [abs_mul]
  calc
    |b-e|*|x0 a s-x1 a b s|≤|b-e|*1 :=
      mul_le_mul_of_nonneg_left (gap01_abs_le_one a b ha hb s hs.1) (abs_nonneg _)
    _=|b-e| := mul_one _

theorem x2_f_uniform_bound (a b e flo fhi : Real)
    (ha : 0<a) (hb : 0<b) (he : 0≤e) (hflo : 0≤flo) (hff : flo≤fhi)
    (hclo : 0<e+flo) (hchi : 0<e+fhi) (t : Real) (ht : 0≤t) :
    |x2 a b e fhi t-x2 a b e flo t|≤
      (fhi-flo)*|b-e|/((e+flo)*(e+fhi)) := by
  have hd : 0≤fhi-flo := sub_nonneg.mpr hff
  rw [delta_kernel]
  have hk := abs_kernel_le (e+fhi)
    (fun s => (fhi-flo)*(x1 a b s-x2 a b e flo s))
    ((fhi-flo)*(|b-e|/(e+flo))) hchi
    (mul_nonneg hd (div_nonneg (abs_nonneg _) hclo.le))
    (((x1_continuous a b).sub (x2_continuous a b e flo)).const_mul (fhi-flo))
    t ht (by
      intro s hs
      rw [abs_mul,abs_of_nonneg hd]
      exact mul_le_mul_of_nonneg_left (gap12_abs_le a b e flo ha.le hb.le hclo s hs.1) hd)
  calc
    |kernel (e+fhi) (fun s => (fhi-flo)*(x1 a b s-x2 a b e flo s)) t|
        ≤((fhi-flo)*(|b-e|/(e+flo)))/(e+fhi) := hk
    _=(fhi-flo)*|b-e|/((e+flo)*(e+fhi)) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

end MathExploration.UniformCdfBound
#print axioms MathExploration.UniformCdfBound.x0_nonneg
#print axioms MathExploration.UniformCdfBound.x0_le_one
#print axioms MathExploration.UniformCdfBound.x1_nonneg
#print axioms MathExploration.UniformCdfBound.gap01_abs_le_one
#print axioms MathExploration.UniformCdfBound.gap12_abs_le
#print axioms MathExploration.UniformCdfBound.x2_f_uniform_bound
