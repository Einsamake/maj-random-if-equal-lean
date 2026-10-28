module
public import NearBlindCompletion
public import CommonSubmeasureBound
public import Mathlib.MeasureTheory.Measure.WithDensity
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.PositiveWaitingDecomposition
open MeasureTheory ProbabilityTheory Real Set
open MathExploration.TankResponse MathExploration.LinearResponseKernel

local instance prob_one : IsProbabilityMeasure (expMeasure (1:Real)) :=
  isProbabilityMeasure_expMeasure (by norm_num)
local instance prob_three_half : IsProbabilityMeasure (expMeasure (3/2:Real)) :=
  isProbabilityMeasure_expMeasure (by norm_num)
local instance prob_two : IsProbabilityMeasure (expMeasure (2:Real)) :=
  isProbabilityMeasure_expMeasure (by norm_num)

theorem response_resolvent (r s t : Real) (hs : s≠0) :
    x0 r t=(r/s)*x0 s t+((s-r)/s)*x1 r s t := by
  have h := ode_to_kernel s
    (fun u => x0 r u-((r/s)*x0 s u+((s-r)/s)*x1 r s u))
    (fun _ => 0) continuous_const (by simp [x0_zero,x1_zero])
    (by
      intro u
      have hd := (x0_hasDerivAt r u).sub
        (((x0_hasDerivAt s u).const_mul (r/s)).add
          ((x1_hasDerivAt r s u).const_mul ((s-r)/s)))
      convert hd using 1
      field_simp [hs]
      <;> ring) t
  have hk : kernel s (fun _ => 0) t=0 := by simp [kernel]
  rw [hk] at h
  linarith

theorem exponential_resolvent (r s : Real) (hr : 0<r) (hs : 0<s) (hrs : r≤s) :
    expMeasure r=
      (Real.toNNReal (r/s)) • expMeasure s+
      (Real.toNNReal ((s-r)/s)) •
        (expMeasure s ∗ expMeasure r) := by
  letI := isProbabilityMeasure_expMeasure hr
  letI := isProbabilityMeasure_expMeasure hs
  apply Measure.ext_of_Iic
  intro t
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (expMeasure r).real (Iic t)=
    ((Real.toNNReal (r/s)) • expMeasure s+
      (Real.toNNReal ((s-r)/s)) • (expMeasure s ∗ expMeasure r)).real (Iic t)
  rw [measureReal_add_apply]
  simp only [measureReal_nnreal_smul_apply,Real.coe_toNNReal _ (div_nonneg hr.le hs.le),
    Real.coe_toNNReal _ (div_nonneg (sub_nonneg.mpr hrs) hs.le)]
  rw [← cdf_eq_real,← cdf_eq_real,← cdf_eq_real]
  by_cases ht : 0≤t
  · rw [GeneralTankCdf.cdf_exp_eq_x0 r hr t ht,
      GeneralTankCdf.cdf_exp_eq_x0 s hs t ht,
      GeneralTankCdf.cdf_middle_eq_x1 r s hr hs t ht]
    exact response_resolvent r s t hs.ne'
  · rw [GeneralTankCdf.cdf_exp_negative r hr t (lt_of_not_ge ht),
      GeneralTankCdf.cdf_exp_negative s hs t (lt_of_not_ge ht),
      GeneralTankCdf.cdf_middle_negative r s hr hs t (lt_of_not_ge ht)]
    ring

theorem conv_nnreal_smul_left (c : NNReal) (mu nu : Measure Real) [SFinite nu] :
    (c • mu) ∗ nu=c • (mu ∗ nu) := by
  simpa only [Measure.coe_nnreal_smul] using Measure.conv_smul_left mu nu (c:ENNReal)

theorem conv_nnreal_smul_right (c : NNReal) (mu nu : Measure Real) [SFinite nu] :
    mu ∗ (c • nu)=c • (mu ∗ nu) := by
  simpa only [Measure.coe_nnreal_smul] using Measure.conv_smul_right mu nu (c:ENNReal)

def Qlo : Measure Real := (1/3:NNReal) • (expMeasure (3/2) ∗ expMeasure 1)
def Qhi : Measure Real := (1/2:NNReal) • (expMeasure 2 ∗ expMeasure 1)
def kappa : Measure Real := (1/6:NNReal) • (expMeasure (3/2) ∗ expMeasure 2)
def remainder (b : Real) : Measure Real := Qhi+Qlo ∗ expMeasure b

instance Qlo_finite : IsFiniteMeasure Qlo := by unfold Qlo; infer_instance
instance Qhi_finite : IsFiniteMeasure Qhi := by unfold Qhi; infer_instance
instance kappa_finite : IsFiniteMeasure kappa := by unfold kappa; infer_instance

theorem exponential_one_two :
    expMeasure (1:Real)=(1/2:NNReal) • expMeasure 2+
      (1/2:NNReal) • (expMeasure 2 ∗ expMeasure 1) := by
  have h := exponential_resolvent 1 2 (by norm_num) (by norm_num) (by norm_num)
  have hw : Real.toNNReal (1/2:Real)=(1/2:NNReal) := by
    apply NNReal.eq
    norm_num [Real.coe_toNNReal _ (by norm_num : (0:Real)≤1/2)]
  norm_num only [show (2-1:Real)/2=1/2 by norm_num] at h
  simpa only [hw] using h

theorem exponential_one_three_half :
    expMeasure (1:Real)=(2/3:NNReal) • expMeasure (3/2)+
      (1/3:NNReal) • (expMeasure (3/2) ∗ expMeasure 1) := by
  have h := exponential_resolvent 1 (3/2) (by norm_num) (by norm_num) (by norm_num)
  have hp : Real.toNNReal (2/3:Real)=(2/3:NNReal) := by
    apply NNReal.eq
    norm_num [Real.coe_toNNReal _ (by norm_num : (0:Real)≤2/3)]
  have hq : Real.toNNReal (1/3:Real)=(1/3:NNReal) := by
    apply NNReal.eq
    norm_num [Real.coe_toNNReal _ (by norm_num : (0:Real)≤1/3)]
  norm_num only [show (1:Real)/(3/2)=2/3 by norm_num,
    show ((3/2:Real)-1)/(3/2)=1/3 by norm_num] at h
  simpa only [hp,hq] using h

theorem Qlo_eq_kappa_add : Qlo=kappa+kappa ∗ expMeasure 1 := by
  change (1/3:NNReal) • (expMeasure (3/2) ∗ expMeasure 1)=_
  conv_lhs => rw [exponential_one_two]
  norm_num only [Measure.conv_add,conv_nnreal_smul_right,smul_add,smul_smul,
    kappa,conv_nnreal_smul_left,Measure.conv_assoc]

theorem Qhi_eq_two_kappa_add : Qhi=(2:NNReal) • kappa+kappa ∗ expMeasure 1 := by
  change (1/2:NNReal) • (expMeasure 2 ∗ expMeasure 1)=_
  conv_lhs => rw [exponential_one_three_half]
  simp only [Measure.conv_add,conv_nnreal_smul_right,smul_add,smul_smul,
    kappa,conv_nnreal_smul_left,← Measure.conv_assoc,
    Measure.conv_comm (expMeasure 2) (expMeasure (3/2))]
  norm_num

theorem Qhi_eq_Qlo_add_kappa : Qhi=Qlo+kappa := by
  rw [Qlo_eq_kappa_add,Qhi_eq_two_kappa_add,two_smul]
  ac_rfl

theorem two_Qlo_eq_Qhi_add : (2:NNReal) • Qlo=Qhi+kappa ∗ expMeasure 1 := by
  rw [Qlo_eq_kappa_add,Qhi_eq_two_kappa_add]
  simp only [two_smul]
  ac_rfl


theorem remainder_finite (b : Real) (hb : 0<b) : IsFiniteMeasure (remainder b) := by
  letI := isProbabilityMeasure_expMeasure hb
  unfold remainder
  infer_instance

theorem conv_mass_real (mu nu : Measure Real) [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    (mu ∗ nu).real univ=mu.real univ*nu.real univ := by
  exact CommonSubmeasureBound.real_conv_mass mu nu

theorem kappa_mass_real : kappa.real univ=(1/6:Real) := by
  norm_num [kappa,measureReal_def,Measure.smul_apply]

theorem Qlo_mass_real : Qlo.real univ=(1/3:Real) := by
  norm_num [Qlo,measureReal_def,Measure.smul_apply]

theorem Qhi_mass_real : Qhi.real univ=(1/2:Real) := by
  norm_num [Qhi,measureReal_def,Measure.smul_apply]

theorem remainder_mass_real (b : Real) (hb : 0<b) :
    (remainder b).real univ=(5/6:Real) := by
  letI := isProbabilityMeasure_expMeasure hb
  rw [remainder,measureReal_add_apply,conv_mass_real,Qhi_mass_real,Qlo_mass_real]
  norm_num [measureReal_def]

theorem low_measure_base (eps : Real) (heps : 0<eps) :
    NearBlindCompletion.lowTotalMeasure eps=
      (2:NNReal) • Qlo+Qlo ∗ expMeasure (1+eps) := by
  letI := isProbabilityMeasure_expMeasure (r:=1+eps) (by linarith)
  change BranchedLaw.totalMeasure 1 (1+eps) 1 (1/2)
    (by norm_num) (by norm_num) (by norm_num)=_
  rw [BranchedCdfMixture.totalMeasure_eq_mixture 1 (1+eps) 1 (1/2)
    (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num)]
  have hq : unitInterval.toNNReal (BranchedLaw.branchProb 1 (1/2)
      (by norm_num) (by norm_num) (by norm_num))=(1/3:NNReal) := by
    ext
    norm_num [unitInterval.coe_toNNReal,BranchedLaw.branchProb]
  have hp : unitInterval.toNNReal (unitInterval.symm (BranchedLaw.branchProb 1 (1/2)
      (by norm_num) (by norm_num) (by norm_num)))=(2/3:NNReal) := by
    ext
    norm_num [unitInterval.coe_toNNReal,unitInterval.coe_symm_eq,BranchedLaw.branchProb]
  rw [hq,hp]
  have ho : expMeasure (3/2) ∗ (expMeasure (1+eps) ∗ expMeasure 1)=
      (expMeasure (3/2) ∗ expMeasure 1) ∗ expMeasure (1+eps) := by
    rw [Measure.conv_comm (expMeasure (1+eps)) (expMeasure 1),Measure.conv_assoc]
  norm_num only [show (1+1/2:Real)=3/2 by norm_num] at *
  rw [ho]
  norm_num [Qlo,conv_nnreal_smul_left,smul_smul]

theorem high_measure_base (eps : Real) (heps : 0<eps) :
    NearBlindCompletion.highTotalMeasure eps=Qhi+Qhi ∗ expMeasure (1+eps) := by
  letI := isProbabilityMeasure_expMeasure (r:=1+eps) (by linarith)
  change BranchedLaw.totalMeasure 1 (1+eps) 1 1
    (by norm_num) (by norm_num) (by norm_num)=_
  rw [BranchedCdfMixture.totalMeasure_eq_mixture 1 (1+eps) 1 1
    (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num)]
  have hq : unitInterval.toNNReal (BranchedLaw.branchProb 1 1
      (by norm_num) (by norm_num) (by norm_num))=(1/2:NNReal) := by
    ext
    norm_num [unitInterval.coe_toNNReal,BranchedLaw.branchProb]
  have hp : unitInterval.toNNReal (unitInterval.symm (BranchedLaw.branchProb 1 1
      (by norm_num) (by norm_num) (by norm_num)))=(1/2:NNReal) := by
    ext
    norm_num [unitInterval.coe_toNNReal,unitInterval.coe_symm_eq,BranchedLaw.branchProb]
  rw [hq,hp]
  have ho : expMeasure 2 ∗ (expMeasure (1+eps) ∗ expMeasure 1)=
      (expMeasure 2 ∗ expMeasure 1) ∗ expMeasure (1+eps) := by
    rw [Measure.conv_comm (expMeasure (1+eps)) (expMeasure 1),Measure.conv_assoc]
  norm_num only [show (1+1:Real)=2 by norm_num] at *
  rw [ho]
  simp only [Qhi,conv_nnreal_smul_left]

theorem low_positive_decomposition (eps : Real) (heps : 0<eps) :
    NearBlindCompletion.lowTotalMeasure eps=
      remainder (1+eps)+kappa ∗ expMeasure 1 := by
  rw [low_measure_base eps heps,two_Qlo_eq_Qhi_add]
  unfold remainder
  ac_rfl

theorem high_positive_decomposition (eps : Real) (heps : 0<eps) :
    NearBlindCompletion.highTotalMeasure eps=
      remainder (1+eps)+kappa ∗ expMeasure (1+eps) := by
  letI := isProbabilityMeasure_expMeasure (r:=1+eps) (by linarith)
  have h : Qhi ∗ expMeasure (1+eps)=
      Qlo ∗ expMeasure (1+eps)+kappa ∗ expMeasure (1+eps) := by
    rw [Qhi_eq_Qlo_add_kappa,Measure.add_conv]
  rw [high_measure_base eps heps,h]
  unfold remainder
  ac_rfl

end MathExploration.PositiveWaitingDecomposition
#print axioms MathExploration.PositiveWaitingDecomposition.prob_one
#print axioms MathExploration.PositiveWaitingDecomposition.prob_three_half
#print axioms MathExploration.PositiveWaitingDecomposition.prob_two
#print axioms MathExploration.PositiveWaitingDecomposition.response_resolvent
#print axioms MathExploration.PositiveWaitingDecomposition.exponential_resolvent
#print axioms MathExploration.PositiveWaitingDecomposition.conv_nnreal_smul_left
#print axioms MathExploration.PositiveWaitingDecomposition.conv_nnreal_smul_right
#print axioms MathExploration.PositiveWaitingDecomposition.Qlo
#print axioms MathExploration.PositiveWaitingDecomposition.Qhi
#print axioms MathExploration.PositiveWaitingDecomposition.kappa
#print axioms MathExploration.PositiveWaitingDecomposition.remainder
#print axioms MathExploration.PositiveWaitingDecomposition.Qlo_finite
#print axioms MathExploration.PositiveWaitingDecomposition.Qhi_finite
#print axioms MathExploration.PositiveWaitingDecomposition.kappa_finite
#print axioms MathExploration.PositiveWaitingDecomposition.exponential_one_two
#print axioms MathExploration.PositiveWaitingDecomposition.exponential_one_three_half
#print axioms MathExploration.PositiveWaitingDecomposition.Qlo_eq_kappa_add
#print axioms MathExploration.PositiveWaitingDecomposition.Qhi_eq_two_kappa_add
#print axioms MathExploration.PositiveWaitingDecomposition.Qhi_eq_Qlo_add_kappa
#print axioms MathExploration.PositiveWaitingDecomposition.two_Qlo_eq_Qhi_add
#print axioms MathExploration.PositiveWaitingDecomposition.remainder_finite
#print axioms MathExploration.PositiveWaitingDecomposition.conv_mass_real
#print axioms MathExploration.PositiveWaitingDecomposition.kappa_mass_real
#print axioms MathExploration.PositiveWaitingDecomposition.Qlo_mass_real
#print axioms MathExploration.PositiveWaitingDecomposition.Qhi_mass_real
#print axioms MathExploration.PositiveWaitingDecomposition.remainder_mass_real
#print axioms MathExploration.PositiveWaitingDecomposition.low_measure_base
#print axioms MathExploration.PositiveWaitingDecomposition.high_measure_base
#print axioms MathExploration.PositiveWaitingDecomposition.low_positive_decomposition
#print axioms MathExploration.PositiveWaitingDecomposition.high_positive_decomposition
