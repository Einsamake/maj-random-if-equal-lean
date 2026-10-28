module
public import NearBlindCompletion
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.ActualBranchMoments
open MeasureTheory ProbabilityTheory Set

noncomputable def lowJoint (n : Nat) (eps : Real) : Measure (Fin n → BranchedLaw.Sample) :=
  Measure.pi (fun _ : Fin n => NearBlindCompletion.lowLaw eps)

noncomputable def highJoint (n : Nat) (eps : Real) : Measure (Fin n → BranchedLaw.Sample) :=
  Measure.pi (fun _ : Fin n => NearBlindCompletion.highLaw eps)

def bit (omega : BranchedLaw.Sample) : Real :=
  if BranchedLaw.J omega then 1 else 0

def count (n : Nat) (x : Fin n → BranchedLaw.Sample) : Real :=
  ∑ i : Fin n, bit (x i)

@[fun_prop] theorem bit_measurable : Measurable bit := by
  exact Measurable.ite
    (BranchedLaw.J_measurable (measurableSet_singleton true)) measurable_const measurable_const

@[fun_prop] theorem count_measurable (n : Nat) : Measurable (count n) := by
  unfold count
  fun_prop

theorem lowJoint_probability (n : Nat) (eps : Real) (heps : 0 < eps) :
    IsProbabilityMeasure (lowJoint n eps) := by
  letI := NearBlindCompletion.lowLaw_probability eps heps
  unfold lowJoint
  infer_instance

theorem highJoint_probability (n : Nat) (eps : Real) (heps : 0 < eps) :
    IsProbabilityMeasure (highJoint n eps) := by
  letI := NearBlindCompletion.highLaw_probability eps heps
  unfold highJoint
  infer_instance

theorem bit_eq_indicator : bit =
    {omega : BranchedLaw.Sample | BranchedLaw.J omega = true}.indicator
      (fun _ => (1 : Real)) := by
  funext omega
  cases h : BranchedLaw.J omega <;> simp [bit, Set.indicator, h]

theorem bit_sq (omega : BranchedLaw.Sample) : (bit omega)^2 = bit omega := by
  cases h : BranchedLaw.J omega <;> simp [bit, h]

theorem bit_memLp (mu : Measure BranchedLaw.Sample) [IsFiniteMeasure mu] : MemLp bit 2 mu := by
  rw [bit_eq_indicator]
  exact memLp_indicator_const 2
    (BranchedLaw.J_measurable (measurableSet_singleton true)).nullMeasurableSet
    1 (Or.inr (measure_ne_top mu _))

theorem bit_mean (mu : Measure BranchedLaw.Sample) :
    (∫ omega, bit omega ∂mu) = mu.real {omega | BranchedLaw.J omega = true} := by
  rw [bit_eq_indicator]
  exact integral_indicator_one (BranchedLaw.J_measurable (measurableSet_singleton true))

theorem bit_variance (mu : Measure BranchedLaw.Sample) [IsProbabilityMeasure mu] :
    variance bit mu = mu.real {omega | BranchedLaw.J omega = true} -
      (mu.real {omega | BranchedLaw.J omega = true})^2 := by
  rw [variance_eq_sub (bit_memLp mu)]
  simp only [Pi.pow_apply, bit_sq, bit_mean]

theorem low_bit_memLp (eps : Real) (heps : 0 < eps) :
    MemLp bit 2 (NearBlindCompletion.lowLaw eps) := by
  letI := NearBlindCompletion.lowLaw_probability eps heps
  exact bit_memLp _

theorem high_bit_memLp (eps : Real) (heps : 0 < eps) :
    MemLp bit 2 (NearBlindCompletion.highLaw eps) := by
  letI := NearBlindCompletion.highLaw_probability eps heps
  exact bit_memLp _

theorem low_bit_mean (eps : Real) (heps : 0 < eps) :
    (∫ omega, bit omega ∂NearBlindCompletion.lowLaw eps) = (1 / 3 : Real) := by
  rw [bit_mean, NearBlindCompletion.low_branch_probability eps heps]

theorem high_bit_mean (eps : Real) (heps : 0 < eps) :
    (∫ omega, bit omega ∂NearBlindCompletion.highLaw eps) = (1 / 2 : Real) := by
  rw [bit_mean, NearBlindCompletion.high_branch_probability eps heps]

theorem low_bit_variance (eps : Real) (heps : 0 < eps) :
    variance bit (NearBlindCompletion.lowLaw eps) = (2 / 9 : Real) := by
  letI := NearBlindCompletion.lowLaw_probability eps heps
  rw [bit_variance, NearBlindCompletion.low_branch_probability eps heps]
  norm_num

theorem high_bit_variance (eps : Real) (heps : 0 < eps) :
    variance bit (NearBlindCompletion.highLaw eps) = (1 / 4 : Real) := by
  letI := NearBlindCompletion.highLaw_probability eps heps
  rw [bit_variance, NearBlindCompletion.high_branch_probability eps heps]
  norm_num

theorem count_memLp (n : Nat) (mu : Measure BranchedLaw.Sample) [IsProbabilityMeasure mu] :
    MemLp (count n) 2 (Measure.pi (fun _ : Fin n => mu)) := by
  unfold count
  exact memLp_finsetSum Finset.univ
    (f := fun i : Fin n => fun x : Fin n → BranchedLaw.Sample => bit (x i))
    (fun i _ => (bit_memLp mu).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => mu) i))

theorem count_mean (n : Nat) (mu : Measure BranchedLaw.Sample) [IsProbabilityMeasure mu] :
    (∫ x, count n x ∂Measure.pi (fun _ : Fin n => mu)) =
      (n : Real) * (∫ omega, bit omega ∂mu) := by
  have hi (i : Fin n) :
      (∫ x : Fin n → BranchedLaw.Sample, bit (x i) ∂Measure.pi (fun _ : Fin n => mu)) =
        ∫ omega, bit omega ∂mu := by
    simpa only [Function.comp_def] using
      (measurePreserving_eval (fun _ : Fin n => mu) i).hasLaw.integral_comp
        bit_measurable.aestronglyMeasurable
  calc
    (∫ x, count n x ∂Measure.pi (fun _ : Fin n => mu)) =
        ∑ i : Fin n, ∫ x : Fin n → BranchedLaw.Sample, bit (x i)
          ∂Measure.pi (fun _ : Fin n => mu) := by
      apply integral_finsetSum
      intro i _
      exact ((bit_memLp mu).comp_measurePreserving
        (measurePreserving_eval (fun _ : Fin n => mu) i)).integrable (by norm_num)
    _ = (n : Real) * (∫ omega, bit omega ∂mu) := by
      simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem count_variance (n : Nat) (mu : Measure BranchedLaw.Sample) [IsProbabilityMeasure mu] :
    variance (count n) (Measure.pi (fun _ : Fin n => mu)) = (n : Real) * variance bit mu := by
  have hc : count n = ∑ i : Fin n, fun x : Fin n → BranchedLaw.Sample => bit (x i) := by
    funext x
    simp only [count, Finset.sum_apply]
  rw [hc, variance_sum_pi (fun _ => bit_memLp mu)]
  simp

theorem low_count_memLp (n : Nat) (eps : Real) (heps : 0 < eps) :
    MemLp (count n) 2 (lowJoint n eps) := by
  letI := NearBlindCompletion.lowLaw_probability eps heps
  exact count_memLp n _

theorem high_count_memLp (n : Nat) (eps : Real) (heps : 0 < eps) :
    MemLp (count n) 2 (highJoint n eps) := by
  letI := NearBlindCompletion.highLaw_probability eps heps
  exact count_memLp n _

theorem low_count_mean (n : Nat) (eps : Real) (heps : 0 < eps) :
    (∫ x, count n x ∂lowJoint n eps) = (n : Real) / 3 := by
  letI := NearBlindCompletion.lowLaw_probability eps heps
  change (∫ x, count n x ∂Measure.pi (fun _ : Fin n => NearBlindCompletion.lowLaw eps)) = _
  rw [count_mean, low_bit_mean eps heps]
  ring

theorem high_count_mean (n : Nat) (eps : Real) (heps : 0 < eps) :
    (∫ x, count n x ∂highJoint n eps) = (n : Real) / 2 := by
  letI := NearBlindCompletion.highLaw_probability eps heps
  change (∫ x, count n x ∂Measure.pi (fun _ : Fin n => NearBlindCompletion.highLaw eps)) = _
  rw [count_mean, high_bit_mean eps heps]
  ring

theorem low_count_variance (n : Nat) (eps : Real) (heps : 0 < eps) :
    variance (count n) (lowJoint n eps) = 2 * (n : Real) / 9 := by
  letI := NearBlindCompletion.lowLaw_probability eps heps
  change variance (count n) (Measure.pi (fun _ : Fin n => NearBlindCompletion.lowLaw eps)) = _
  rw [count_variance, low_bit_variance eps heps]
  ring

theorem high_count_variance (n : Nat) (eps : Real) (heps : 0 < eps) :
    variance (count n) (highJoint n eps) = (n : Real) / 4 := by
  letI := NearBlindCompletion.highLaw_probability eps heps
  change variance (count n) (Measure.pi (fun _ : Fin n => NearBlindCompletion.highLaw eps)) = _
  rw [count_variance, high_bit_variance eps heps]
  ring

end MathExploration.ActualBranchMoments
#print axioms MathExploration.ActualBranchMoments.lowJoint
#print axioms MathExploration.ActualBranchMoments.highJoint
#print axioms MathExploration.ActualBranchMoments.bit
#print axioms MathExploration.ActualBranchMoments.count
#print axioms MathExploration.ActualBranchMoments.bit_measurable
#print axioms MathExploration.ActualBranchMoments.count_measurable
#print axioms MathExploration.ActualBranchMoments.lowJoint_probability
#print axioms MathExploration.ActualBranchMoments.highJoint_probability
#print axioms MathExploration.ActualBranchMoments.bit_eq_indicator
#print axioms MathExploration.ActualBranchMoments.bit_sq
#print axioms MathExploration.ActualBranchMoments.bit_memLp
#print axioms MathExploration.ActualBranchMoments.bit_mean
#print axioms MathExploration.ActualBranchMoments.bit_variance
#print axioms MathExploration.ActualBranchMoments.low_bit_memLp
#print axioms MathExploration.ActualBranchMoments.high_bit_memLp
#print axioms MathExploration.ActualBranchMoments.low_bit_mean
#print axioms MathExploration.ActualBranchMoments.high_bit_mean
#print axioms MathExploration.ActualBranchMoments.low_bit_variance
#print axioms MathExploration.ActualBranchMoments.high_bit_variance
#print axioms MathExploration.ActualBranchMoments.count_memLp
#print axioms MathExploration.ActualBranchMoments.count_mean
#print axioms MathExploration.ActualBranchMoments.count_variance
#print axioms MathExploration.ActualBranchMoments.low_count_memLp
#print axioms MathExploration.ActualBranchMoments.high_count_memLp
#print axioms MathExploration.ActualBranchMoments.low_count_mean
#print axioms MathExploration.ActualBranchMoments.high_count_mean
#print axioms MathExploration.ActualBranchMoments.low_count_variance
#print axioms MathExploration.ActualBranchMoments.high_count_variance
