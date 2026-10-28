module
public import ActualBranchMoments
public import BinaryTestingBound
public import Mathlib.Probability.Moments.Variance
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.BranchThresholdTesting
open MeasureTheory ProbabilityTheory Set
open MathExploration.ActualBranchMoments

def threshold (n : Nat) : Real := 5 * (n : Real) / 12

def chooseHigh (n : Nat) : Set (Fin n → BranchedLaw.Sample) :=
  {x | threshold n ≤ count n x}

theorem chooseHigh_measurable (n : Nat) : MeasurableSet (chooseHigh n) :=
  measurableSet_le measurable_const (count_measurable n)

theorem chooseHigh_iff (n : Nat) (x : Fin n → BranchedLaw.Sample) :
    x ∈ chooseHigh n ↔ threshold n ≤ count n x := Iff.rfl

theorem chooseLow_iff (n : Nat) (x : Fin n → BranchedLaw.Sample) :
    x ∈ (chooseHigh n)ᶜ ↔ count n x < threshold n := by
  change (¬threshold n ≤ count n x) ↔ _
  exact not_le

theorem chooseHigh_iff_average (n : Nat) (hn : 0 < n)
    (x : Fin n → BranchedLaw.Sample) :
    x ∈ chooseHigh n ↔ (5 / 12 : Real) ≤ count n x / (n : Real) := by
  have hnr : (0 : Real) < n := by exact_mod_cast hn
  rw [chooseHigh_iff, le_div_iff₀ hnr]
  unfold threshold
  constructor <;> intro h <;> linarith

theorem real_chebyshev {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    [IsFiniteMeasure mu] (X : Ω → Real) (hX : MemLp X 2 mu)
    (radius : Real) (hradius : 0 < radius) :
    mu.real {x | radius ≤ |X x - mu[X]|} ≤ variance X mu / radius^2 := by
  have h := meas_ge_le_variance_div_sq (μ := mu) hX hradius
  have hv : 0 ≤ variance X mu / radius^2 :=
    div_nonneg (variance_nonneg X mu) (sq_nonneg radius)
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [measureReal_def, ENNReal.toReal_ofReal hv] using ht

theorem low_error_subset (n : Nat) :
    chooseHigh n ⊆ {x | (n : Real) / 12 ≤ |count n x - (n : Real) / 3|} := by
  intro x hx
  change threshold n ≤ count n x at hx
  change (n : Real) / 12 ≤ |count n x - (n : Real) / 3|
  have ha := le_abs_self (count n x - (n : Real) / 3)
  unfold threshold at hx
  linarith

theorem high_error_subset (n : Nat) :
    (chooseHigh n)ᶜ ⊆ {x | (n : Real) / 12 ≤ |count n x - (n : Real) / 2|} := by
  intro x hx
  change (¬threshold n ≤ count n x) at hx
  have ht : count n x < threshold n := lt_of_not_ge hx
  change (n : Real) / 12 ≤ |count n x - (n : Real) / 2|
  have ha := neg_le_abs (count n x - (n : Real) / 2)
  unfold threshold at ht
  linarith

theorem low_error_bound (n : Nat) (eps : Real) (heps : 0 < eps) (hn : 0 < n) :
    (lowJoint n eps).real (chooseHigh n) ≤ 32 / (n : Real) := by
  letI := lowJoint_probability n eps heps
  have hnr : (0 : Real) < n := by exact_mod_cast hn
  have hr : (0 : Real) < (n : Real) / 12 := by positivity
  have h := real_chebyshev (lowJoint n eps) (count n)
    (low_count_memLp n eps heps) ((n : Real) / 12) hr
  rw [low_count_mean n eps heps, low_count_variance n eps heps] at h
  calc
    (lowJoint n eps).real (chooseHigh n) ≤
        (lowJoint n eps).real {x | (n : Real) / 12 ≤ |count n x - (n : Real) / 3|} :=
      measureReal_mono (low_error_subset n)
    _ ≤ (2 * (n : Real) / 9) / ((n : Real) / 12)^2 := h
    _ = 32 / (n : Real) := by
      field_simp [ne_of_gt hnr]
      <;> ring

theorem high_error_bound (n : Nat) (eps : Real) (heps : 0 < eps) (hn : 0 < n) :
    (highJoint n eps).real (chooseHigh n)ᶜ ≤ 36 / (n : Real) := by
  letI := highJoint_probability n eps heps
  have hnr : (0 : Real) < n := by exact_mod_cast hn
  have hr : (0 : Real) < (n : Real) / 12 := by positivity
  have h := real_chebyshev (highJoint n eps) (count n)
    (high_count_memLp n eps heps) ((n : Real) / 12) hr
  rw [high_count_mean n eps heps, high_count_variance n eps heps] at h
  calc
    (highJoint n eps).real (chooseHigh n)ᶜ ≤
        (highJoint n eps).real {x | (n : Real) / 12 ≤ |count n x - (n : Real) / 2|} :=
      measureReal_mono (high_error_subset n)
    _ ≤ ((n : Real) / 4) / ((n : Real) / 12)^2 := h
    _ = 36 / (n : Real) := by
      field_simp [ne_of_gt hnr]
      <;> ring

-- Equal model priors; the event chooseHigh n is evaluated on the actual joint sample.
def testError (n : Nat) (eps : Real) : Real :=
  BinaryTestingBound.error (lowJoint n eps) (highJoint n eps) (chooseHigh n)

def testSuccess (n : Nat) (eps : Real) : Real :=
  BinaryTestingBound.success (lowJoint n eps) (highJoint n eps) (chooseHigh n)

theorem testError_eq (n : Nat) (eps : Real) :
    testError n eps =
      ((lowJoint n eps).real (chooseHigh n) + (highJoint n eps).real (chooseHigh n)ᶜ) / 2 := rfl

theorem testSuccess_eq (n : Nat) (eps : Real) :
    testSuccess n eps =
      ((highJoint n eps).real (chooseHigh n) + (lowJoint n eps).real (chooseHigh n)ᶜ) / 2 := rfl

theorem testSuccess_add_testError (n : Nat) (eps : Real) (heps : 0 < eps) :
    testSuccess n eps + testError n eps = 1 := by
  letI := lowJoint_probability n eps heps
  letI := highJoint_probability n eps heps
  exact BinaryTestingBound.success_add_error _ _ _ (chooseHigh_measurable n)

theorem testError_le (n : Nat) (eps : Real) (heps : 0 < eps) (hn : 0 < n) :
    testError n eps ≤ 34 / (n : Real) := by
  have hl := low_error_bound n eps heps hn
  have hh := high_error_bound n eps heps hn
  rw [testError_eq]
  linarith

theorem testSuccess_ge (n : Nat) (eps : Real) (heps : 0 < eps) (hn : 0 < n) :
    1 - 34 / (n : Real) ≤ testSuccess n eps := by
  have he := testError_le n eps heps hn
  have ht := testSuccess_add_testError n eps heps
  linarith

theorem low_error_one_hundred (eps : Real) (heps : 0 < eps) :
    (lowJoint 100 eps).real (chooseHigh 100) ≤ (8 / 25 : Real) := by
  have h := low_error_bound 100 eps heps (by norm_num)
  norm_num at h ⊢
  exact h

theorem high_error_one_hundred (eps : Real) (heps : 0 < eps) :
    (highJoint 100 eps).real (chooseHigh 100)ᶜ ≤ (9 / 25 : Real) := by
  have h := high_error_bound 100 eps heps (by norm_num)
  norm_num at h ⊢
  exact h

theorem testError_one_hundred (eps : Real) (heps : 0 < eps) :
    testError 100 eps ≤ (17 / 50 : Real) := by
  have h := testError_le 100 eps heps (by norm_num)
  norm_num at h ⊢
  exact h

theorem testSuccess_one_hundred (eps : Real) (heps : 0 < eps) :
    (33 / 50 : Real) ≤ testSuccess 100 eps := by
  have h := testSuccess_ge 100 eps heps (by norm_num)
  norm_num at h ⊢
  exact h

end MathExploration.BranchThresholdTesting
#print axioms MathExploration.BranchThresholdTesting.threshold
#print axioms MathExploration.BranchThresholdTesting.chooseHigh
#print axioms MathExploration.BranchThresholdTesting.chooseHigh_measurable
#print axioms MathExploration.BranchThresholdTesting.chooseHigh_iff
#print axioms MathExploration.BranchThresholdTesting.chooseLow_iff
#print axioms MathExploration.BranchThresholdTesting.chooseHigh_iff_average
#print axioms MathExploration.BranchThresholdTesting.real_chebyshev
#print axioms MathExploration.BranchThresholdTesting.low_error_subset
#print axioms MathExploration.BranchThresholdTesting.high_error_subset
#print axioms MathExploration.BranchThresholdTesting.low_error_bound
#print axioms MathExploration.BranchThresholdTesting.high_error_bound
#print axioms MathExploration.BranchThresholdTesting.testError
#print axioms MathExploration.BranchThresholdTesting.testSuccess
#print axioms MathExploration.BranchThresholdTesting.testError_eq
#print axioms MathExploration.BranchThresholdTesting.testSuccess_eq
#print axioms MathExploration.BranchThresholdTesting.testSuccess_add_testError
#print axioms MathExploration.BranchThresholdTesting.testError_le
#print axioms MathExploration.BranchThresholdTesting.testSuccess_ge
#print axioms MathExploration.BranchThresholdTesting.low_error_one_hundred
#print axioms MathExploration.BranchThresholdTesting.high_error_one_hundred
#print axioms MathExploration.BranchThresholdTesting.testError_one_hundred
#print axioms MathExploration.BranchThresholdTesting.testSuccess_one_hundred
