module
public import ActualCompletionEventBound
public import CommonIIDBound
public import BinaryTestingBound
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.ActualCompletionTesting
open MeasureTheory Set

-- Coordinates are distinct IID completion-time observations.
def lowSampleMeasure (n : Nat) (eps : Real) : Measure (Fin n → Real) :=
  Measure.pi (fun _ : Fin n => NearBlindCompletion.lowTotalMeasure eps)

def highSampleMeasure (n : Nat) (eps : Real) : Measure (Fin n → Real) :=
  Measure.pi (fun _ : Fin n => NearBlindCompletion.highTotalMeasure eps)

def commonSampleMeasure (n : Nat) (eps : Real) : Measure (Fin n → Real) :=
  Measure.pi (fun _ : Fin n => ActualCompletionEventBound.gamma eps)

def commonMass (eps : Real) : Real := 5 / 6 + 1 / (6 * (1 + eps))

def missingMass (eps : Real) : Real := eps / (6 * (1 + eps))

theorem lowSampleMeasure_probability (n : Nat) (eps : Real) (heps : 0 < eps) :
    IsProbabilityMeasure (lowSampleMeasure n eps) := by
  letI := NearBlindCompletion.lowTotalMeasure_probability eps heps
  unfold lowSampleMeasure
  infer_instance

theorem highSampleMeasure_probability (n : Nat) (eps : Real) (heps : 0 < eps) :
    IsProbabilityMeasure (highSampleMeasure n eps) := by
  letI := NearBlindCompletion.highTotalMeasure_probability eps heps
  unfold highSampleMeasure
  infer_instance

theorem lowSampleMeasure_coordinate (n : Nat) (eps : Real) (heps : 0 < eps) (i : Fin n) :
    (lowSampleMeasure n eps).map (Function.eval i) = NearBlindCompletion.lowTotalMeasure eps := by
  letI := NearBlindCompletion.lowTotalMeasure_probability eps heps
  exact (measurePreserving_eval (fun _ : Fin n => NearBlindCompletion.lowTotalMeasure eps) i).map_eq

theorem highSampleMeasure_coordinate (n : Nat) (eps : Real) (heps : 0 < eps) (i : Fin n) :
    (highSampleMeasure n eps).map (Function.eval i) = NearBlindCompletion.highTotalMeasure eps := by
  letI := NearBlindCompletion.highTotalMeasure_probability eps heps
  exact (measurePreserving_eval (fun _ : Fin n => NearBlindCompletion.highTotalMeasure eps) i).map_eq

theorem lowSampleMeasure_rectangle (n : Nat) (eps : Real) (heps : 0 < eps)
    (s : Fin n → Set Real) :
    lowSampleMeasure n eps (Set.pi univ s) =
      ∏ i : Fin n, NearBlindCompletion.lowTotalMeasure eps (s i) := by
  letI := NearBlindCompletion.lowTotalMeasure_probability eps heps
  exact Measure.pi_pi _ s

theorem highSampleMeasure_rectangle (n : Nat) (eps : Real) (heps : 0 < eps)
    (s : Fin n → Set Real) :
    highSampleMeasure n eps (Set.pi univ s) =
      ∏ i : Fin n, NearBlindCompletion.highTotalMeasure eps (s i) := by
  letI := NearBlindCompletion.highTotalMeasure_probability eps heps
  exact Measure.pi_pi _ s

theorem commonSampleMeasure_le_low (n : Nat) (eps : Real) (heps : 0 < eps) :
    commonSampleMeasure n eps ≤ lowSampleMeasure n eps := by
  letI := NearBlindCompletion.lowTotalMeasure_probability eps heps
  exact CommonIIDBound.commonIID_le n _ _ (ActualCompletionEventBound.gamma_le_low eps heps)

theorem commonSampleMeasure_le_high (n : Nat) (eps : Real) (heps : 0 < eps) :
    commonSampleMeasure n eps ≤ highSampleMeasure n eps := by
  letI := NearBlindCompletion.highTotalMeasure_probability eps heps
  exact CommonIIDBound.commonIID_le n _ _ (ActualCompletionEventBound.gamma_le_high eps heps)

theorem commonSampleMeasure_mass (n : Nat) (eps : Real) (heps : 0 < eps) :
    (commonSampleMeasure n eps).real univ = (commonMass eps)^n := by
  letI := NearBlindCompletion.lowTotalMeasure_probability eps heps
  letI : IsFiniteMeasure (ActualCompletionEventBound.gamma eps) :=
    isFiniteMeasure_of_le _ (ActualCompletionEventBound.gamma_le_low eps heps)
  change (CommonIIDBound.commonIID n (ActualCompletionEventBound.gamma eps)).real univ = _
  rw [CommonIIDBound.commonIID_real_mass, ActualCompletionEventBound.gamma_mass_real eps heps]
  rfl

theorem commonMass_nonneg (eps : Real) (heps : 0 < eps) : 0 ≤ commonMass eps := by
  rw [commonMass, ← ActualCompletionEventBound.gamma_mass_real eps heps]
  exact ENNReal.toReal_nonneg

theorem commonMass_le_one (eps : Real) (heps : 0 < eps) : commonMass eps ≤ 1 := by
  letI := NearBlindCompletion.lowTotalMeasure_probability eps heps
  rw [commonMass, ← ActualCompletionEventBound.gamma_mass_real eps heps]
  exact CommonIIDBound.common_mass_le_one _ _ (ActualCompletionEventBound.gamma_le_low eps heps)

theorem one_sub_commonMass (eps : Real) (heps : 0 < eps) :
    1 - commonMass eps = missingMass eps := by
  rw [commonMass, ← ActualCompletionEventBound.gamma_mass_real eps heps]
  exact ActualCompletionEventBound.gamma_missing_mass eps heps

theorem missing_sample_mass_le_linear (n : Nat) (eps : Real) (heps : 0 < eps) :
    1 - (commonMass eps)^n ≤ (n : Real) * missingMass eps := by
  have h := CommonIIDBound.one_sub_pow_le_mul_one_sub n (commonMass eps)
    (commonMass_nonneg eps heps) (commonMass_le_one eps heps)
  rwa [one_sub_commonMass eps heps] at h

theorem all_test_event_gap (n : Nat) (eps : Real) (heps : 0 < eps)
    (A : Set (Fin n → Real)) (hA : MeasurableSet A) :
    |(highSampleMeasure n eps).real A - (lowSampleMeasure n eps).real A| ≤
      1 - (commonMass eps)^n := by
  letI := lowSampleMeasure_probability n eps heps
  letI := highSampleMeasure_probability n eps heps
  have h := CommonSubmeasureBound.abs_event_gap_le_missing_mass
    (highSampleMeasure n eps) (lowSampleMeasure n eps) (commonSampleMeasure n eps)
    (commonSampleMeasure_le_high n eps heps) (commonSampleMeasure_le_low n eps heps) A hA
  rwa [commonSampleMeasure_mass n eps heps] at h

theorem all_test_event_gap_linear (n : Nat) (eps : Real) (heps : 0 < eps)
    (A : Set (Fin n → Real)) (hA : MeasurableSet A) :
    |(highSampleMeasure n eps).real A - (lowSampleMeasure n eps).real A| ≤
      (n : Real) * missingMass eps :=
  le_trans (all_test_event_gap n eps heps A hA) (missing_sample_mass_le_linear n eps heps)

-- The measurable event A means choosing high after observing the whole sample.
-- Each model has prior probability 1/2.
def testSuccess (n : Nat) (eps : Real) (A : Set (Fin n → Real)) : Real :=
  BinaryTestingBound.success (lowSampleMeasure n eps) (highSampleMeasure n eps) A

def testError (n : Nat) (eps : Real) (A : Set (Fin n → Real)) : Real :=
  BinaryTestingBound.error (lowSampleMeasure n eps) (highSampleMeasure n eps) A

theorem testSuccess_eq (n : Nat) (eps : Real) (A : Set (Fin n → Real)) :
    testSuccess n eps A =
      ((highSampleMeasure n eps).real A + (lowSampleMeasure n eps).real Aᶜ) / 2 := rfl

theorem testError_eq (n : Nat) (eps : Real) (A : Set (Fin n → Real)) :
    testError n eps A =
      ((lowSampleMeasure n eps).real A + (highSampleMeasure n eps).real Aᶜ) / 2 := rfl

theorem testSuccess_add_testError (n : Nat) (eps : Real) (heps : 0 < eps)
    (A : Set (Fin n → Real)) (hA : MeasurableSet A) :
    testSuccess n eps A + testError n eps A = 1 := by
  letI := lowSampleMeasure_probability n eps heps
  letI := highSampleMeasure_probability n eps heps
  exact BinaryTestingBound.success_add_error _ _ A hA

theorem testError_ge_common_power (n : Nat) (eps : Real) (heps : 0 < eps)
    (A : Set (Fin n → Real)) (hA : MeasurableSet A) :
    (commonMass eps)^n / 2 ≤ testError n eps A := by
  letI := lowSampleMeasure_probability n eps heps
  letI := highSampleMeasure_probability n eps heps
  have h := BinaryTestingBound.error_ge_common_mass
    (lowSampleMeasure n eps) (highSampleMeasure n eps) (commonSampleMeasure n eps)
    (commonSampleMeasure_le_low n eps heps) (commonSampleMeasure_le_high n eps heps) A hA
  rwa [commonSampleMeasure_mass n eps heps] at h

theorem testSuccess_le_common_power (n : Nat) (eps : Real) (heps : 0 < eps)
    (A : Set (Fin n → Real)) (hA : MeasurableSet A) :
    testSuccess n eps A ≤ 1 - (commonMass eps)^n / 2 := by
  have h := testError_ge_common_power n eps heps A hA
  have ht := testSuccess_add_testError n eps heps A hA
  linarith

theorem testError_ge_linear (n : Nat) (eps : Real) (heps : 0 < eps)
    (A : Set (Fin n → Real)) (hA : MeasurableSet A) :
    1 / 2 - (n : Real) * missingMass eps / 2 ≤ testError n eps A := by
  have h := testError_ge_common_power n eps heps A hA
  have hm := missing_sample_mass_le_linear n eps heps
  linarith

theorem testSuccess_le_linear (n : Nat) (eps : Real) (heps : 0 < eps)
    (A : Set (Fin n → Real)) (hA : MeasurableSet A) :
    testSuccess n eps A ≤ 1 / 2 + (n : Real) * missingMass eps / 2 := by
  have h := testError_ge_linear n eps heps A hA
  have ht := testSuccess_add_testError n eps heps A hA
  linarith

theorem testSuccess_one_hundredth_one_hundred
    (A : Set (Fin 100 → Real)) (hA : MeasurableSet A) :
    testSuccess 100 (1 / 100) A ≤ (353 / 606 : Real) := by
  have h := testSuccess_le_linear 100 (1 / 100) (by norm_num) A hA
  norm_num [missingMass] at h ⊢
  exact h

theorem testError_one_hundredth_one_hundred
    (A : Set (Fin 100 → Real)) (hA : MeasurableSet A) :
    (253 / 606 : Real) ≤ testError 100 (1 / 100) A := by
  have h := testError_ge_linear 100 (1 / 100) (by norm_num) A hA
  norm_num [missingMass] at h ⊢
  exact h

theorem testSuccess_one_hundredth_one_hundred_power
    (A : Set (Fin 100 → Real)) (hA : MeasurableSet A) :
    testSuccess 100 (1 / 100) A ≤ 1 - (605 / 606 : Real)^100 / 2 := by
  have h := testSuccess_le_common_power 100 (1 / 100) (by norm_num) A hA
  have hc : commonMass (1 / 100) = (605 / 606 : Real) := by norm_num [commonMass]
  simpa only [hc] using h

theorem testError_one_hundredth_one_hundred_power
    (A : Set (Fin 100 → Real)) (hA : MeasurableSet A) :
    (605 / 606 : Real)^100 / 2 ≤ testError 100 (1 / 100) A := by
  have h := testError_ge_common_power 100 (1 / 100) (by norm_num) A hA
  have hc : commonMass (1 / 100) = (605 / 606 : Real) := by norm_num [commonMass]
  simpa only [hc] using h

end MathExploration.ActualCompletionTesting
#print axioms MathExploration.ActualCompletionTesting.lowSampleMeasure
#print axioms MathExploration.ActualCompletionTesting.highSampleMeasure
#print axioms MathExploration.ActualCompletionTesting.commonSampleMeasure
#print axioms MathExploration.ActualCompletionTesting.commonMass
#print axioms MathExploration.ActualCompletionTesting.missingMass
#print axioms MathExploration.ActualCompletionTesting.lowSampleMeasure_probability
#print axioms MathExploration.ActualCompletionTesting.highSampleMeasure_probability
#print axioms MathExploration.ActualCompletionTesting.lowSampleMeasure_coordinate
#print axioms MathExploration.ActualCompletionTesting.highSampleMeasure_coordinate
#print axioms MathExploration.ActualCompletionTesting.lowSampleMeasure_rectangle
#print axioms MathExploration.ActualCompletionTesting.highSampleMeasure_rectangle
#print axioms MathExploration.ActualCompletionTesting.commonSampleMeasure_le_low
#print axioms MathExploration.ActualCompletionTesting.commonSampleMeasure_le_high
#print axioms MathExploration.ActualCompletionTesting.commonSampleMeasure_mass
#print axioms MathExploration.ActualCompletionTesting.commonMass_nonneg
#print axioms MathExploration.ActualCompletionTesting.commonMass_le_one
#print axioms MathExploration.ActualCompletionTesting.one_sub_commonMass
#print axioms MathExploration.ActualCompletionTesting.missing_sample_mass_le_linear
#print axioms MathExploration.ActualCompletionTesting.all_test_event_gap
#print axioms MathExploration.ActualCompletionTesting.all_test_event_gap_linear
#print axioms MathExploration.ActualCompletionTesting.testSuccess
#print axioms MathExploration.ActualCompletionTesting.testError
#print axioms MathExploration.ActualCompletionTesting.testSuccess_eq
#print axioms MathExploration.ActualCompletionTesting.testError_eq
#print axioms MathExploration.ActualCompletionTesting.testSuccess_add_testError
#print axioms MathExploration.ActualCompletionTesting.testError_ge_common_power
#print axioms MathExploration.ActualCompletionTesting.testSuccess_le_common_power
#print axioms MathExploration.ActualCompletionTesting.testError_ge_linear
#print axioms MathExploration.ActualCompletionTesting.testSuccess_le_linear
#print axioms MathExploration.ActualCompletionTesting.testSuccess_one_hundredth_one_hundred
#print axioms MathExploration.ActualCompletionTesting.testError_one_hundredth_one_hundred
#print axioms MathExploration.ActualCompletionTesting.testSuccess_one_hundredth_one_hundred_power
#print axioms MathExploration.ActualCompletionTesting.testError_one_hundredth_one_hundred_power
