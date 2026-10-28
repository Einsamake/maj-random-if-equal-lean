module
public import PositiveWaitingDecomposition
public import ExponentialMinorization
public import CommonSubmeasureBound
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.ActualCompletionEventBound
open MeasureTheory ProbabilityTheory Set
open MathExploration.PositiveWaitingDecomposition
open MathExploration.ExponentialMinorization

def gamma (eps : Real) : Measure Real :=
  remainder (1 + eps) + kappa ∗ rho (1 + eps)

theorem gamma_le_low (eps : Real) (heps : 0 < eps) :
    gamma eps ≤ NearBlindCompletion.lowTotalMeasure eps := by
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0 : Real) < 1)
  rw [low_positive_decomposition eps heps]
  exact add_le_add_left
    (CommonSubmeasureBound.conv_mono_right kappa (rho (1 + eps)) (expMeasure 1)
      (rho_le_exp_one (1 + eps) (by linarith))) (remainder (1 + eps))

theorem gamma_le_high (eps : Real) (heps : 0 < eps) :
    gamma eps ≤ NearBlindCompletion.highTotalMeasure eps := by
  letI := isProbabilityMeasure_expMeasure (by linarith : 0 < 1 + eps)
  rw [high_positive_decomposition eps heps]
  exact add_le_add_left
    (CommonSubmeasureBound.conv_mono_right kappa (rho (1 + eps)) (expMeasure (1 + eps))
      (rho_le_exp_same (1 + eps) (by linarith))) (remainder (1 + eps))

theorem gamma_mass_real (eps : Real) (heps : 0 < eps) :
    (gamma eps).real univ = (5 / 6 : Real) + 1 / (6 * (1 + eps)) := by
  have hb : 0 < 1 + eps := by linarith
  letI := remainder_finite (1 + eps) hb
  letI := rho_finite (1 + eps) hb
  change (remainder (1 + eps) + kappa ∗ rho (1 + eps)).real univ = _
  rw [measureReal_add_apply, CommonSubmeasureBound.real_conv_mass,
    remainder_mass_real (1 + eps) hb, kappa_mass_real, rho_mass_real (1 + eps) hb]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem gamma_missing_mass (eps : Real) (heps : 0 < eps) :
    1 - (gamma eps).real univ = eps / (6 * (1 + eps)) := by
  rw [gamma_mass_real eps heps]
  have hb : 1 + eps ≠ 0 := ne_of_gt (by linarith)
  field_simp [hb]
  <;> ring

theorem all_output_event_gap (eps : Real) (heps : 0 < eps)
    (s : Set Real) (hs : MeasurableSet s) :
    |(NearBlindCompletion.highTotalMeasure eps).real s -
      (NearBlindCompletion.lowTotalMeasure eps).real s| ≤ eps / (6 * (1 + eps)) := by
  letI := NearBlindCompletion.highTotalMeasure_probability eps heps
  letI := NearBlindCompletion.lowTotalMeasure_probability eps heps
  exact CommonSubmeasureBound.abs_event_gap_le_of_common_mass
    (NearBlindCompletion.highTotalMeasure eps) (NearBlindCompletion.lowTotalMeasure eps)
    (gamma eps) (gamma_le_high eps heps) (gamma_le_low eps heps)
    (eps / (6 * (1 + eps))) (le_of_eq (gamma_missing_mass eps heps)) s hs

theorem all_product_law_event_gap (eps : Real) (heps : 0 < eps)
    (s : Set Real) (hs : MeasurableSet s) :
    |(NearBlindCompletion.highLaw eps).real {ω | BranchedLaw.total ω ∈ s} -
      (NearBlindCompletion.lowLaw eps).real {ω | BranchedLaw.total ω ∈ s}| ≤
        eps / (6 * (1 + eps)) := by
  have hhi : (NearBlindCompletion.highTotalMeasure eps).real s =
      (NearBlindCompletion.highLaw eps).real {ω | BranchedLaw.total ω ∈ s} := by
    change ((NearBlindCompletion.highLaw eps).map BranchedLaw.total).real s = _
    exact map_measureReal_apply BranchedLaw.total_measurable hs
  have hlo : (NearBlindCompletion.lowTotalMeasure eps).real s =
      (NearBlindCompletion.lowLaw eps).real {ω | BranchedLaw.total ω ∈ s} := by
    change ((NearBlindCompletion.lowLaw eps).map BranchedLaw.total).real s = _
    exact map_measureReal_apply BranchedLaw.total_measurable hs
  rw [← hhi, ← hlo]
  exact all_output_event_gap eps heps s hs

theorem all_output_event_gap_one_hundredth (s : Set Real) (hs : MeasurableSet s) :
    |(NearBlindCompletion.highTotalMeasure (1 / 100)).real s -
      (NearBlindCompletion.lowTotalMeasure (1 / 100)).real s| ≤ (1 / 606 : Real) := by
  have h := all_output_event_gap (1 / 100) (by norm_num) s hs
  have hconst : (1 / 100 : Real) / (6 * (1 + 1 / 100)) = 1 / 606 := by norm_num
  simpa only [hconst] using h

theorem all_product_law_event_gap_one_hundredth (s : Set Real) (hs : MeasurableSet s) :
    |(NearBlindCompletion.highLaw (1 / 100)).real {ω | BranchedLaw.total ω ∈ s} -
      (NearBlindCompletion.lowLaw (1 / 100)).real {ω | BranchedLaw.total ω ∈ s}| ≤
        (1 / 606 : Real) := by
  have h := all_product_law_event_gap (1 / 100) (by norm_num) s hs
  have hconst : (1 / 100 : Real) / (6 * (1 + 1 / 100)) = 1 / 606 := by norm_num
  simpa only [hconst] using h

end MathExploration.ActualCompletionEventBound
#print axioms MathExploration.ActualCompletionEventBound.gamma
#print axioms MathExploration.ActualCompletionEventBound.gamma_le_low
#print axioms MathExploration.ActualCompletionEventBound.gamma_le_high
#print axioms MathExploration.ActualCompletionEventBound.gamma_mass_real
#print axioms MathExploration.ActualCompletionEventBound.gamma_missing_mass
#print axioms MathExploration.ActualCompletionEventBound.all_output_event_gap
#print axioms MathExploration.ActualCompletionEventBound.all_product_law_event_gap
#print axioms MathExploration.ActualCompletionEventBound.all_output_event_gap_one_hundredth
#print axioms MathExploration.ActualCompletionEventBound.all_product_law_event_gap_one_hundredth
