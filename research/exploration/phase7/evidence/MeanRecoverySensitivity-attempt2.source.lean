module
public import ParameterRecovery
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.MeanRecoverySensitivity
open MeasureTheory

-- These are means of the phase5 law, with a = e = 1, b = 1 + eps.
def lowMean (eps : Real) : Real :=
  integral (BranchedLaw.law 1 (1 + eps) 1 (1 / 2)
    (by norm_num) (by norm_num) (by norm_num)) BranchedLaw.total

def highMean (eps : Real) : Real :=
  integral (BranchedLaw.law 1 (1 + eps) 1 1
    (by norm_num) (by norm_num) (by norm_num)) BranchedLaw.total

theorem low_total_integrable (eps : Real) (heps : 0 < eps) :
    Integrable BranchedLaw.total (BranchedLaw.law 1 (1 + eps) 1 (1 / 2)
      (by norm_num) (by norm_num) (by norm_num)) :=
  BranchedLaw.total_integrable 1 (1 + eps) 1 (1 / 2)
    (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num)

theorem high_total_integrable (eps : Real) (heps : 0 < eps) :
    Integrable BranchedLaw.total (BranchedLaw.law 1 (1 + eps) 1 1
      (by norm_num) (by norm_num) (by norm_num)) :=
  BranchedLaw.total_integrable 1 (1 + eps) 1 1
    (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num)

theorem total_mean_gap (eps : Real) (heps : 0 < eps) :
    lowMean eps - highMean eps = eps / (6 * (1 + eps)) := by
  unfold lowMean highMean
  rw [BranchedLaw.total_mean 1 (1 + eps) 1 (1 / 2)
        (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num),
      BranchedLaw.total_mean 1 (1 + eps) 1 1
        (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num)]
  have hb : 1 + eps ≠ 0 := ne_of_gt (by linarith : 0 < 1 + eps)
  field_simp [hb]
  <;> ring

theorem total_mean_gap_pos_lt (eps : Real) (heps : 0 < eps) :
    0 < lowMean eps - highMean eps ∧ lowMean eps - highMean eps < eps := by
  rw [total_mean_gap eps heps]
  constructor
  · exact div_pos heps (by positivity)
  · apply (div_lt_iff₀ (by positivity : 0 < (6 : Real) * (1 + eps))).2
    nlinarith [sq_nonneg eps]

theorem parameter_gap : (1 : Real) - 1 / 2 = 1 / 2 := by norm_num

theorem lowMean_one_hundredth : lowMean (1 / 100) = 605 / 303 := by
  unfold lowMean
  rw [BranchedLaw.total_mean 1 (1 + 1 / 100) 1 (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

theorem highMean_one_hundredth : highMean (1 / 100) = 403 / 202 := by
  unfold highMean
  rw [BranchedLaw.total_mean 1 (1 + 1 / 100) 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

theorem total_mean_gap_one_hundredth :
    lowMean (1 / 100) - highMean (1 / 100) = 1 / 606 := by
  rw [lowMean_one_hundredth, highMean_one_hundredth]
  norm_num

theorem finite_difference_ratio :
    ((1 : Real) - 1 / 2) / (lowMean (1 / 100) - highMean (1 / 100)) = 303 := by
  rw [total_mean_gap_one_hundredth]
  norm_num
end MathExploration.MeanRecoverySensitivity
#print axioms MathExploration.MeanRecoverySensitivity.lowMean
#print axioms MathExploration.MeanRecoverySensitivity.highMean
#print axioms MathExploration.MeanRecoverySensitivity.low_total_integrable
#print axioms MathExploration.MeanRecoverySensitivity.high_total_integrable
#print axioms MathExploration.MeanRecoverySensitivity.total_mean_gap
#print axioms MathExploration.MeanRecoverySensitivity.total_mean_gap_pos_lt
#print axioms MathExploration.MeanRecoverySensitivity.parameter_gap
#print axioms MathExploration.MeanRecoverySensitivity.lowMean_one_hundredth
#print axioms MathExploration.MeanRecoverySensitivity.highMean_one_hundredth
#print axioms MathExploration.MeanRecoverySensitivity.total_mean_gap_one_hundredth
#print axioms MathExploration.MeanRecoverySensitivity.finite_difference_ratio
