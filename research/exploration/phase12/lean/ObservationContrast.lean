module
public import BranchThresholdTesting
public import ObservationMaps
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.ObservationContrast
open MeasureTheory Set

def branchSuccess : Real := BranchThresholdTesting.testSuccess 100 (1/100)

def timeSuccess (A : Set (Fin 100 → Real)) : Real :=
  BinaryTestingBound.success (ActualBranchMoments.lowJoint 100 (1/100))
    (ActualBranchMoments.highJoint 100 (1/100)) (ObservationMaps.totals 100 ⁻¹' A)

theorem branchSuccess_ge : (33/50:Real)≤branchSuccess := by
  exact BranchThresholdTesting.testSuccess_one_hundred (1/100) (by norm_num)

theorem timeSuccess_eq (A : Set (Fin 100 → Real)) (hA : MeasurableSet A) :
    timeSuccess A=ActualCompletionTesting.testSuccess 100 (1/100) A := by
  exact ObservationMaps.time_test_success 100 (1/100) (by norm_num) A hA

theorem timeSuccess_le (A : Set (Fin 100 → Real)) (hA : MeasurableSet A) :
    timeSuccess A≤(353/606:Real) := by
  rw [timeSuccess_eq A hA]
  exact ActualCompletionTesting.testSuccess_one_hundredth_one_hundred A hA

theorem advantage_ge (A : Set (Fin 100 → Real)) (hA : MeasurableSet A) :
    (587/7575:Real)≤branchSuccess-timeSuccess A := by
  have hb := branchSuccess_ge
  have ht := timeSuccess_le A hA
  linarith

theorem branch_strictly_better (A : Set (Fin 100 → Real)) (hA : MeasurableSet A) :
    timeSuccess A<branchSuccess := by
  have hg := advantage_ge A hA
  have hp : (0:Real)<587/7575 := by norm_num
  linarith

end MathExploration.ObservationContrast
#print axioms MathExploration.ObservationContrast.branchSuccess
#print axioms MathExploration.ObservationContrast.timeSuccess
#print axioms MathExploration.ObservationContrast.branchSuccess_ge
#print axioms MathExploration.ObservationContrast.timeSuccess_eq
#print axioms MathExploration.ObservationContrast.timeSuccess_le
#print axioms MathExploration.ObservationContrast.advantage_ge
#print axioms MathExploration.ObservationContrast.branch_strictly_better
