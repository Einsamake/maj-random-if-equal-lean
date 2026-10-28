module
public import CommonSubmeasureBound
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.BinaryTestingBound
open MeasureTheory Set

def success {α : Type*} [MeasurableSpace α] (low high : Measure α) (chooseHigh : Set α) : Real :=
  (high.real chooseHigh+low.real chooseHighᶜ)/2

def error {α : Type*} [MeasurableSpace α] (low high : Measure α) (chooseHigh : Set α) : Real :=
  (low.real chooseHigh+high.real chooseHighᶜ)/2

theorem success_add_error {α : Type*} [MeasurableSpace α] (low high : Measure α)
    [IsProbabilityMeasure low] [IsProbabilityMeasure high]
    (A : Set α) (hA : MeasurableSet A) : success low high A+error low high A=1 := by
  have hl := measureReal_add_measureReal_compl (μ:=low) hA
  have hh := measureReal_add_measureReal_compl (μ:=high) hA
  simp only [probReal_univ] at hl hh
  unfold success error
  linarith

theorem error_ge_common_mass {α : Type*} [MeasurableSpace α]
    (low high gamma : Measure α) [IsProbabilityMeasure low] [IsProbabilityMeasure high]
    (hgl : gamma≤low) (hgh : gamma≤high) (A : Set α) (hA : MeasurableSet A) :
    gamma.real univ/2≤error low high A := by
  have hg := CommonSubmeasureBound.abs_event_gap_le_missing_mass high low gamma hgh hgl A hA
  have hd := (abs_le.mp hg).2
  have hh := measureReal_add_measureReal_compl (μ:=high) hA
  simp only [probReal_univ] at hh
  unfold error
  linarith

theorem success_le_of_common_mass {α : Type*} [MeasurableSpace α]
    (low high gamma : Measure α) [IsProbabilityMeasure low] [IsProbabilityMeasure high]
    (hgl : gamma≤low) (hgh : gamma≤high) (A : Set α) (hA : MeasurableSet A) :
    success low high A≤1-gamma.real univ/2 := by
  have he := error_ge_common_mass low high gamma hgl hgh A hA
  have ht := success_add_error low high A hA
  linarith

end MathExploration.BinaryTestingBound
#print axioms MathExploration.BinaryTestingBound.success
#print axioms MathExploration.BinaryTestingBound.error
#print axioms MathExploration.BinaryTestingBound.success_add_error
#print axioms MathExploration.BinaryTestingBound.error_ge_common_mass
#print axioms MathExploration.BinaryTestingBound.success_le_of_common_mass
