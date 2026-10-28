module
public import ActualCompletionTesting
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.ObservationMaps
open MeasureTheory Set

def joint (n : Nat) (mu : Measure BranchedLaw.Sample) : Measure (Fin n → BranchedLaw.Sample) :=
  Measure.pi (fun _ : Fin n => mu)

def totals (n : Nat) (x : Fin n → BranchedLaw.Sample) : Fin n → Real :=
  fun i => BranchedLaw.total (x i)

@[fun_prop] theorem totals_measurable (n : Nat) : Measurable (totals n) := by
  unfold totals
  fun_prop

theorem low_joint_totals (n : Nat) (eps : Real) (heps : 0<eps) :
    (joint n (NearBlindCompletion.lowLaw eps)).map (totals n)=
      ActualCompletionTesting.lowSampleMeasure n eps := by
  letI : IsProbabilityMeasure ((NearBlindCompletion.lowLaw eps).map BranchedLaw.total) := by
    change IsProbabilityMeasure (NearBlindCompletion.lowTotalMeasure eps)
    exact NearBlindCompletion.lowTotalMeasure_probability eps heps
  change (Measure.pi (fun _ : Fin n => NearBlindCompletion.lowLaw eps)).map
    (fun x i => BranchedLaw.total (x i))=Measure.pi (fun _ => NearBlindCompletion.lowTotalMeasure eps)
  rw [Measure.pi_map_pi (fun _ => BranchedLaw.total_measurable.aemeasurable)]
  rfl

theorem high_joint_totals (n : Nat) (eps : Real) (heps : 0<eps) :
    (joint n (NearBlindCompletion.highLaw eps)).map (totals n)=
      ActualCompletionTesting.highSampleMeasure n eps := by
  letI : IsProbabilityMeasure ((NearBlindCompletion.highLaw eps).map BranchedLaw.total) := by
    change IsProbabilityMeasure (NearBlindCompletion.highTotalMeasure eps)
    exact NearBlindCompletion.highTotalMeasure_probability eps heps
  change (Measure.pi (fun _ : Fin n => NearBlindCompletion.highLaw eps)).map
    (fun x i => BranchedLaw.total (x i))=Measure.pi (fun _ => NearBlindCompletion.highTotalMeasure eps)
  rw [Measure.pi_map_pi (fun _ => BranchedLaw.total_measurable.aemeasurable)]
  rfl

theorem low_joint_time_event (n : Nat) (eps : Real) (heps : 0<eps)
    (A : Set (Fin n → Real)) (hA : MeasurableSet A) :
    (joint n (NearBlindCompletion.lowLaw eps)).real (totals n ⁻¹' A)=
      (ActualCompletionTesting.lowSampleMeasure n eps).real A := by
  rw [← low_joint_totals n eps heps]
  exact (map_measureReal_apply (totals_measurable n) hA).symm

theorem high_joint_time_event (n : Nat) (eps : Real) (heps : 0<eps)
    (A : Set (Fin n → Real)) (hA : MeasurableSet A) :
    (joint n (NearBlindCompletion.highLaw eps)).real (totals n ⁻¹' A)=
      (ActualCompletionTesting.highSampleMeasure n eps).real A := by
  rw [← high_joint_totals n eps heps]
  exact (map_measureReal_apply (totals_measurable n) hA).symm

theorem time_test_success (n : Nat) (eps : Real) (heps : 0<eps)
    (A : Set (Fin n → Real)) (hA : MeasurableSet A) :
    BinaryTestingBound.success (joint n (NearBlindCompletion.lowLaw eps))
      (joint n (NearBlindCompletion.highLaw eps)) (totals n ⁻¹' A)=
      ActualCompletionTesting.testSuccess n eps A := by
  change ((joint n (NearBlindCompletion.highLaw eps)).real (totals n ⁻¹' A)+
    (joint n (NearBlindCompletion.lowLaw eps)).real (totals n ⁻¹' Aᶜ))/2=_
  rw [high_joint_time_event n eps heps A hA,low_joint_time_event n eps heps Aᶜ hA.compl]
  rfl

end MathExploration.ObservationMaps
#print axioms MathExploration.ObservationMaps.joint
#print axioms MathExploration.ObservationMaps.totals
#print axioms MathExploration.ObservationMaps.totals_measurable
#print axioms MathExploration.ObservationMaps.low_joint_totals
#print axioms MathExploration.ObservationMaps.high_joint_totals
#print axioms MathExploration.ObservationMaps.low_joint_time_event
#print axioms MathExploration.ObservationMaps.high_joint_time_event
#print axioms MathExploration.ObservationMaps.time_test_success
