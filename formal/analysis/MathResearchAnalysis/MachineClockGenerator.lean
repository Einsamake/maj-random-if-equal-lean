module
public import MathResearchAnalysis.MachineClockDynkin
set_option autoImplicit false
/-! The genuine finite-machine Dynkin identity under the original clock law,
with the fair one-site generator identified and the predictable strict-past
state replaced by the actual current state only under Lebesgue-time AE.
No generator equation or transition law is supplied as an assumption. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MachineClockGenerator
open MeasureTheory Set
open DropletClockLaw (Sample Event Vertex)
variable {A : Type*} [Fintype A]

def generator (L : Nat) (step : Vertex L → Bool → A → A) (F : A → Real) (a : A) : Real :=
  ∑ v : Vertex L, ((F (step v false a) + F (step v true a))/2 - F a)

omit [Fintype A] in
theorem increment_rate_eq_generator (L : Nat) (step : Vertex L → Bool → A → A)
    (initial : A) (F : A → Real) (p : NNReal × Sample L) :
    (1/2 : Real) * ∑ v : Vertex L, ∑ b : Bool,
      MachineClockDynkin.increment F L step initial v b p =
    generator L step F (FiniteMachinePreState.beforeState L step initial p.1 p.2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  simp only [MachineClockDynkin.increment, Fintype.sum_bool]
  ring

theorem increment_sample_integrable (L : Nat) (step : Vertex L → Bool → A → A)
    (initial : A) (F : A → Real) (v : Vertex L) (b : Bool) (u : NNReal) :
    Integrable (fun z : Sample L => MachineClockDynkin.increment F L step initial v b (u,z))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  RealPredictableCompensation.sample_integrable L _
    ((MachineClockDynkin.increment_stronglyMeasurable F L step initial v b).mono
      (PredictableClockSigma.predictable_le_ambient L))
    (2 * MachineClockDynkin.bound F) (MachineClockDynkin.increment_norm_le F L step initial v b) u

theorem generator_sample_integrable (L : Nat) (step : Vertex L → Bool → A → A)
    (initial : A) (F : A → Real) (u : NNReal) :
    Integrable (fun z : Sample L => generator L step F
      (FiniteMachinePreState.beforeState L step initial u z))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  have hs := integrable_finsetSum Finset.univ (fun v _ =>
    integrable_finsetSum Finset.univ (fun b _ => increment_sample_integrable L step initial F v b u))
  apply (hs.const_mul (1/2 : Real)).congr
  exact Filter.Eventually.of_forall (fun z => increment_rate_eq_generator L step initial F (u,z))

theorem expected_rate_eq_generator (L : Nat) (step : Vertex L → Bool → A → A)
    (initial : A) (F : A → Real) (u : NNReal) :
    (1/2 : Real) * ∑ v : Vertex L, ∑ b : Bool,
      ∫ z : Sample L, MachineClockDynkin.increment F L step initial v b (u,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) =
    ∫ z : Sample L, generator L step F (FiniteMachinePreState.beforeState L step initial u z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  have hs : (∫ z : Sample L, ∑ v : Vertex L, ∑ b : Bool,
      MachineClockDynkin.increment F L step initial v b (u,z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    ∑ v : Vertex L, ∑ b : Bool, ∫ z : Sample L,
      MachineClockDynkin.increment F L step initial v b (u,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
    rw [integral_finsetSum _ (fun v _ => integrable_finsetSum _
      (fun b _ => increment_sample_integrable L step initial F v b u))]
    apply Finset.sum_congr rfl
    intro v _
    exact integral_finsetSum _ (fun b _ => increment_sample_integrable L step initial F v b u)
  rw [← hs, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (fun z => increment_rate_eq_generator L step initial F (u,z)))

theorem generator_time_mean_integrable (L : Nat) (step : Vertex L → Bool → A → A)
    (initial : A) (F : A → Real) (T : NNReal) :
    Integrable (fun u : Real => ∫ z : Sample L, generator L step F
      (FiniteMachinePreState.beforeState L step initial u.toNNReal z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L))
      ((volume : Measure Real).restrict (Ioc 0 (T : Real))) := by
  have hs := integrable_finsetSum Finset.univ (fun v _ =>
    integrable_finsetSum Finset.univ (fun b _ =>
      MachineClockDynkin.time_mean_increment_integrable F L step initial v b T))
  apply (hs.const_mul (1/2 : Real)).congr
  exact Filter.Eventually.of_forall
    (fun u => expected_rate_eq_generator L step initial F u.toNNReal)

theorem observable_change_dynkin_before (L : Nat) (step : Vertex L → Bool → A → A)
    (initial : A) (F : A → Real) (T : NNReal) :
    (∫ z : Sample L, F (FiniteObservedClockState.endpoint L step initial (T : Real) z) - F initial
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    ∫ u : Real in Ioc 0 (T : Real), ∫ z : Sample L,
      generator L step F (FiniteMachinePreState.beforeState L step initial u.toNNReal z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  rw [MachineClockDynkin.observable_change_dynkin_single_integral F, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (fun u => expected_rate_eq_generator L step initial F u.toNNReal))

theorem current_generator_time_mean_integrable (L : Nat) (step : Vertex L → Bool → A → A)
    (initial : A) (F : A → Real) (T : NNReal) :
    Integrable (fun u : Real => ∫ z : Sample L, generator L step F
      (FiniteObservedClockState.endpoint L step initial u z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L))
      ((volume : Measure Real).restrict (Ioc 0 (T : Real))) := by
  apply (generator_time_mean_integrable L step initial F T).congr
  filter_upwards [ae_restrict_of_ae (FiniteMachinePreState.beforeState_eq_endpoint_time_ae L step initial),
    ae_restrict_mem measurableSet_Ioc] with u hu huint
  apply integral_congr_ae
  filter_upwards [hu] with z hz
  rw [hz huint.1.le]

theorem observable_change_dynkin_current (L : Nat) (step : Vertex L → Bool → A → A)
    (initial : A) (F : A → Real) (T : NNReal) :
    (∫ z : Sample L, F (FiniteObservedClockState.endpoint L step initial (T : Real) z) - F initial
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    ∫ u : Real in Ioc 0 (T : Real), ∫ z : Sample L,
      generator L step F (FiniteObservedClockState.endpoint L step initial u z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  rw [observable_change_dynkin_before L step initial F T]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (FiniteMachinePreState.beforeState_eq_endpoint_time_ae L step initial),
    ae_restrict_mem measurableSet_Ioc] with u hu huint
  apply integral_congr_ae
  filter_upwards [hu] with z hz
  rw [hz huint.1.le]

theorem expected_observable_dynkin_current (L : Nat) (step : Vertex L → Bool → A → A)
    (initial : A) (F : A → Real) (T : NNReal) :
    (∫ z : Sample L, F (FiniteObservedClockState.endpoint L step initial (T : Real) z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    F initial + ∫ u : Real in Ioc 0 (T : Real), ∫ z : Sample L,
      generator L step F (FiniteObservedClockState.endpoint L step initial u z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  have h := observable_change_dynkin_current L step initial F T
  rw [integral_sub (MachineClockDynkin.observable_integrable F L step initial T) (integrable_const _)] at h
  simpa only [integral_const, probReal_univ, one_smul] using
    (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
end MathResearchAnalysis.MachineClockGenerator
