module
public import MathResearchAnalysis.PredictableClockReference
public import MathResearchAnalysis.PredictableClockSigma
public import MathResearchAnalysis.MarkedPredictableRectangles
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit false
/-! Actual compensation for nonnegative weights measurable in the standard
predictable sigma of the original marked history. We compare the actual event
measure and the canonical time/reference measure only after trimming to this
sigma, then return to the genuine pathwise event sum. No Poisson process law,
compensation premise, physical-state predictability or area drift is assumed. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MarkedPredictableCompensation
open MeasureTheory
open DropletClockLaw (Sample Vertex)

theorem trim_eq_reference (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal) :
    (MarkedClockPointMeasure.measure L v b T).trim
        (PredictableClockSigma.predictable_le_ambient L) =
      (PredictableClockReference.reference L T).trim
        (PredictableClockSigma.predictable_le_ambient L) := by
  apply PredictableClockSigma.trim_eq_of_rectangle_masses L
    (MarkedClockPointMeasure.measure L v b T) (PredictableClockReference.reference L T)
  · intro E _hE
    rw [MarkedPredictableRectangles.zero_rectangle,
      PredictableClockReference.reference_zero_rectangle]
  · intro s E hE
    rw [MarkedPredictableRectangles.future_rectangle L v b T s E hE,
      PredictableClockReference.reference_future_rectangle L T s E]
  · rw [MarkedClockPointMeasure.measure_univ_eq, PredictableClockReference.reference_univ]

theorem lintegral_eq_reference (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → ENNReal)
    (hf : Measurable[(RationalProtectedExit.nnHistory L).predictable] f) :
    (∫⁻ q, f q ∂MarkedClockPointMeasure.measure L v b T) =
      ∫⁻ q, f q ∂PredictableClockReference.reference L T := by
  rw [← lintegral_trim (PredictableClockSigma.predictable_le_ambient L) hf,
    trim_eq_reference L v b T, lintegral_trim (PredictableClockSigma.predictable_le_ambient L) hf]

theorem lintegral_eq_time (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → ENNReal)
    (hf : Measurable[(RationalProtectedExit.nnHistory L).predictable] f) :
    (∫⁻ q, f q ∂MarkedClockPointMeasure.measure L v b T) =
      (2 : ENNReal)⁻¹ * ∫⁻ u : Real in Set.Ioc 0 (T : Real),
        ∫⁻ z : Sample L, f (u.toNNReal,z)
          ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  rw [lintegral_eq_reference L v b T f hf]
  exact PredictableClockReference.lintegral_reference L T f
    (hf.mono (PredictableClockSigma.predictable_le_ambient L) le_rfl)

/-- The actual marked arrivals, not an abstract replacement process, are
summed. The extended sum and both nonnegative integrals may be infinite. -/
theorem pathwise_lintegral_eq_time (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → ENNReal)
    (hf : Measurable[(RationalProtectedExit.nnHistory L).predictable] f) :
    (∫⁻ z : Sample L, ∑' k : Nat, (MarkedClockPointMeasure.window L v b T k).indicator
        (fun z => f (MarkedClockPointMeasure.point L v k z)) z
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      (2 : ENNReal)⁻¹ * ∫⁻ u : Real in Set.Ioc 0 (T : Real),
        ∫⁻ z : Sample L, f (u.toNNReal,z)
          ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  rw [← MarkedClockPointMeasure.lintegral_eq_pathwise_sum L v b T f
    (hf.mono (PredictableClockSigma.predictable_le_ambient L) le_rfl)]
  exact lintegral_eq_time L v b T f hf

/-- Equality of real Bochner integrals on the two actual measures. Its use
as an expectation still requires integrability, provided separately below. -/
theorem integral_eq_reference (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → Real)
    (hf : StronglyMeasurable[(RationalProtectedExit.nnHistory L).predictable] f) :
    (∫ q, f q ∂MarkedClockPointMeasure.measure L v b T) =
      ∫ q, f q ∂PredictableClockReference.reference L T := by
  calc
    _ = ∫ q, f q ∂(MarkedClockPointMeasure.measure L v b T).trim
          (PredictableClockSigma.predictable_le_ambient L) :=
      integral_trim (PredictableClockSigma.predictable_le_ambient L) hf
    _ = ∫ q, f q ∂(PredictableClockReference.reference L T).trim
          (PredictableClockSigma.predictable_le_ambient L) := by rw [trim_eq_reference]
    _ = _ := (integral_trim (PredictableClockSigma.predictable_le_ambient L) hf).symm

theorem integrable_iff_reference (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → Real)
    (hf : StronglyMeasurable[(RationalProtectedExit.nnHistory L).predictable] f) :
    Integrable f (MarkedClockPointMeasure.measure L v b T) ↔
      Integrable f (PredictableClockReference.reference L T) := by
  constructor
  · intro hi
    have htrim := hi.trim (PredictableClockSigma.predictable_le_ambient L) hf
    rw [trim_eq_reference L v b T] at htrim
    exact integrable_of_integrable_trim (PredictableClockSigma.predictable_le_ambient L) htrim
  · intro hi
    have htrim := hi.trim (PredictableClockSigma.predictable_le_ambient L) hf
    rw [← trim_eq_reference L v b T] at htrim
    exact integrable_of_integrable_trim (PredictableClockSigma.predictable_le_ambient L) htrim

theorem integrable_point_of_bounded (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → Real)
    (hf : StronglyMeasurable[(RationalProtectedExit.nnHistory L).predictable] f)
    (C : Real) (hC : ∀ q, ‖f q‖ ≤ C) :
    Integrable f (MarkedClockPointMeasure.measure L v b T) := by
  apply (integrable_const C).mono'
    (hf.mono (PredictableClockSigma.predictable_le_ambient L)).aestronglyMeasurable
  exact ae_of_all _ hC

theorem integrable_reference_of_bounded (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → Real)
    (hf : StronglyMeasurable[(RationalProtectedExit.nnHistory L).predictable] f)
    (C : Real) (hC : ∀ q, ‖f q‖ ≤ C) :
    Integrable f (PredictableClockReference.reference L T) :=
  (integrable_iff_reference L v b T f hf).mp (integrable_point_of_bounded L v b T f hf C hC)
end MathResearchAnalysis.MarkedPredictableCompensation
