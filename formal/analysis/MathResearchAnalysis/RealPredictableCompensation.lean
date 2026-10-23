module
public import MathResearchAnalysis.MarkedPredictableCompensation
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
set_option autoImplicit false
/-! Signed compensation for the original marked arrivals. A finite integral
of absolute event scores is established before exchanging series and Bochner
integrals. Thus the actual event-score series is absolutely summable almost
everywhere and its pathwise sum is genuinely integrable. The final bounded
predictable theorem has no assumed event law or compensation identity.
Exceptional paths are not asserted finite; the underlying ENNReal counts and
infinite recovery times are unchanged. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.RealPredictableCompensation
open MeasureTheory Set
open scoped ENNReal
open DropletClockLaw (Sample Vertex)

def term (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → Real) (k : Nat) (z : Sample L) : Real :=
  (MarkedClockPointMeasure.window L v b T k).indicator
    (fun z => f (MarkedClockPointMeasure.point L v k z)) z

def pathSum (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → Real) (z : Sample L) : Real :=
  ∑' k : Nat, term L v b T f k z

theorem term_measurable (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → Real) (hf : Measurable f) (k : Nat) :
    Measurable (term L v b T f k) :=
  (hf.comp (MarkedClockPointMeasure.point_measurable L v k)).indicator
    (MarkedClockPointMeasure.window_measurable L v b T k)

theorem pathSum_measurable (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → Real) (hf : Measurable f) :
    Measurable (pathSum L v b T f) :=
  Measurable.tsum (fun k => term_measurable L v b T f hf k)

theorem norm_integral_sum_eq (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → Real) (hf : Measurable f) :
    (∑' k : Nat, ∫⁻ z, ‖term L v b T f k z‖ₑ
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    ∫⁻ q, ‖f q‖ₑ ∂MarkedClockPointMeasure.measure L v b T := by
  rw [MarkedClockPointMeasure.lintegral_eq_tsum L v b T (fun q => ‖f q‖ₑ) hf.enorm]
  apply tsum_congr
  intro k
  rw [← lintegral_indicator (MarkedClockPointMeasure.window_measurable L v b T k)]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ MarkedClockPointMeasure.window L v b T k <;>
    simp [term, hz]

theorem term_norm_sum_finite (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → Real) (hf : Measurable f)
    (hi : Integrable f (MarkedClockPointMeasure.measure L v b T)) :
    (∑' k : Nat, ∫⁻ z, ‖term L v b T f k z‖ₑ
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) ≠ ∞ := by
  rw [norm_integral_sum_eq L v b T f hf]
  exact hi.hasFiniteIntegral.ne

theorem term_absolutely_summable_ae (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → Real) (hf : Measurable f)
    (hi : Integrable f (MarkedClockPointMeasure.measure L v b T)) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      Summable (fun k => ‖term L v b T f k z‖) := by
  have hnorm := term_norm_sum_finite L v b T f hf hi
  rw [← lintegral_tsum (fun k => (term_measurable L v b T f hf k).enorm.aemeasurable)] at hnorm
  filter_upwards [ae_lt_top' (Measurable.tsum (fun k =>
    (term_measurable L v b T f hf k).enorm)).aemeasurable hnorm] with z hz
  exact tsum_enorm_ne_top_iff_summable_norm.mp hz.ne

theorem pathSum_integrable (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → Real) (hf : Measurable f)
    (hi : Integrable f (MarkedClockPointMeasure.measure L v b T)) :
    Integrable (pathSum L v b T f)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  have hm : Measurable (fun z => ∑' k : Nat, ‖term L v b T f k z‖ₑ) :=
    Measurable.tsum (fun k => (term_measurable L v b T f hf k).enorm)
  have hnorm : (∫⁻ z, ∑' k : Nat, ‖term L v b T f k z‖ₑ
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) ≠ ∞ := by
    rw [lintegral_tsum (fun k => (term_measurable L v b T f hf k).enorm.aemeasurable)]
    exact term_norm_sum_finite L v b T f hf hi
  apply (integrable_toReal_of_lintegral_ne_top hm.aemeasurable hnorm).mono'
    (pathSum_measurable L v b T f hf).aestronglyMeasurable
  filter_upwards [ae_lt_top' hm.aemeasurable hnorm] with z hz
  have hle := ENNReal.toReal_mono hz.ne
    (enorm_tsum_le_tsum_enorm (f := fun k => term L v b T f k z))
  simpa only [pathSum, toReal_enorm] using hle

theorem integral_pathSum_eq_point (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → Real) (hf : Measurable f)
    (hi : Integrable f (MarkedClockPointMeasure.measure L v b T)) :
    (∫ z, pathSum L v b T f z
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    ∫ q, f q ∂MarkedClockPointMeasure.measure L v b T := by
  change (∫ z, ∑' k, term L v b T f k z
    ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) = _
  rw [integral_tsum (fun k => (term_measurable L v b T f hf k).aestronglyMeasurable)
    (term_norm_sum_finite L v b T f hf hi)]
  rw [MarkedClockPointMeasure.measure, integral_sum_measure hi]
  apply tsum_congr
  intro k
  rw [integral_map_of_stronglyMeasurable (MarkedClockPointMeasure.point_measurable L v k) hf.stronglyMeasurable]
  exact integral_indicator (MarkedClockPointMeasure.window_measurable L v b T k)

/-- The actual finite-time product has the original sample law and genuine
Lebesgue time. Boundedness proves integrability before Fubini is used. -/
theorem time_product_integrable (L : Nat) (T : NNReal)
    (f : NNReal × Sample L → Real) (hf : StronglyMeasurable f)
    (C : Real) (hC : ∀ q, ‖f q‖ ≤ C) :
    Integrable f ((PredictableClockReference.timeMeasure T).prod
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L))) := by
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  exact ae_of_all _ hC

theorem sample_integrable (L : Nat) (f : NNReal × Sample L → Real)
    (hf : StronglyMeasurable f) (C : Real) (hC : ∀ q, ‖f q‖ ≤ C) (u : NNReal) :
    Integrable (fun z => f (u,z))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  apply (integrable_const C).mono'
    (hf.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact ae_of_all _ (fun z => hC (u,z))

theorem time_mean_integrable (L : Nat) (T : NNReal)
    (f : NNReal × Sample L → Real) (hf : StronglyMeasurable f)
    (C : Real) (hC : ∀ q, ‖f q‖ ≤ C) :
    Integrable (fun u : Real => ∫ z, f (u.toNNReal,z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L))
      ((volume : Measure Real).restrict (Ioc 0 (T : Real))) := by
  have hi := (time_product_integrable L T f hf C hC).integral_prod_left
  exact hi.comp_measurable measurable_real_toNNReal

theorem integral_reference_eq_time (L : Nat) (T : NNReal)
    (f : NNReal × Sample L → Real) (hf : StronglyMeasurable f)
    (C : Real) (hC : ∀ q, ‖f q‖ ≤ C) :
    (∫ q, f q ∂PredictableClockReference.reference L T) =
      (1 / 2 : Real) * ∫ u : Real in Ioc 0 (T : Real),
        ∫ z, f (u.toNNReal,z)
          ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  rw [PredictableClockReference.reference, integral_smul_measure,
    integral_prod f (time_product_integrable L T f hf C hC)]
  have hm : StronglyMeasurable (fun u : NNReal => ∫ z, f (u,z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
    hf.integral_prod_right'
  rw [PredictableClockReference.timeMeasure,
    integral_map_of_stronglyMeasurable measurable_real_toNNReal hm]
  norm_num

/-- A bounded predictable real score has an actual absolutely summable
pathwise event sum, an integrable expectation and the genuine time-integral
formula. The current fair mark enters only through the factor one half. -/
theorem bounded_predictable_integrable (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → Real)
    (hf : StronglyMeasurable[(RationalProtectedExit.nnHistory L).predictable] f)
    (C : Real) (hC : ∀ q, ‖f q‖ ≤ C) :
    Integrable (pathSum L v b T f)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  pathSum_integrable L v b T f
    (hf.mono (PredictableClockSigma.predictable_le_ambient L)).measurable
    (MarkedPredictableCompensation.integrable_point_of_bounded L v b T f hf C hC)

theorem bounded_predictable_absolutely_summable_ae
    (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → Real)
    (hf : StronglyMeasurable[(RationalProtectedExit.nnHistory L).predictable] f)
    (C : Real) (hC : ∀ q, ‖f q‖ ≤ C) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      Summable (fun k => ‖term L v b T f k z‖) :=
  term_absolutely_summable_ae L v b T f
    (hf.mono (PredictableClockSigma.predictable_le_ambient L)).measurable
    (MarkedPredictableCompensation.integrable_point_of_bounded L v b T f hf C hC)

theorem bounded_predictable_integral_eq_point
    (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → Real)
    (hf : StronglyMeasurable[(RationalProtectedExit.nnHistory L).predictable] f)
    (C : Real) (hC : ∀ q, ‖f q‖ ≤ C) :
    (∫ z, pathSum L v b T f z
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    ∫ q, f q ∂MarkedClockPointMeasure.measure L v b T :=
  integral_pathSum_eq_point L v b T f
    (hf.mono (PredictableClockSigma.predictable_le_ambient L)).measurable
    (MarkedPredictableCompensation.integrable_point_of_bounded L v b T f hf C hC)

theorem bounded_predictable_integral_eq_time (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (f : NNReal × Sample L → Real)
    (hf : StronglyMeasurable[(RationalProtectedExit.nnHistory L).predictable] f)
    (C : Real) (hC : ∀ q, ‖f q‖ ≤ C) :
    (∫ z, pathSum L v b T f z
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      (1 / 2 : Real) * ∫ u : Real in Ioc 0 (T : Real),
        ∫ z, f (u.toNNReal,z)
          ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  have hfa := hf.mono (PredictableClockSigma.predictable_le_ambient L)
  rw [integral_pathSum_eq_point L v b T f hfa.measurable
    (MarkedPredictableCompensation.integrable_point_of_bounded L v b T f hf C hC),
    MarkedPredictableCompensation.integral_eq_reference L v b T f hf]
  exact integral_reference_eq_time L T f hfa C hC

end MathResearchAnalysis.RealPredictableCompensation
