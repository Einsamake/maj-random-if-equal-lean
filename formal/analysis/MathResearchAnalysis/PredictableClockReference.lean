module
public import MathResearchAnalysis.DropletClockLaw
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.Prod
set_option autoImplicit false
/-! A genuine finite Lebesgue-time reference measure for one fair mark.
Time is actual real Lebesgue volume on (0,T], mapped into NNReal; sample
measure is the original clock/mark law. No equality to the actual event
measure, Poisson characterization or compensation theorem is presumed. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.PredictableClockReference
open MeasureTheory Set
open DropletClockLaw (Sample)

def timeMeasure (T : NNReal) : Measure NNReal :=
  ((volume : Measure Real).restrict (Ioc (0 : Real) (T : Real))).map Real.toNNReal

def reference (L : Nat) (T : NNReal) : Measure (NNReal × Sample L) :=
  (2 : ENNReal)⁻¹ • ((timeMeasure T).prod
    (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)))

theorem timeMeasure_apply (T : NNReal) (A : Set NNReal) (hA : MeasurableSet A) :
    timeMeasure T A = (volume : Measure Real)
      (Real.toNNReal ⁻¹' A ∩ Ioc (0 : Real) (T : Real)) := by
  rw [timeMeasure,Measure.map_apply measurable_real_toNNReal hA,
    Measure.restrict_apply (hA.preimage measurable_real_toNNReal)]

theorem timeMeasure_univ (T : NNReal) : timeMeasure T univ = ENNReal.ofReal (T : Real) := by
  rw [timeMeasure_apply T _ MeasurableSet.univ]
  simp only [Set.preimage_univ,Set.univ_inter,Real.volume_Ioc,sub_zero]

instance timeMeasure_finite (T : NNReal) : IsFiniteMeasure (timeMeasure T) where
  measure_univ_lt_top := by rw [timeMeasure_univ]; exact ENNReal.ofReal_lt_top

/-- The positive part automatically handles a threshold beyond the horizon. -/
theorem timeMeasure_Ioi (T s : NNReal) :
    timeMeasure T (Ioi s) = ENNReal.ofReal ((T : Real)-(s : Real)) := by
  rw [timeMeasure_apply T _ measurableSet_Ioi]
  have hset : Real.toNNReal ⁻¹' Ioi s ∩ Ioc (0 : Real) (T : Real) =
      Ioc (s : Real) (T : Real) := by
    ext u
    have hgt : s < u.toNNReal ↔ (s : Real) < u := by
      rw [← not_le, Real.toNNReal_le_iff_le_coe, not_le]
    change (s < u.toNNReal ∧ 0 < u ∧ u ≤ (T : Real)) ↔
      ((s : Real) < u ∧ u ≤ (T : Real))
    rw [hgt]
    constructor
    · rintro ⟨hs,_,hT⟩
      exact ⟨hs,hT⟩
    · rintro ⟨hs,hT⟩
      exact ⟨hs,lt_of_le_of_lt s.property hs,hT⟩
  rw [hset,Real.volume_Ioc]

theorem timeMeasure_zero (T : NNReal) : timeMeasure T {0} = 0 := by
  rw [timeMeasure_apply T _ (measurableSet_singleton 0)]
  have hset : Real.toNNReal ⁻¹' ({0} : Set NNReal) ∩ Ioc (0 : Real) (T : Real) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have hz : u.toNNReal = 0 := hu.1
    have hp : 0 < u.toNNReal := Real.toNNReal_pos.mpr hu.2.1
    exact (ne_of_gt hp) hz
  rw [hset,measure_empty]

/-- Product rectangle masses require no sample-set measurability assumption. -/
theorem reference_apply_prod (L : Nat) (T : NNReal) (A : Set NNReal)
    (E : Set (Sample L)) : reference L T (A ×ˢ E) =
      (2 : ENNReal)⁻¹ * timeMeasure T A *
        ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) E := by
  rw [reference,Measure.smul_apply,Measure.prod_prod,smul_eq_mul,mul_assoc]

theorem reference_univ (L : Nat) (T : NNReal) :
    reference L T univ = ENNReal.ofReal ((T : Real)/2) := by
  have hu : (univ : Set (NNReal × Sample L)) = univ ×ˢ univ := Set.univ_prod_univ.symm
  rw [hu,reference_apply_prod,timeMeasure_univ,measure_univ,mul_one,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real) < 2)]
  norm_num [div_eq_mul_inv,mul_comm]

instance reference_finite (L : Nat) (T : NNReal) : IsFiniteMeasure (reference L T) where
  measure_univ_lt_top := by rw [reference_univ]; exact ENNReal.ofReal_lt_top

theorem reference_future_rectangle (L : Nat) (T s : NNReal) (E : Set (Sample L)) :
    reference L T (Ioi s ×ˢ E) =
      ENNReal.ofReal (((T : Real)-(s : Real))/2) *
        ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) E := by
  rw [reference_apply_prod,timeMeasure_Ioi,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real) < 2)]
  norm_num [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]

theorem reference_zero_rectangle (L : Nat) (T : NNReal) (E : Set (Sample L)) :
    reference L T ({0} ×ˢ E) = 0 := by
  rw [reference_apply_prod,timeMeasure_zero,mul_zero,zero_mul]

/-- The reference integral is actual real-time integration under the
original sample law, with the fair-mark coefficient one half. -/
theorem lintegral_reference (L : Nat) (T : NNReal)
    (f : NNReal × Sample L → ENNReal) (hf : Measurable f) :
    (∫⁻ q, f q ∂reference L T) = (2 : ENNReal)⁻¹ *
      ∫⁻ u : Real in Ioc (0 : Real) (T : Real),
        ∫⁻ z : Sample L, f (u.toNNReal,z)
          ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  have hi : Measurable (fun u : NNReal =>
      ∫⁻ z : Sample L, f (u,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
    hf.lintegral_prod_right'
  rw [reference,lintegral_smul_measure,smul_eq_mul,
    lintegral_prod _ hf.aemeasurable]
  congr 1
  exact lintegral_map hi measurable_real_toNNReal
end MathResearchAnalysis.PredictableClockReference
