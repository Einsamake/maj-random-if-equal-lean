module
public import MathResearchAnalysis.MarkedClockPointMeasure
public import MathResearchAnalysis.MarkedConditionalCount
set_option autoImplicit false
/-! Genuine marked event-point masses on future rectangles determined by
original past events. The original joint history is used without replacing
it by its right continuation. This is not a full predictable compensation
formula or equality on the ambient time/sample product sigma-algebra. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MarkedPredictableRectangles
open MeasureTheory Set
open DropletClockLaw (Sample Vertex)
open MarkedClockPointMeasure (point measure carrier)

theorem point_time_gt_iff (L : Nat) (v : Vertex L) (k : Nat) (s : NNReal)
    (z : Sample L) : s < (point L v k z).1 ↔
      (s : Real) < ClockEventWord.eventTime z.1 (v,k) := by
  change s < (ClockEventWord.eventTime z.1 (v,k)).toNNReal ↔ _
  rw [← not_le, Real.toNNReal_le_iff_le_coe, not_le]

/-- A future rectangle carries exactly the original conditional marked
arrival mass. Every hypothesis refers to the original joint history. -/
theorem future_rectangle_of_le (L : Nat) (v : Vertex L) (b : Bool) (T s : NNReal)
    (hsT : s ≤ T) (E : Set (Sample L))
    (hE : MeasurableSet[MarkedClockFiltration.history L (s : Real)] E) :
    measure L v b T (Ioi s ×ˢ E) = ENNReal.ofReal (((T : Real)-(s : Real))/2) *
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) E := by
  have hEa : MeasurableSet E := (MarkedClockFiltration.history L).le (s : Real) E hE
  rw [MarkedClockPointMeasure.measure_apply L v b T _ (measurableSet_Ioi.prod hEa)]
  calc
    _ = ∑' k : Nat, ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
        {z : Sample L | z ∈ E ∧ (s : Real) < ClockEventWord.eventTime z.1 (v,k) ∧
          ClockEventWord.eventTime z.1 (v,k) ≤ (T : Real) ∧ z.2 (v,k) = b} := by
      apply tsum_congr
      intro k
      congr 1
      ext z
      change ((0 < ClockEventWord.eventTime z.1 (v,k) ∧
        ClockEventWord.eventTime z.1 (v,k) ≤ (T : Real) ∧ z.2 (v,k) = b) ∧
        (s < (point L v k z).1 ∧ z ∈ E)) ↔ _
      rw [point_time_gt_iff]
      constructor
      · rintro ⟨⟨_,ht,hb⟩,hs,hz⟩
        exact ⟨hz,hs,ht,hb⟩
      · rintro ⟨hz,hs,ht,hb⟩
        exact ⟨⟨lt_of_le_of_lt s.property hs,ht,hb⟩,hs,hz⟩
    _ = ∫⁻ z in E, MarkedConditionalCount.markedCount L v b (s : Real) (T : Real) z
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) :=
      (MarkedConditionalCount.lintegral_markedCount_eq_tsum L v b (s : Real) (T : Real) E).symm
    _ = _ := MarkedConditionalCount.markedCount_lintegral_on_history L v b
      (s : Real) (T : Real) s.property (by exact_mod_cast hsT) E hE

/-- Rectangles beginning at or beyond the horizon have no mass, even for
nonmeasurable sample sets. Concentration alone supplies this conclusion. -/
theorem future_rectangle_zero (L : Nat) (v : Vertex L) (b : Bool) (T s : NNReal)
    (hTs : T ≤ s) (E : Set (Sample L)) : measure L v b T (Ioi s ×ˢ E) = 0 := by
  apply le_antisymm _ bot_le
  calc
    _ ≤ measure L v b T (carrier L T)ᶜ := by
      apply measure_mono
      intro q hq hc
      have hstrict : s < q.1 := hq.1
      have hbound : q.1 ≤ T := hc.1.2
      exact (not_lt.mpr (hbound.trans hTs)) hstrict
    _ = 0 := MarkedClockPointMeasure.measure_compl_carrier L v b T

/-- The positive-part coefficient handles rectangles extending past the
finite horizon without any changed filtration. -/
theorem future_rectangle (L : Nat) (v : Vertex L) (b : Bool) (T s : NNReal)
    (E : Set (Sample L))
    (hE : MeasurableSet[MarkedClockFiltration.history L (s : Real)] E) :
    measure L v b T (Ioi s ×ˢ E) = ENNReal.ofReal (((T : Real)-(s : Real))/2) *
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) E := by
  by_cases hsT : s ≤ T
  · exact future_rectangle_of_le L v b T s hsT E hE
  · have hTs : T ≤ s := le_of_not_ge hsT
    rw [future_rectangle_zero L v b T s hTs E,
      ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (by exact_mod_cast hTs)) (by norm_num)), zero_mul]

/-- Time zero contributes no event points. No measurability of E is needed. -/
theorem zero_rectangle (L : Nat) (v : Vertex L) (b : Bool) (T : NNReal)
    (E : Set (Sample L)) : measure L v b T ({0} ×ˢ E) = 0 := by
  apply le_antisymm _ bot_le
  calc
    _ ≤ measure L v b T (carrier L T)ᶜ := by
      apply measure_mono
      intro q hq hc
      have hzero : q.1 = 0 := Set.mem_singleton_iff.mp hq.1
      exact (ne_of_gt hc.1.1) hzero
    _ = 0 := MarkedClockPointMeasure.measure_compl_carrier L v b T
end MathResearchAnalysis.MarkedPredictableRectangles
