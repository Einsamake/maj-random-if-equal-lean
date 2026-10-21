module
public import MathResearchAnalysis.MarkedRingCount
public import MathResearchAnalysis.ClockArrivalCountTail
public import MathResearchAnalysis.ProtectedExitResidual
set_option autoImplicit false
/-! Actual fixed-horizon arrival counts have finite expectation under the
constructed clock/mark law. The exponential bound is only an integrability
bound for counts, not a recovery-time bound, Poisson compensator or Dynkin law.
Real representatives are used only after their extended expectations are finite. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MarkedRingIntegrability
open MeasureTheory
open DropletClockLaw (Sample Event Vertex)

theorem geometric_shifted_half : (∑' k : Nat, ((2 : ENNReal)⁻¹)^(k+1)) = 1 := by
  calc
    _ = (∑' k : Nat, ((2 : ENNReal)⁻¹)^k) * (2 : ENNReal)⁻¹ := by
      simp_rw [pow_succ]
      exact ENNReal.tsum_mul_right
    _ = 2 * (2 : ENNReal)⁻¹ := by
      congr 1
      simpa only [one_div] using ENNReal.tsum_geometric_two
    _ = _ := by
      have h : (2 : ENNReal)⁻¹ * (2 * 1) = 1 :=
        ENNReal.inv_mul_cancel_left (by norm_num) (by norm_num)
      simpa only [mul_one,one_mul,mul_comm] using h

theorem count_lintegral_le (L : Nat) (v : Vertex L) (t : Real) :
    (∫⁻ z, MarkedRingCount.count L v t z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) ≤
      ENNReal.ofReal (Real.exp t) := by
  rw [MarkedRingCount.lintegral_count_eq_clock_tsum]
  calc
    _ ≤ ∑' k : Nat, ENNReal.ofReal (Real.exp t) * ((2 : ENNReal)⁻¹)^(k+1) :=
      ENNReal.tsum_le_tsum (fun k => ClockArrivalCountTail.arrival_measure_le v k t)
    _ = ENNReal.ofReal (Real.exp t) * (∑' k : Nat, ((2 : ENNReal)⁻¹)^(k+1)) := ENNReal.tsum_mul_left
    _ = _ := by rw [geometric_shifted_half,mul_one]

theorem markedCount_lintegral_le (L : Nat) (v : Vertex L) (b : Bool) (t : Real) :
    (∫⁻ z, MarkedRingCount.markedCount L v b t z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) ≤
      ENNReal.ofReal (Real.exp t) :=
  (lintegral_mono (fun z => MarkedRingCount.markedCount_le_count L v b t z)).trans (count_lintegral_le L v t)

theorem count_lintegral_ne_top (L : Nat) (v : Vertex L) (t : Real) :
    (∫⁻ z, MarkedRingCount.count L v t z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (count_lintegral_le L v t)

theorem markedCount_lintegral_ne_top (L : Nat) (v : Vertex L) (b : Bool) (t : Real) :
    (∫⁻ z, MarkedRingCount.markedCount L v b t z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (markedCount_lintegral_le L v b t)

theorem count_toReal_integrable (L : Nat) (v : Vertex L) (t : Real) :
    Integrable (fun z => (MarkedRingCount.count L v t z).toReal)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  integrable_toReal_of_lintegral_ne_top (MarkedRingCount.count_measurable L v t).aemeasurable
    (count_lintegral_ne_top L v t)

theorem markedCount_toReal_integrable (L : Nat) (v : Vertex L) (b : Bool) (t : Real) :
    Integrable (fun z => (MarkedRingCount.markedCount L v b t z).toReal)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  integrable_toReal_of_lintegral_ne_top (MarkedRingCount.markedCount_measurable L v b t).aemeasurable
    (markedCount_lintegral_ne_top L v b t)

theorem count_at_measurable (L : Nat) (v : Vertex L) (R : Sample L → Real) (hR : Measurable R) :
    Measurable (fun z => MarkedRingCount.count L v (R z) z) := by
  apply Measurable.tsum
  intro k
  exact Measurable.ite (measurableSet_le (MarkedClockFiltration.arrival_measurable L (v,k)) hR)
    measurable_const measurable_const

theorem markedCount_at_measurable (L : Nat) (v : Vertex L) (b : Bool) (R : Sample L → Real) (hR : Measurable R) :
    Measurable (fun z => MarkedRingCount.markedCount L v b (R z) z) := by
  apply Measurable.tsum
  intro k
  exact Measurable.ite ((measurableSet_le (MarkedClockFiltration.arrival_measurable L (v,k)) hR).inter
    (measurableSet_eq_fun (MarkedClockFiltration.mark_measurable L (v,k)) measurable_const))
    measurable_const measurable_const

theorem count_at_lintegral_le (L : Nat) (v : Vertex L) (R : Sample L → Real) (T : Real)
    (hRT : ∀ z, R z ≤ T) :
    (∫⁻ z, MarkedRingCount.count L v (R z) z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) ≤
      ENNReal.ofReal (Real.exp T) :=
  (lintegral_mono (fun z => MarkedRingCount.count_mono L v z (hRT z))).trans (count_lintegral_le L v T)

theorem markedCount_at_lintegral_le (L : Nat) (v : Vertex L) (b : Bool) (R : Sample L → Real) (T : Real)
    (hRT : ∀ z, R z ≤ T) :
    (∫⁻ z, MarkedRingCount.markedCount L v b (R z) z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) ≤
      ENNReal.ofReal (Real.exp T) :=
  (lintegral_mono (fun z => MarkedRingCount.markedCount_mono L v b z (hRT z))).trans
    (markedCount_lintegral_le L v b T)

theorem count_at_toReal_integrable (L : Nat) (v : Vertex L) (R : Sample L → Real) (hR : Measurable R)
    (T : Real) (hRT : ∀ z, R z ≤ T) :
    Integrable (fun z => (MarkedRingCount.count L v (R z) z).toReal)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  integrable_toReal_of_lintegral_ne_top (count_at_measurable L v R hR).aemeasurable
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (count_at_lintegral_le L v R T hRT))

theorem markedCount_at_toReal_integrable (L : Nat) (v : Vertex L) (b : Bool) (R : Sample L → Real) (hR : Measurable R)
    (T : Real) (hRT : ∀ z, R z ≤ T) :
    Integrable (fun z => (MarkedRingCount.markedCount L v b (R z) z).toReal)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  integrable_toReal_of_lintegral_ne_top (markedCount_at_measurable L v b R hR).aemeasurable
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (markedCount_at_lintegral_le L v b R T hRT))

theorem boundedExit_untopD_le_horizon (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (T : NNReal) (z : Sample L) :
    (ProtectedExitResidual.boundedExit L D I S T z).untopD 0 ≤ (T : Real) := by
  simpa only [ProtectedExitResidual.boundedExit,WithTop.untopD_coe,WithTop.coe_le_coe] using
    ProtectedExitResidual.boundedExit_le_horizon L D I S T z

theorem boundedExit_count_toReal_integrable (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (T : NNReal) (v : Vertex L) :
    Integrable (fun z => (MarkedRingCount.count L v
      ((ProtectedExitResidual.boundedExit L D I S T z).untopD 0) z).toReal)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  count_at_toReal_integrable L v (fun z => (ProtectedExitResidual.boundedExit L D I S T z).untopD 0)
    ((ProtectedExitResidual.boundedExit_isStoppingTime L D I S T).measurable'.untopD 0)
    (T : Real) (boundedExit_untopD_le_horizon L D I S T)

theorem boundedExit_markedCount_toReal_integrable (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (T : NNReal) (v : Vertex L) (b : Bool) :
    Integrable (fun z => (MarkedRingCount.markedCount L v b
      ((ProtectedExitResidual.boundedExit L D I S T z).untopD 0) z).toReal)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  markedCount_at_toReal_integrable L v b (fun z => (ProtectedExitResidual.boundedExit L D I S T z).untopD 0)
    ((ProtectedExitResidual.boundedExit_isStoppingTime L D I S T).measurable'.untopD 0)
    (T : Real) (boundedExit_untopD_le_horizon L D I S T)
end MathResearchAnalysis.MarkedRingIntegrability
