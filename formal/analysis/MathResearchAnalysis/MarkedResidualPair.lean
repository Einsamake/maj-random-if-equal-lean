module
public import MathResearchAnalysis.StoppedFreshMark
set_option autoImplicit false
/-! Full fixed-site residual wait/mark law in the original marked history. The flip preserves arbitrary measurable waiting events. Marginal independence alone is never used to infer pair independence. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MarkedResidualPair
open MeasureTheory ProbabilityTheory
open DropletClockLaw (Sample Event Vertex)
open UnrevealedMarkInvariance (flipSample)

def pair (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real) (z : Sample L) : Real × Bool :=
  (MarkedStoppedResidual.waiting L v R z,StoppedFreshMark.nextMark L v R z)

theorem pair_measurable (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) : Measurable (pair L v R) :=
  (MarkedStoppedResidual.waiting_measurable L v R hR).prodMk (StoppedFreshMark.nextMark_measurable L v R hR)

theorem waiting_event_factor (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R)
    (hfinite : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), R z ≠ ⊤)
    (E : Set (Sample L)) (hE : MeasurableSet[hR.measurableSpace] E)
    (A : Set Real) (hA : MeasurableSet A) (b : Bool) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      ((E ∩ (MarkedStoppedResidual.waiting L v R) ⁻¹' A) ∩ {z | StoppedFreshMark.nextMark L v R z = b}) =
        ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
          (E ∩ (MarkedStoppedResidual.waiting L v R) ⁻¹' A) * FairMarks.fair {b} := by
  rw [FairMarks.fair_singleton]
  apply StoppedFreshMark.invariant_factor L v R hR hfinite _
    ((hR.measurableSpace_le E hE).inter (hA.preimage (MarkedStoppedResidual.waiting_measurable L v R hR)))
  intro k z hc
  change (z ∈ E ∧ MarkedStoppedResidual.waiting L v R z ∈ A) ↔
    (flipSample L (v,k) z ∈ E ∧ MarkedStoppedResidual.waiting L v R (flipSample L (v,k) z) ∈ A)
  rw [StoppedMarkSlices.candidate_waiting_flip L v R hR k z hc]
  exact and_congr_left (fun _ => StoppedMarkSlices.candidate_stopped_event_flip_iff L v R hR k z hc E hE)

theorem waiting_event_mark_map (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R)
    (hfinite : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), R z ≠ ⊤)
    (E : Set (Sample L)) (hE : MeasurableSet[hR.measurableSpace] E)
    (A : Set Real) (hA : MeasurableSet A) :
    ((ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)).restrict
      (E ∩ (MarkedStoppedResidual.waiting L v R) ⁻¹' A)).map (StoppedFreshMark.nextMark L v R) =
        ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
          (E ∩ (MarkedStoppedResidual.waiting L v R) ⁻¹' A) • FairMarks.fair := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (StoppedFreshMark.nextMark_measurable L v R hR) (measurableSet_singleton b),
    Measure.restrict_apply ((measurableSet_singleton b).preimage (StoppedFreshMark.nextMark_measurable L v R hR)),
    Measure.smul_apply]
  simpa only [Set.preimage,Set.mem_singleton_iff,Set.inter_comm,smul_eq_mul] using
    waiting_event_factor L v R hR hfinite E hE A hA b

theorem rectangle_factor (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R)
    (hfinite : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), R z ≠ ⊤)
    (E : Set (Sample L)) (hE : MeasurableSet[hR.measurableSpace] E)
    (A : Set Real) (hA : MeasurableSet A) (B : Set Bool) (hB : MeasurableSet B) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      ((E ∩ (MarkedStoppedResidual.waiting L v R) ⁻¹' A) ∩ (StoppedFreshMark.nextMark L v R) ⁻¹' B) =
        ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
          (E ∩ (MarkedStoppedResidual.waiting L v R) ⁻¹' A) * FairMarks.fair B := by
  have h := congrArg (fun ν : Measure Bool => ν B) (waiting_event_mark_map L v R hR hfinite E hE A hA)
  rw [Measure.map_apply (StoppedFreshMark.nextMark_measurable L v R hR) hB,
    Measure.restrict_apply (hB.preimage (StoppedFreshMark.nextMark_measurable L v R hR)),Measure.smul_apply] at h
  simpa only [Set.inter_comm,smul_eq_mul] using h

theorem restricted_map_eq (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) (hpos : ∀ z, 0 ≤ R z)
    (hfinite : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), R z ≠ ⊤)
    (E : Set (Sample L)) (hE : MeasurableSet[hR.measurableSpace] E) :
    ((ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)).restrict E).map (pair L v R) =
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) E • ((expMeasure 1).prod FairMarks.fair) := by
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply (pair_measurable L v R hR) (hA.prod hB),
    Measure.restrict_apply ((hA.prod hB).preimage (pair_measurable L v R hR)),Measure.smul_apply,Measure.prod_prod]
  have heq : (pair L v R) ⁻¹' (A ×ˢ B) ∩ E =
      (E ∩ (MarkedStoppedResidual.waiting L v R) ⁻¹' A) ∩ (StoppedFreshMark.nextMark L v R) ⁻¹' B := by
    ext z
    simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_prod,pair]
    tauto
  rw [heq,rectangle_factor L v R hR hfinite E hE A hA B hB]
  have hw := congrArg (fun ν : Measure Real => ν A)
    (SurvivalLaw.restricted_map_eq (MarkedStoppedResidual.waiting_measurable L v R hR)
      (MarkedStoppedResidual.waiting_nonnegative L v R) hR.measurableSpace_le
      (MarkedStoppedResidual.waiting_jointSurvival L v R hR hpos hfinite) E hE)
  rw [Measure.map_apply (MarkedStoppedResidual.waiting_measurable L v R hR) hA,
    Measure.restrict_apply (hA.preimage (MarkedStoppedResidual.waiting_measurable L v R hR)),Measure.smul_apply] at hw
  have hw' : ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      (E ∩ (MarkedStoppedResidual.waiting L v R) ⁻¹' A) =
        ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) E * expMeasure 1 A := by
    simpa only [Set.inter_comm,smul_eq_mul] using hw
  rw [hw',smul_eq_mul,mul_assoc]

theorem pair_hasLaw (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) (hpos : ∀ z, 0 ≤ R z)
    (hfinite : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), R z ≠ ⊤) :
    HasLaw (pair L v R) ((expMeasure 1).prod FairMarks.fair)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  refine ⟨(pair_measurable L v R hR).aemeasurable,?_⟩
  simpa only [Measure.restrict_univ,measure_univ,one_smul] using
    restricted_map_eq L v R hR hpos hfinite Set.univ MeasurableSet.univ

theorem pair_independent_stopped_history (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) (hpos : ∀ z, 0 ≤ R z)
    (hfinite : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), R z ≠ ⊤) :
    Indep ((inferInstance : MeasurableSpace (Real × Bool)).comap (pair L v R)) hR.measurableSpace
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  rw [Indep_iff]
  intro A E hA hE
  rcases MeasurableSpace.measurableSet_comap.mp hA with ⟨B,hB,rfl⟩
  have h := congrArg (fun ν : Measure (Real × Bool) => ν B) (restricted_map_eq L v R hR hpos hfinite E hE)
  rw [Measure.map_apply (pair_measurable L v R hR) hB,
    Measure.restrict_apply (hB.preimage (pair_measurable L v R hR)),Measure.smul_apply] at h
  have hm : ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) ((pair L v R) ⁻¹' B) =
      (expMeasure 1).prod FairMarks.fair B := by
    rw [← (pair_hasLaw L v R hR hpos hfinite).map_eq,Measure.map_apply (pair_measurable L v R hR) hB]
  simpa only [hm,smul_eq_mul,mul_comm] using h

theorem waiting_mark_independent (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R)
    (hfinite : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), R z ≠ ⊤) :
    IndepFun (MarkedStoppedResidual.waiting L v R) (StoppedFreshMark.nextMark L v R)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B hA hB
  have h := rectangle_factor L v R hR hfinite Set.univ MeasurableSet.univ A hA B hB
  have hm : ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      ((StoppedFreshMark.nextMark L v R) ⁻¹' B) = FairMarks.fair B := by
    rw [← (StoppedFreshMark.nextMark_hasLaw L v R hR hfinite).map_eq,
      Measure.map_apply (StoppedFreshMark.nextMark_measurable L v R hR) hB]
  simpa only [Set.univ_inter,hm] using h

theorem boundedExit_pair_hasLaw (L : Nat) (D I S : Finset InfiniteGridModel.Site) (T : NNReal) (v : Vertex L) :
    HasLaw (pair L v (ProtectedExitResidual.boundedExit L D I S T)) ((expMeasure 1).prod FairMarks.fair)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  pair_hasLaw L v (ProtectedExitResidual.boundedExit L D I S T)
    (ProtectedExitResidual.boundedExit_isStoppingTime L D I S T)
    (ProtectedExitResidual.boundedExit_nonnegative L D I S T)
    (Filter.Eventually.of_forall (ProtectedExitResidual.boundedExit_ne_top L D I S T))

theorem boundedExit_pair_independent_stopped_history (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (T : NNReal) (v : Vertex L) :
    Indep ((inferInstance : MeasurableSpace (Real × Bool)).comap (pair L v (ProtectedExitResidual.boundedExit L D I S T)))
      (ProtectedExitResidual.boundedExit_isStoppingTime L D I S T).measurableSpace
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  pair_independent_stopped_history L v (ProtectedExitResidual.boundedExit L D I S T)
    (ProtectedExitResidual.boundedExit_isStoppingTime L D I S T)
    (ProtectedExitResidual.boundedExit_nonnegative L D I S T)
    (Filter.Eventually.of_forall (ProtectedExitResidual.boundedExit_ne_top L D I S T))
end MathResearchAnalysis.MarkedResidualPair
