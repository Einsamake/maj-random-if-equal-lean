module
public import MathResearchAnalysis.StoppedMarkSlices
public import MathResearchAnalysis.ProtectedExitResidual
set_option autoImplicit false
/-! The actual first strictly future site-ring mark at a joint-history stopping time. The total definition keeps a false fallback when no future ring exists; actual cofinal clocks and almost-sure finite readiness remove that branch only almost everywhere. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.StoppedFreshMark
open MeasureTheory ProbabilityTheory
open DropletClockLaw (Sample Event Vertex)
open StoppedMarkSlices (candidate)
open UnrevealedMarkInvariance (flipSample)

def nextMark (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real) (z : Sample L) : Bool := by
  classical
  exact if hex : ∃ k, R z < (ClockEventWord.eventTime z.1 (v,k) : WithTop Real) then
    z.2 (v,Nat.find hex) else false

theorem candidate_find (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real) (z : Sample L)
    (hex : ∃ k, R z < (ClockEventWord.eventTime z.1 (v,k) : WithTop Real)) :
    candidate L v R (Nat.find hex) z := by
  refine ⟨Nat.find_spec hex,?_⟩
  intro j
  exact le_of_not_gt (Nat.find_min hex j.isLt)

theorem candidate_exists_iff (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real) (z : Sample L) :
    (∃ k, candidate L v R k z) ↔ ∃ k, R z < (ClockEventWord.eventTime z.1 (v,k) : WithTop Real) := by
  constructor
  · rintro ⟨k,hk⟩; exact ⟨k,hk.1⟩
  · intro hex; exact ⟨Nat.find hex,candidate_find L v R z hex⟩

theorem nextMark_eq_of_candidate (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (z : Sample L) (k : Nat) (hc : candidate L v R k z) : nextMark L v R z = z.2 (v,k) := by
  have hex : ∃ j, R z < (ClockEventWord.eventTime z.1 (v,j) : WithTop Real) := ⟨k,hc.1⟩
  have he := StoppedMarkSlices.candidate_unique L v R z (Nat.find hex) k (candidate_find L v R z hex) hc
  simp only [nextMark,dite_eq_left hex,he]

theorem nextMark_fiber (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real) (z : Sample L) (b : Bool) :
    nextMark L v R z = b ↔ (∃ k, candidate L v R k z ∧ z.2 (v,k) = b) ∨
      (¬ ∃ k, candidate L v R k z) ∧ false = b := by
  classical
  by_cases hc : ∃ k, candidate L v R k z
  · obtain ⟨k,hk⟩ := hc
    rw [nextMark_eq_of_candidate L v R z k hk]
    constructor
    · intro hb; exact Or.inl ⟨k,hk,hb⟩
    · rintro (⟨j,hj,hb⟩ | ⟨hno,_⟩)
      · rwa [StoppedMarkSlices.candidate_unique L v R z k j hk hj]
      · exact False.elim (hno ⟨k,hk⟩)
  · have hn := not_congr (candidate_exists_iff L v R z)
    have hfuture := hn.mp hc
    simp only [nextMark,dite_eq_right hfuture,hc,not_false_eq_true,true_and]
    constructor
    · exact Or.inr
    · rintro (⟨k,hk,_⟩ | hb)
      · exact False.elim (hc ⟨k,hk⟩)
      · exact hb

theorem nextMark_measurable (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) : Measurable (nextMark L v R) := by
  apply measurable_to_countable'
  intro b
  have heq : {z | nextMark L v R z = b} =
      (⋃ k : Nat, {z | candidate L v R k z} ∩ {z | z.2 (v,k) = b}) ∪
      (⋃ k : Nat, {z | candidate L v R k z})ᶜ ∩ {z | false = b} := by
    ext z
    simpa only [Set.mem_union,Set.mem_iUnion,Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_ofPred_eq] using
      nextMark_fiber L v R z b
  change MeasurableSet {z | nextMark L v R z = b}
  rw [heq]
  exact (MeasurableSet.iUnion fun k => (StoppedMarkSlices.candidate_measurable L v R hR k).inter
      (measurableSet_eq_fun (MarkedClockFiltration.mark_measurable L (v,k)) measurable_const)).union
    ((MeasurableSet.iUnion fun k => StoppedMarkSlices.candidate_measurable L v R hR k).compl.inter
      (MeasurableSet.const _))

theorem candidate_exists_ae (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hfinite : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), R z ≠ ⊤) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∃ k, candidate L v R k z := by
  have hco : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      ∀ r : Real, ∃ k, r < ArrivalFiltration.chronologicalArrival v k z.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := ExponentialClocks.clockMeasure (Vertex L))
      (ν := FairMarks.markMeasure (Event L))).ae (ClockReadiness.arrival_cofinal_ae v)
  filter_upwards [hfinite,hco] with z hr hc
  apply (candidate_exists_iff L v R z).mpr
  exact ExtendedNextRing.future_of_finite_cofinal
    (fun k (z : Sample L) => ClockEventWord.eventTime z.1 (v,k)) R z hr hc

theorem candidate_partition_tsum (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R)
    (hfinite : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), R z ≠ ⊤)
    (G : Set (Sample L)) (hG : MeasurableSet G) :
    (∑' k : Nat, ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) ({z | candidate L v R k z} ∩ G)) =
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) G := by
  have hcover : (⋃ k : Nat, {z | candidate L v R k z} ∩ G)
      =ᵐ[ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)] G := by
    filter_upwards [candidate_exists_ae L v R hfinite] with z hz
    simp only [Set.mem_iUnion,Set.mem_inter_iff,Set.mem_ofPred_eq]
    exact propext ⟨fun ⟨_,_,hg⟩ => hg,fun hg => let ⟨k,hk⟩ := hz; ⟨k,hk,hg⟩⟩
  calc
    _ = ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) (⋃ k : Nat, {z | candidate L v R k z} ∩ G) := by
      symm
      apply measure_iUnion
      · intro i j hij
        apply Set.disjoint_left.mpr
        intro z hi hj
        exact hij (StoppedMarkSlices.candidate_unique L v R z i j hi.1 hj.1)
      · exact fun k => (StoppedMarkSlices.candidate_measurable L v R hR k).inter hG
    _ = _ := measure_congr hcover

theorem marked_partition_tsum (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R)
    (hfinite : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), R z ≠ ⊤)
    (G : Set (Sample L)) (hG : MeasurableSet G) (b : Bool) :
    (∑' k : Nat, ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      ({z | candidate L v R k z} ∩ G ∩ {z | z.2 (v,k) = b})) =
        ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) (G ∩ {z | nextMark L v R z = b}) := by
  have heq : ∀ k, {z | candidate L v R k z} ∩ G ∩ {z | z.2 (v,k) = b} =
      {z | candidate L v R k z} ∩ (G ∩ {z | nextMark L v R z = b}) := by
    intro k
    ext z
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hc,hg⟩,hb⟩
      exact ⟨hc,hg,(nextMark_eq_of_candidate L v R z k hc).trans hb⟩
    · rintro ⟨hc,hg,hb⟩
      exact ⟨⟨hc,hg⟩,(nextMark_eq_of_candidate L v R z k hc).symm.trans hb⟩
  simp_rw [heq]
  exact candidate_partition_tsum L v R hR hfinite _
    (hG.inter (measurableSet_eq_fun (nextMark_measurable L v R hR) measurable_const))

theorem invariant_factor (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R)
    (hfinite : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), R z ≠ ⊤)
    (G : Set (Sample L)) (hG : MeasurableSet G)
    (hinv : ∀ k z, candidate L v R k z → (z ∈ G ↔ flipSample L (v,k) z ∈ G)) (b : Bool) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) (G ∩ {z | nextMark L v R z = b}) =
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) G * (2 : ENNReal)⁻¹ := by
  rw [← marked_partition_tsum L v R hR hfinite G hG b]
  simp_rw [StoppedMarkSlices.candidate_slice_factor L v R hR _ G hG (hinv _) b]
  rw [ENNReal.tsum_mul_right,candidate_partition_tsum L v R hR hfinite G hG]

theorem stopped_history_factor (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R)
    (hfinite : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), R z ≠ ⊤)
    (E : Set (Sample L)) (hE : MeasurableSet[hR.measurableSpace] E) (b : Bool) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) (E ∩ {z | nextMark L v R z = b}) =
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) E * FairMarks.fair {b} := by
  rw [FairMarks.fair_singleton]
  exact invariant_factor L v R hR hfinite E (hR.measurableSpace_le E hE)
    (fun k z hc => StoppedMarkSlices.candidate_stopped_event_flip_iff L v R hR k z hc E hE) b

theorem restricted_map_eq (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R)
    (hfinite : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), R z ≠ ⊤)
    (E : Set (Sample L)) (hE : MeasurableSet[hR.measurableSpace] E) :
    ((ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)).restrict E).map (nextMark L v R) =
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) E • FairMarks.fair := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (nextMark_measurable L v R hR) (measurableSet_singleton b),
    Measure.restrict_apply ((measurableSet_singleton b).preimage (nextMark_measurable L v R hR)),Measure.smul_apply]
  simpa only [Set.preimage,Set.mem_singleton_iff,Set.inter_comm,smul_eq_mul] using
    stopped_history_factor L v R hR hfinite E hE b

theorem nextMark_hasLaw (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R)
    (hfinite : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), R z ≠ ⊤) :
    HasLaw (nextMark L v R) FairMarks.fair (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  refine ⟨(nextMark_measurable L v R hR).aemeasurable,?_⟩
  simpa only [Measure.restrict_univ,measure_univ,one_smul] using
    restricted_map_eq L v R hR hfinite Set.univ MeasurableSet.univ

theorem nextMark_independent_stopped_history (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R)
    (hfinite : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), R z ≠ ⊤) :
    Indep ((inferInstance : MeasurableSpace Bool).comap (nextMark L v R)) hR.measurableSpace
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  rw [Indep_iff]
  intro A E hA hE
  rcases MeasurableSpace.measurableSet_comap.mp hA with ⟨B,hB,rfl⟩
  have h := congrArg (fun ν : Measure Bool => ν B) (restricted_map_eq L v R hR hfinite E hE)
  rw [Measure.map_apply (nextMark_measurable L v R hR) hB,
    Measure.restrict_apply (hB.preimage (nextMark_measurable L v R hR)),Measure.smul_apply] at h
  have hm : ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) ((nextMark L v R) ⁻¹' B) = FairMarks.fair B := by
    rw [← (nextMark_hasLaw L v R hR hfinite).map_eq,Measure.map_apply (nextMark_measurable L v R hR) hB]
  simpa only [hm,smul_eq_mul,mul_comm] using h

theorem stopped_waiting_mark_factor (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R)
    (hfinite : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), R z ≠ ⊤)
    (E : Set (Sample L)) (hE : MeasurableSet[hR.measurableSpace] E) (u : Real) (b : Bool) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      ((E ∩ {z | u < MarkedStoppedResidual.waiting L v R z}) ∩ {z | nextMark L v R z = b}) =
        ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
          (E ∩ {z | u < MarkedStoppedResidual.waiting L v R z}) * FairMarks.fair {b} := by
  rw [FairMarks.fair_singleton]
  apply invariant_factor L v R hR hfinite _ ((hR.measurableSpace_le E hE).inter
    (measurableSet_lt measurable_const (MarkedStoppedResidual.waiting_measurable L v R hR)))
  intro k z hc
  change (z ∈ E ∧ u < MarkedStoppedResidual.waiting L v R z) ↔
    (flipSample L (v,k) z ∈ E ∧ u < MarkedStoppedResidual.waiting L v R (flipSample L (v,k) z))
  rw [StoppedMarkSlices.candidate_waiting_flip L v R hR k z hc]
  exact and_congr_left (fun _ => StoppedMarkSlices.candidate_stopped_event_flip_iff L v R hR k z hc E hE)

theorem stopped_waiting_mark_survival (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) (hpos : ∀ z, 0 ≤ R z)
    (hfinite : ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), R z ≠ ⊤)
    (E : Set (Sample L)) (hE : MeasurableSet[hR.measurableSpace] E) (u : Real) (hu : 0 ≤ u) (b : Bool) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      ((E ∩ {z | u < MarkedStoppedResidual.waiting L v R z}) ∩ {z | nextMark L v R z = b}) =
        ENNReal.ofReal (Real.exp (-u)) * ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) E * FairMarks.fair {b} := by
  rw [stopped_waiting_mark_factor L v R hR hfinite E hE u b,
    MarkedStoppedResidual.waiting_jointSurvival L v R hR hpos hfinite u hu E hE]
theorem boundedExit_nextMark_hasLaw (L : Nat) (D I S : Finset InfiniteGridModel.Site) (T : NNReal) (v : Vertex L) :
    HasLaw (nextMark L v (ProtectedExitResidual.boundedExit L D I S T)) FairMarks.fair
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  nextMark_hasLaw L v (ProtectedExitResidual.boundedExit L D I S T)
    (ProtectedExitResidual.boundedExit_isStoppingTime L D I S T)
    (Filter.Eventually.of_forall (ProtectedExitResidual.boundedExit_ne_top L D I S T))

theorem boundedExit_nextMark_independent_stopped_history (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (T : NNReal) (v : Vertex L) :
    Indep ((inferInstance : MeasurableSpace Bool).comap (nextMark L v (ProtectedExitResidual.boundedExit L D I S T)))
      (ProtectedExitResidual.boundedExit_isStoppingTime L D I S T).measurableSpace
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  nextMark_independent_stopped_history L v (ProtectedExitResidual.boundedExit L D I S T)
    (ProtectedExitResidual.boundedExit_isStoppingTime L D I S T)
    (Filter.Eventually.of_forall (ProtectedExitResidual.boundedExit_ne_top L D I S T))

theorem boundedExit_waiting_mark_survival (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (T : NNReal) (v : Vertex L) (E : Set (Sample L))
    (hE : MeasurableSet[(ProtectedExitResidual.boundedExit_isStoppingTime L D I S T).measurableSpace] E)
    (u : Real) (hu : 0 ≤ u) (b : Bool) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      ((E ∩ {z | u < MarkedStoppedResidual.waiting L v (ProtectedExitResidual.boundedExit L D I S T) z}) ∩
        {z | nextMark L v (ProtectedExitResidual.boundedExit L D I S T) z = b}) =
      ENNReal.ofReal (Real.exp (-u)) * ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) E * FairMarks.fair {b} :=
  stopped_waiting_mark_survival L v (ProtectedExitResidual.boundedExit L D I S T)
    (ProtectedExitResidual.boundedExit_isStoppingTime L D I S T)
    (ProtectedExitResidual.boundedExit_nonnegative L D I S T)
    (Filter.Eventually.of_forall (ProtectedExitResidual.boundedExit_ne_top L D I S T)) E hE u hu b
end MathResearchAnalysis.StoppedFreshMark
