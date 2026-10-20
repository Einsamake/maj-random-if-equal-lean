module
public import MathResearchAnalysis.UnrevealedMarkInvariance
set_option autoImplicit false
/-! Fair slices of the next actual site-ring identity after a marked-history stopping time. Flip symmetry preserves the selected identity, the stopped past and the actual residual wait. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.StoppedMarkSlices
open MeasureTheory
open DropletClockLaw (Sample Event Vertex)
open UnrevealedMarkInvariance (flipSample)

theorem flip_slice_measure (L : Nat) (e : Event L) (A : Set (Sample L)) (hA : MeasurableSet A)
    (hinv : ∀ z, z ∈ A ↔ flipSample L e z ∈ A) (b : Bool) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) (A ∩ {z | z.2 e = !b}) =
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) (A ∩ {z | z.2 e = b}) := by
  have hm : MeasurableSet (A ∩ {z : Sample L | z.2 e = b}) :=
    hA.inter (measurableSet_eq_fun (MarkedClockFiltration.mark_measurable L e) measurable_const)
  have heq : flipSample L e ⁻¹' (A ∩ {z : Sample L | z.2 e = b}) = A ∩ {z : Sample L | z.2 e = !b} := by
    ext z
    change (flipSample L e z ∈ A ∧ (flipSample L e z).2 e = b) ↔ (z ∈ A ∧ z.2 e = !b)
    rw [← hinv z]
    apply and_congr_right
    intro _
    simp only [UnrevealedMarkInvariance.flipSample,UnrevealedMarkInvariance.flipField,Function.update_self]
    cases b <;> cases z.2 e <;> decide
  rw [← heq,← Measure.map_apply (UnrevealedMarkInvariance.flipSample_measurable L e) hm,
    UnrevealedMarkInvariance.flipSample_map L e]

theorem fair_slice_factor (L : Nat) (e : Event L) (A : Set (Sample L)) (hA : MeasurableSet A)
    (hinv : ∀ z, z ∈ A ↔ flipSample L e z ∈ A) (b : Bool) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) (A ∩ {z | z.2 e = b}) =
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) A * (2 : ENNReal)⁻¹ := by
  let μ := ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
  have hm : MeasurableSet (A ∩ {z : Sample L | z.2 e = !b}) :=
    hA.inter (measurableSet_eq_fun (MarkedClockFiltration.mark_measurable L e) measurable_const)
  have hd : Disjoint (A ∩ {z : Sample L | z.2 e = b}) (A ∩ {z : Sample L | z.2 e = !b}) := by
    apply Set.disjoint_left.mpr
    intro z hz hw
    have he : b = !b := hz.2.symm.trans hw.2
    cases b <;> cases he
  have hu : (A ∩ {z : Sample L | z.2 e = b}) ∪ (A ∩ {z : Sample L | z.2 e = !b}) = A := by
    ext z
    simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_ofPred_eq]
    cases b <;> cases z.2 e <;> simp
  have hs : μ (A ∩ {z | z.2 e = b}) + μ (A ∩ {z | z.2 e = b}) = μ A := by
    have h := measure_union hd hm (μ := μ)
    rw [hu,flip_slice_measure L e A hA hinv b] at h
    exact h.symm
  calc
    _ = (2 : ENNReal)⁻¹ * (μ (A ∩ {z | z.2 e = b}) + μ (A ∩ {z | z.2 e = b})) := by
      rw [← two_mul,ENNReal.inv_mul_cancel_left (by norm_num) (by norm_num)]
    _ = _ := by rw [hs,mul_comm]

def candidate (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real) (k : Nat) (z : Sample L) : Prop :=
  R z < (ClockEventWord.eventTime z.1 (v,k) : WithTop Real) ∧
    ∀ j : Fin k, (ClockEventWord.eventTime z.1 (v,j.val) : WithTop Real) ≤ R z

theorem candidate_measurable (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) (k : Nat) :
    MeasurableSet {z | candidate L v R k z} := by
  have hp : MeasurableSet {z : Sample L | ∀ j : Fin k,
      (ClockEventWord.eventTime z.1 (v,j.val) : WithTop Real) ≤ R z} := by
    convert (MeasurableSet.iInter fun j : Fin k => measurableSet_le
      (MarkedClockFiltration.arrival_measurable L (v,j.val)).withTop_coe hR.measurable') using 1
    ext z
    simp only [Set.mem_iInter,Set.mem_ofPred_eq]
  exact (measurableSet_lt hR.measurable' (MarkedClockFiltration.arrival_measurable L (v,k)).withTop_coe).inter hp

theorem candidate_unique (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real) (z : Sample L)
    (k j : Nat) (hk : candidate L v R k z) (hj : candidate L v R j z) : k = j := by
  apply Nat.le_antisymm
  · by_contra h
    exact not_le_of_gt hj.1 (hk.2 ⟨j,lt_of_not_ge h⟩)
  · by_contra h
    exact not_le_of_gt hk.1 (hj.2 ⟨k,lt_of_not_ge h⟩)

theorem candidate_flip_stoppingTime (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) (k : Nat) (z : Sample L)
    (hc : candidate L v R k z) : R (flipSample L (v,k) z) = R z := by
  cases hz : R z using WithTop.recTopCoe with
  | top => exact False.elim (not_top_lt (hz ▸ hc.1))
  | coe r =>
    have h := UnrevealedMarkInvariance.stoppingTime_invariant L (v,k) (!(z.2 (v,k))) z R hR r hz
      (WithTop.coe_lt_coe.mp (by simpa only [hz] using hc.1))
    exact h.trans hz

theorem candidate_flip (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) (k : Nat) (z : Sample L)
    (hc : candidate L v R k z) : candidate L v R k (flipSample L (v,k) z) := by
  have he := candidate_flip_stoppingTime L v R hR k z hc
  change R (flipSample L (v,k) z) < (ClockEventWord.eventTime z.1 (v,k) : WithTop Real) ∧
    ∀ j : Fin k, (ClockEventWord.eventTime z.1 (v,j.val) : WithTop Real) ≤ R (flipSample L (v,k) z)
  rwa [he]

theorem candidate_flip_iff (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) (k : Nat) (z : Sample L) :
    candidate L v R k z ↔ candidate L v R k (flipSample L (v,k) z) := by
  constructor
  · exact candidate_flip L v R hR k z
  · intro hc
    simpa only [UnrevealedMarkInvariance.flipSample_involutive L (v,k) z] using
      candidate_flip L v R hR k (flipSample L (v,k) z) hc

theorem candidate_stopped_event_flip_iff (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) (k : Nat) (z : Sample L)
    (hc : candidate L v R k z) (E : Set (Sample L)) (hE : MeasurableSet[hR.measurableSpace] E) :
    z ∈ E ↔ flipSample L (v,k) z ∈ E := by
  cases hz : R z using WithTop.recTopCoe with
  | top => exact False.elim (not_top_lt (hz ▸ hc.1))
  | coe r =>
    apply UnrevealedMarkInvariance.stopped_history_invariant L (v,k) (!(z.2 (v,k))) z R hR r hz ?_ E hE
    exact WithTop.coe_lt_coe.mp (by simpa only [hz] using hc.1)

theorem candidate_waiting_flip (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) (k : Nat) (z : Sample L)
    (hc : candidate L v R k z) :
    MarkedStoppedResidual.waiting L v R (flipSample L (v,k) z) = MarkedStoppedResidual.waiting L v R z := by
  classical
  have he := candidate_flip_stoppingTime L v R hR k z hc
  simp only [MarkedStoppedResidual.waiting,ClockWaitingLimit.waiting,ExtendedNextRing.after]
  change max ((if hex : ∃ j, R (flipSample L (v,k) z) <
      (ArrivalFiltration.chronologicalArrival v j z.1 : WithTop Real) then
      (ArrivalFiltration.chronologicalArrival v (Nat.find hex) z.1 : WithTop Real) else ⊤).untopD 0 -
      (R (flipSample L (v,k) z)).untopD 0) 0 = _
  rw [he]

theorem candidate_slice_factor (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) (k : Nat)
    (G : Set (Sample L)) (hG : MeasurableSet G)
    (hinv : ∀ z, candidate L v R k z → (z ∈ G ↔ flipSample L (v,k) z ∈ G)) (b : Bool) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) ({z | candidate L v R k z} ∩ G ∩ {z | z.2 (v,k) = b}) =
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) ({z | candidate L v R k z} ∩ G) * (2 : ENNReal)⁻¹ := by
  apply fair_slice_factor L (v,k) _ ((candidate_measurable L v R hR k).inter hG)
  intro z
  change (candidate L v R k z ∧ z ∈ G) ↔
    (candidate L v R k (flipSample L (v,k) z) ∧ flipSample L (v,k) z ∈ G)
  constructor
  · rintro ⟨hc,hg⟩
    exact ⟨(candidate_flip_iff L v R hR k z).mp hc,(hinv z hc).mp hg⟩
  · rintro ⟨hc,hg⟩
    have hc' := (candidate_flip_iff L v R hR k z).mpr hc
    exact ⟨hc',(hinv z hc').mpr hg⟩

theorem stopped_history_slice_factor (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) (k : Nat)
    (E : Set (Sample L)) (hE : MeasurableSet[hR.measurableSpace] E) (b : Bool) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) ({z | candidate L v R k z} ∩ E ∩ {z | z.2 (v,k) = b}) =
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) ({z | candidate L v R k z} ∩ E) * (2 : ENNReal)⁻¹ :=
  candidate_slice_factor L v R hR k E (hR.measurableSpace_le E hE)
    (fun z hc => candidate_stopped_event_flip_iff L v R hR k z hc E hE) b

theorem stopped_waiting_slice_factor (L : Nat) (v : Vertex L) (R : Sample L → WithTop Real)
    (hR : IsStoppingTime (MarkedClockFiltration.history L) R) (k : Nat)
    (E : Set (Sample L)) (hE : MeasurableSet[hR.measurableSpace] E) (u : Real) (b : Bool) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      ({z | candidate L v R k z} ∩ (E ∩ {z | u < MarkedStoppedResidual.waiting L v R z}) ∩ {z | z.2 (v,k) = b}) =
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
        ({z | candidate L v R k z} ∩ (E ∩ {z | u < MarkedStoppedResidual.waiting L v R z})) * (2 : ENNReal)⁻¹ := by
  apply candidate_slice_factor L v R hR k _
    ((hR.measurableSpace_le E hE).inter (measurableSet_lt measurable_const (MarkedStoppedResidual.waiting_measurable L v R hR)))
  intro z hc
  change (z ∈ E ∧ u < MarkedStoppedResidual.waiting L v R z) ↔
    (flipSample L (v,k) z ∈ E ∧ u < MarkedStoppedResidual.waiting L v R (flipSample L (v,k) z))
  rw [candidate_waiting_flip L v R hR k z hc]
  exact and_congr_left (fun _ => candidate_stopped_event_flip_iff L v R hR k z hc E hE)
end MathResearchAnalysis.StoppedMarkSlices
