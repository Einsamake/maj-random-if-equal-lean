module
public import MathResearchAnalysis.ObservedProgressive
set_option autoImplicit false
/-! Complete local history, chronological prefix consistency and right gaps on every finite-site clock sample, including paths outside the global clock-Good event. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.LocalObservedHistory
open MeasureTheory
open DropletClockLaw (Sample Event Vertex)
open MarkedHistoryWords (fiber ordered indexedEvents)
open InfiniteGridModel (Site)

def valid (L : Nat) (t : Real) : Set (Sample L) := {z | ∃ l : List (Event L), ∃ ξ : Fin l.length → Bool, fiber L t l ξ z}

theorem valid_measurable (L : Nat) (t : Real) : MeasurableSet[MarkedClockFiltration.history L t] (valid L t) := by
  let : MeasurableSpace (Sample L) := MarkedClockFiltration.history L t
  have heq : valid L t = ⋃ l : List (Event L), ⋃ ξ : Fin l.length → Bool, {z | fiber L t l ξ z} := by
    ext z
    simp only [valid,Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [heq]
  exact MeasurableSet.iUnion fun l => MeasurableSet.iUnion fun ξ => MarkedHistoryWords.fiber_measurable L t l ξ

theorem past_fiber (L : Nat) (z : Sample L) {s t : Real} (hst : s ≤ t)
    (l : List (Event L)) (ξ : Fin l.length → Bool) (hf : fiber L t l ξ z) :
    fiber L s (l.filter (fun e => decide (ClockEventWord.eventTime z.1 e ≤ s)))
      (fun i => z.2 (l.filter (fun e => decide (ClockEventWord.eventTime z.1 e ≤ s)))[i]) z := by
  classical
  let k := l.filter (fun e => decide (ClockEventWord.eventTime z.1 e ≤ s))
  have hc : ∀ e : Event L, e ∈ k ↔ ClockEventWord.eventTime z.1 e ≤ s := by
    intro e
    simp only [k,List.mem_filter,decide_eq_true_eq]
    exact ⟨fun h => h.2,fun h => ⟨(hf.1 e).mpr (h.trans hst),h⟩⟩
  have ho : ordered L t k z := hf.2.1.sublist List.filter_sublist
  exact ⟨hc,(ObservedProgressive.ordered_horizon_iff L hst k z (fun e he => (hc e).mp he)).mpr ho,
    fun i => ⟨(hc k[i]).mp (List.getElem_mem _),rfl⟩⟩

theorem valid_backward (L : Nat) (z : Sample L) {s t : Real} (hst : s ≤ t)
    (ht : z ∈ valid L t) : z ∈ valid L s := by
  rcases ht with ⟨l,ξ,hf⟩
  exact ⟨_,_,past_fiber L z hst l ξ hf⟩

theorem fiber_events_prefix (L : Nat) (z : Sample L) {s t : Real} (hst : s ≤ t)
    (k l : List (Event L)) (η : Fin k.length → Bool) (ξ : Fin l.length → Bool)
    (hk : fiber L s k η z) (hl : fiber L t l ξ z) :
    (indexedEvents L k η).IsPrefix (indexedEvents L l ξ) := by
  classical
  let p := l.filter (fun e => decide (ClockEventWord.eventTime z.1 e ≤ s))
  let θ : Fin p.length → Bool := fun i => z.2 p[i]
  have hp : fiber L s p θ z := past_fiber L z hst l ξ hl
  have heq := ObservedFrozenProcess.fiber_events_eq L s z k p η θ hk hp
  rw [heq,MarkedHistoryWords.indexedEvents_eq_map L p θ z (fun _ => rfl),
    MarkedHistoryWords.indexedEvents_eq_map L l ξ z (fun i => (hl.2.2 i).2)]
  apply List.IsPrefix.map
  apply ClockWordConsistency.threshold_filter_prefix
  apply hl.2.1.imp_of_mem
  intro a b ha hb hab
  rwa [MarkedHistoryWords.censoredArrival_eq_of_arrived L t a z ((hl.1 a).mp ha),
    MarkedHistoryWords.censoredArrival_eq_of_arrived L t b z ((hl.1 b).mp hb)] at hab

theorem loss_persistent_of_valid (L : Nat) (D I S : Finset Site) (z : Sample L)
    {s t : Real} (hst : s ≤ t) (ht : z ∈ valid L t)
    (hs : z ∈ MarkedHistoryWords.observedLoss L D I S s) :
    z ∈ MarkedHistoryWords.observedLoss L D I S t := by
  rcases hs with ⟨k,η,hk,hm⟩
  rcases ht with ⟨l,ξ,hl⟩
  obtain ⟨u,hu⟩ := fiber_events_prefix L z hst k l η ξ hk hl
  refine ⟨l,ξ,hl,?_⟩
  rw [← hu,DropletStoppedWord.stoppedWord_append,DropletStoppedWord.stoppedWord_of_missing hm]
  exact hm

theorem next_event_gap (L : Nat) (z : Sample L) (t : Real) :
    ∃ b : Real, t < b ∧ ∀ e : Event L, t < ClockEventWord.eventTime z.1 e → b ≤ ClockEventWord.eventTime z.1 e := by
  classical
  let next : Vertex L → Real := fun v => if h : ∃ k : Nat, t < ArrivalFiltration.chronologicalArrival v k z.1
    then ArrivalFiltration.chronologicalArrival v (Nat.find h) z.1 else t+1
  have hn : ∀ v : Vertex L, t < next v := by
    intro v
    dsimp only [next]
    split_ifs with h
    · exact Nat.find_spec h
    · linarith
  let values := Finset.univ.image next
  have hne : values.Nonempty := Finset.univ_nonempty.image next
  let b := values.min' hne
  have hb : t < b := by
    obtain ⟨v,_,hv⟩ := Finset.mem_image.mp (Finset.min'_mem values hne)
    change t < values.min' hne
    rw [← hv]
    exact hn v
  refine ⟨b,hb,?_⟩
  rintro ⟨v,k⟩ hk
  have hex : ∃ j : Nat, t < ArrivalFiltration.chronologicalArrival v j z.1 := ⟨k,hk⟩
  have hnext : next v ≤ ClockEventWord.eventTime z.1 (v,k) := by
    dsimp only [next]
    rw [dite_eq_left hex]
    exact ArrivalFiltration.chronologicalArrival_monotone v z.1 (Nat.find_min' hex hk)
  exact (Finset.min'_le values (next v) (Finset.mem_image.mpr ⟨v,Finset.mem_univ v,rfl⟩)).trans hnext

theorem same_past_on_gap (L : Nat) (z : Sample L) (t : Real) :
    ∃ b : Real, t < b ∧ ∀ s : Real, t ≤ s → s < b → ∀ e : Event L,
      (ClockEventWord.eventTime z.1 e ≤ s ↔ ClockEventWord.eventTime z.1 e ≤ t) := by
  obtain ⟨b,htb,hb⟩ := next_event_gap L z t
  refine ⟨b,htb,?_⟩
  intro s hts hsb e
  constructor
  · intro hs
    by_contra ht
    exact (not_le_of_gt hsb) ((hb e (lt_of_not_ge ht)).trans hs)
  · exact fun ht => ht.trans hts

theorem fiber_iff_same_past (L : Nat) (z : Sample L) {s t : Real} (hst : s ≤ t)
    (he : ∀ e : Event L, ClockEventWord.eventTime z.1 e ≤ t ↔ ClockEventWord.eventTime z.1 e ≤ s)
    (l : List (Event L)) (ξ : Fin l.length → Bool) : fiber L t l ξ z ↔ fiber L s l ξ z := by
  constructor
  · rintro ⟨hc,ho,hm⟩
    have hcs : ∀ e, e ∈ l ↔ ClockEventWord.eventTime z.1 e ≤ s := fun e => (hc e).trans (he e)
    exact ⟨hcs,(ObservedProgressive.ordered_horizon_iff L hst l z (fun e he => (hcs e).mp he)).mpr ho,
      fun i => ⟨(he l[i]).mp (hm i).1,(hm i).2⟩⟩
  · rintro ⟨hc,ho,hm⟩
    exact ⟨(fun e => (hc e).trans (he e).symm),
      (ObservedProgressive.ordered_horizon_iff L hst l z (fun e he => (hc e).mp he)).mp ho,
      fun i => ⟨(he l[i]).mpr (hm i).1,(hm i).2⟩⟩

theorem valid_iff_same_past (L : Nat) (z : Sample L) {s t : Real} (hst : s ≤ t)
    (he : ∀ e : Event L, ClockEventWord.eventTime z.1 e ≤ t ↔ ClockEventWord.eventTime z.1 e ≤ s) :
    z ∈ valid L t ↔ z ∈ valid L s := by
  simp only [valid,Set.mem_ofPred_eq]
  exact exists_congr fun l => exists_congr fun ξ => fiber_iff_same_past L z hst he l ξ

theorem loss_iff_same_past (L : Nat) (D I S : Finset Site) (z : Sample L) {s t : Real} (hst : s ≤ t)
    (he : ∀ e : Event L, ClockEventWord.eventTime z.1 e ≤ t ↔ ClockEventWord.eventTime z.1 e ≤ s) :
    z ∈ MarkedHistoryWords.observedLoss L D I S t ↔ z ∈ MarkedHistoryWords.observedLoss L D I S s := by
  simp only [MarkedHistoryWords.observedLoss,Set.mem_ofPred_eq]
  exact exists_congr fun l => exists_congr fun ξ => and_congr_left (fun _ => fiber_iff_same_past L z hst he l ξ)

theorem valid_of_good (L : Nat) (z : Sample L) (t : Real) (hg : ClockEventWord.Good z.1 t) : z ∈ valid L t := by
  obtain ⟨l,ξ,hf,_⟩ := ObservedFrozenProcess.graph_stateAt L ∅ ∅ ∅ t z hg
  exact ⟨l,ξ,hf⟩
/- The invalid-history branch is an independent absorbing cemetery flag. It is
   not identified with missing protection when I is empty. -/
def absorbingLoss (L : Nat) (D I S : Finset Site) (t : Real) : Set (Sample L) :=
  (valid L t)ᶜ ∪ MarkedHistoryWords.observedLoss L D I S t

theorem absorbingLoss_measurable (L : Nat) (D I S : Finset Site) (t : Real) :
    MeasurableSet[MarkedClockFiltration.history L t] (absorbingLoss L D I S t) :=
  (valid_measurable L t).compl.union (MarkedHistoryWords.observedLoss_measurable L D I S t)

theorem absorbingLoss_mono (L : Nat) (D I S : Finset Site) (z : Sample L)
    {s t : Real} (hst : s ≤ t) (hs : z ∈ absorbingLoss L D I S s) :
    z ∈ absorbingLoss L D I S t := by
  rcases hs with hs | hs
  · exact Or.inl (fun ht => hs (valid_backward L z hst ht))
  · by_cases ht : z ∈ valid L t
    · exact Or.inr (loss_persistent_of_valid L D I S z hst ht hs)
    · exact Or.inl ht

theorem absorbingLoss_iff_same_past (L : Nat) (D I S : Finset Site) (z : Sample L)
    {s t : Real} (hst : s ≤ t)
    (he : ∀ e : Event L, ClockEventWord.eventTime z.1 e ≤ t ↔ ClockEventWord.eventTime z.1 e ≤ s) :
    z ∈ absorbingLoss L D I S t ↔ z ∈ absorbingLoss L D I S s :=
  or_congr (not_congr (valid_iff_same_past L z hst he)) (loss_iff_same_past L D I S z hst he)

def exit (L : Nat) (D I S : Finset Site) (z : Sample L) : ENNReal :=
  FrozenPhysicalExit.firstLossTime (fun t => z ∈ absorbingLoss L D I S t)

theorem exit_le_iff (L : Nat) (D I S : Finset Site) (z : Sample L) {t : Real} (ht : 0 ≤ t) :
    exit L D I S z ≤ ENNReal.ofReal t ↔ z ∈ absorbingLoss L D I S t := by
  apply FrozenPhysicalExit.firstLossTime_le_iff _ ?_ ?_ ht
  · intro s u _ hsu hs
    exact absorbingLoss_mono L D I S z hsu hs
  · intro u _ hnot
    obtain ⟨b,hub,hb⟩ := same_past_on_gap L z u
    refine ⟨b,hub,?_⟩
    intro v huv hvb hv
    exact hnot ((absorbingLoss_iff_same_past L D I S z huv (hb v huv hvb)).mp hv)

theorem exit_isStoppingTime (L : Nat) (D I S : Finset Site) :
    IsStoppingTime (RationalProtectedExit.nnHistory L) (exit L D I S) := by
  intro t
  change MeasurableSet[MarkedClockFiltration.history L (t : Real)] {z | exit L D I S z ≤ (t : ENNReal)}
  have heq : {z : Sample L | exit L D I S z ≤ (t : ENNReal)} = absorbingLoss L D I S (t : Real) := by
    ext z
    simpa only [ENNReal.ofReal_coe_nnreal,Set.mem_ofPred_eq] using exit_le_iff L D I S z (NNReal.coe_nonneg t)
  rw [heq]
  exact absorbingLoss_measurable L D I S (t : Real)

theorem exit_measurable (L : Nat) (D I S : Finset Site) : Measurable (exit L D I S) :=
  (exit_isStoppingTime L D I S).measurable'

theorem exit_eq_physicalExit (L : Nat) (D I S : Finset Site) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t) : exit L D I S z = FrozenPhysicalExit.physicalExit L D I S z := by
  have he : (fun t => z ∈ absorbingLoss L D I S t) =
      (fun t => ¬ I ⊆ DropletStoppedClockLaw.stateAt L D I S t z) := by
    funext t
    apply propext
    have hv := valid_of_good L z t (hg t)
    change (z ∉ valid L t ∨ z ∈ MarkedHistoryWords.observedLoss L D I S t) ↔ _
    simp only [hv,not_true_eq_false,false_or]
    exact MarkedHistoryWords.observedLoss_iff L D I S t z (hg t)
  change FrozenPhysicalExit.firstLossTime _ = FrozenPhysicalExit.firstLossTime _
  rw [he]

theorem exit_ae_eq_physicalExit (L : Nat) (D I S : Finset Site) :
    exit L D I S =ᵐ[ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)]
      FrozenPhysicalExit.physicalExit L D I S := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L] with z hz
  exact exit_eq_physicalExit L D I S z hz

theorem exit_law_equal (L : Nat) (D I S : Finset Site) :
    Measure.map (exit L D I S) (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      Measure.map (FrozenPhysicalExit.physicalExit L D I S) (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  Measure.map_congr (exit_ae_eq_physicalExit L D I S)

theorem exit_extended_mean_equal (L : Nat) (D I S : Finset Site) :
    ∫⁻ z, exit L D I S z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) =
      ∫⁻ z, FrozenPhysicalExit.physicalExit L D I S z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) :=
  lintegral_congr_ae (exit_ae_eq_physicalExit L D I S)
end MathResearchAnalysis.LocalObservedHistory
