module
public import MathResearchAnalysis.ObservedFrozenProcess
set_option autoImplicit false
/-! Progressive measurability from finite observed history, on every sample. No completion or almost-sure path regularity is substituted for a product-measurability proof. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.ObservedProgressive
open MeasureTheory
open DropletClockLaw (Sample Event)
open InfiniteGridModel (Site)
open MarkedHistoryWords (censoredArrival ordered fiber)

abbrev pastProduct (L : Nat) (t : Real) : MeasurableSpace (Set.Iic t × Sample L) :=
  Subtype.instMeasurableSpace.prod (MarkedClockFiltration.history L t)

theorem variable_arrival_measurable (L : Nat) (t : Real) (e : Event L) :
    MeasurableSet[pastProduct L t]
      {p : Set.Iic t × Sample L | ClockEventWord.eventTime p.2.1 e ≤ (p.1 : Real)} := by
  let : MeasurableSpace (Sample L) := MarkedClockFiltration.history L t
  have heq : {p : Set.Iic t × Sample L | ClockEventWord.eventTime p.2.1 e ≤ (p.1 : Real)} =
      Prod.snd ⁻¹' {z : Sample L | ClockEventWord.eventTime z.1 e ≤ t} ∩
      {p : Set.Iic t × Sample L | censoredArrival L t e p.2 ≤ (p.1 : Real)} := by
    ext p
    simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_preimage]
    constructor
    · intro h
      exact ⟨h.trans p.1.prop,(min_le_left _ _).trans h⟩
    · rintro ⟨h,hc⟩
      rwa [MarkedHistoryWords.censoredArrival_eq_of_arrived L t e p.2 h] at hc
  rw [heq]
  exact ((MarkedClockFiltration.arrival_event_measurable L e (u := t) le_rfl).preimage measurable_snd).inter
    (measurableSet_le ((MarkedHistoryWords.censoredArrival_measurable L t e).comp measurable_snd)
      (measurable_subtype_coe.comp measurable_fst))

theorem variable_marked_arrival_measurable (L : Nat) (t : Real) (e : Event L) (b : Bool) :
    MeasurableSet[pastProduct L t] {p : Set.Iic t × Sample L |
      ClockEventWord.eventTime p.2.1 e ≤ (p.1 : Real) ∧ p.2.2 e = b} := by
  let : MeasurableSpace (Sample L) := MarkedClockFiltration.history L t
  have heq : {p : Set.Iic t × Sample L |
      ClockEventWord.eventTime p.2.1 e ≤ (p.1 : Real) ∧ p.2.2 e = b} =
      {p : Set.Iic t × Sample L | ClockEventWord.eventTime p.2.1 e ≤ (p.1 : Real)} ∩
      Prod.snd ⁻¹' {z : Sample L | ClockEventWord.eventTime z.1 e ≤ t ∧ z.2 e = b} := by
    ext p
    simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_preimage]
    exact ⟨fun h => ⟨h.1,h.1.trans p.1.prop,h.2⟩,fun h => ⟨h.1,h.2.2⟩⟩
  rw [heq]
  exact (variable_arrival_measurable L t e).inter
    ((MarkedClockFiltration.marked_event_measurable L e b (u := t) le_rfl).preimage measurable_snd)

theorem ordered_horizon_iff (L : Nat) {s t : Real} (hst : s ≤ t)
    (l : List (Event L)) (z : Sample L)
    (ha : ∀ e ∈ l, ClockEventWord.eventTime z.1 e ≤ s) : ordered L s l z ↔ ordered L t l z := by
  have he : ∀ e ∈ l, censoredArrival L s e z = censoredArrival L t e z := by
    intro e he
    rw [MarkedHistoryWords.censoredArrival_eq_of_arrived L s e z (ha e he),
      MarkedHistoryWords.censoredArrival_eq_of_arrived L t e z ((ha e he).trans hst)]
  constructor <;> intro ho <;> apply ho.imp_of_mem <;> intro a b ha hb hab
  · rwa [← he a ha,← he b hb]
  · rwa [he a ha,he b hb]

theorem variable_fiber_measurable (L : Nat) (t : Real) (l : List (Event L)) (ξ : Fin l.length → Bool) :
    MeasurableSet[pastProduct L t] {p : Set.Iic t × Sample L | fiber L (p.1 : Real) l ξ p.2} := by
  let : MeasurableSpace (Sample L) := MarkedClockFiltration.history L t
  have heq : {p : Set.Iic t × Sample L | fiber L (p.1 : Real) l ξ p.2} =
      (⋂ e : Event L, {p : Set.Iic t × Sample L | e ∈ l ↔ ClockEventWord.eventTime p.2.1 e ≤ (p.1 : Real)}) ∩
      (Prod.snd ⁻¹' {z | ordered L t l z} ∩ ⋂ i : Fin l.length,
        {p : Set.Iic t × Sample L | ClockEventWord.eventTime p.2.1 l[i] ≤ (p.1 : Real) ∧ p.2.2 l[i] = ξ i}) := by
    ext p
    simp only [Set.mem_inter_iff,Set.mem_iInter,Set.mem_preimage,Set.mem_ofPred_eq,fiber]
    constructor
    · rintro ⟨hc,ho,hm⟩
      exact ⟨hc,(ordered_horizon_iff L p.1.prop l p.2 (fun e he => (hc e).mp he)).mp ho,hm⟩
    · rintro ⟨hc,ho,hm⟩
      exact ⟨hc,(ordered_horizon_iff L p.1.prop l p.2 (fun e he => (hc e).mp he)).mpr ho,hm⟩
  rw [heq]
  exact (MeasurableSet.iInter fun e => (MeasurableSet.const (e ∈ l)).iff
    (variable_arrival_measurable L t e)).inter
    (((MarkedHistoryWords.ordered_measurable L t l).preimage measurable_snd).inter
      (MeasurableSet.iInter fun i => variable_marked_arrival_measurable L t l[i] (ξ i)))

theorem variable_graph_measurable (L : Nat) (D I S : Finset Site) (t : Real) (T : Finset Site) :
    MeasurableSet[pastProduct L t]
      {p : Set.Iic t × Sample L | p.2 ∈ ObservedFrozenProcess.graph L D I S (p.1 : Real) T} := by
  let : MeasurableSpace (Sample L) := MarkedClockFiltration.history L t
  have heq : {p : Set.Iic t × Sample L | p.2 ∈ ObservedFrozenProcess.graph L D I S (p.1 : Real) T} =
      ⋃ l : List (Event L), ⋃ ξ : Fin l.length → Bool,
      {p : Set.Iic t × Sample L | fiber L (p.1 : Real) l ξ p.2} ∩ {p : Set.Iic t × Sample L |
        DropletStoppedWord.stoppedWord D I S (MarkedHistoryWords.indexedEvents L l ξ) = T} := by
    ext p
    simp only [ObservedFrozenProcess.graph,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff]
  rw [heq]
  exact MeasurableSet.iUnion fun l => MeasurableSet.iUnion fun ξ =>
    (variable_fiber_measurable L t l ξ).inter (MeasurableSet.const _)

theorem state_isProgressive (L : Nat) (D I S : Finset Site) :
    letI : MeasurableSpace (Finset Site) := ObservedFrozenProcess.stateSpace
    IsProgressive (MarkedClockFiltration.history L) (ObservedFrozenProcess.state L D I S) := by
  let : MeasurableSpace (Finset Site) := ObservedFrozenProcess.stateSpace
  intro t
  let : MeasurableSpace (Sample L) := MarkedClockFiltration.history L t
  apply measurable_to_countable'
  intro T
  have heq : (fun p : Set.Iic t × Sample L => ObservedFrozenProcess.state L D I S (p.1 : Real) p.2) ⁻¹' {T} =
      {p : Set.Iic t × Sample L | p.2 ∈ ObservedFrozenProcess.graph L D I S (p.1 : Real) T} ∪
      (⋃ U : Finset Site, {p : Set.Iic t × Sample L |
        p.2 ∈ ObservedFrozenProcess.graph L D I S (p.1 : Real) U})ᶜ ∩ {p : Set.Iic t × Sample L | S = T} := by
    ext p
    simp only [Set.mem_preimage,Set.mem_singleton_iff,ObservedFrozenProcess.state_eq_iff,
      Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_iUnion,Set.mem_ofPred_eq]
  rw [heq]
  exact (variable_graph_measurable L D I S t T).union
    ((MeasurableSet.iUnion (fun U => variable_graph_measurable L D I S t U)).compl.inter (MeasurableSet.const _))

theorem state_isProgressive_nn (L : Nat) (D I S : Finset Site) :
    letI : MeasurableSpace (Finset Site) := ObservedFrozenProcess.stateSpace
    IsProgressive (RationalProtectedExit.nnHistory L)
      (fun t : NNReal => ObservedFrozenProcess.state L D I S (t : Real)) := by
  let : MeasurableSpace (Finset Site) := ObservedFrozenProcess.stateSpace
  intro t
  let : MeasurableSpace (Sample L) := MarkedClockFiltration.history L (t : Real)
  have hm : Measurable (fun p : Set.Iic t × Sample L =>
      ((⟨((p.1 : NNReal) : Real),by exact_mod_cast p.1.prop⟩ : Set.Iic (t : Real)),p.2)) := by
    exact (((measurable_coe_nnreal_real.comp measurable_subtype_coe).comp measurable_fst).subtype_mk).prodMk measurable_snd
  exact (state_isProgressive L D I S (t : Real)).comp hm

theorem area_isStronglyProgressive (L : Nat) (D I S : Finset Site) :
    IsStronglyProgressive (RationalProtectedExit.nnHistory L)
      (fun t : NNReal => fun z => ((S \ ObservedFrozenProcess.state L D I S (t : Real) z).card : Real)) := by
  let : MeasurableSpace (Finset Site) := ObservedFrozenProcess.stateSpace
  have hf : Measurable (fun T : Finset Site => ((S \ T).card : Real)) := fun _ _ => trivial
  intro t
  exact (hf.comp (state_isProgressive_nn L D I S t)).stronglyMeasurable
theorem area_isStronglyProgressive_right (L : Nat) (D I S : Finset Site) :
    IsStronglyProgressive (RationalProtectedExit.rightHistory L)
      (fun t : NNReal => fun z => ((S \ ObservedFrozenProcess.state L D I S (t : Real) z).card : Real)) := by
  intro t
  apply (area_isStronglyProgressive L D I S t).mono
  exact sup_le_sup le_rfl (MeasurableSpace.comap_mono ((RationalProtectedExit.nnHistory L).le_rightCont t))

def exitArea (L : Nat) (D I S : Finset Site) : Sample L → Real :=
  stoppedValue (fun t : NNReal => fun z => ((S \ ObservedFrozenProcess.state L D I S (t : Real) z).card : Real))
    (RationalProtectedExit.rationalExit L D I S)

theorem exitArea_measurable_at_exit (L : Nat) (D I S : Finset Site) :
    @Measurable (Sample L) Real (RationalProtectedExit.rationalExit_isStoppingTime L D I S).measurableSpace
      inferInstance (exitArea L D I S) :=
  measurable_stoppedValue (area_isStronglyProgressive_right L D I S)
    (RationalProtectedExit.rationalExit_isStoppingTime L D I S)

theorem exitArea_eq_of_finite (L : Nat) (D I S : Finset Site) (z : Sample L)
    (hfin : RationalProtectedExit.rationalExit L D I S z ≠ ⊤) :
    exitArea L D I S z = ((S \ ObservedFrozenProcess.state L D I S
      (RationalProtectedExit.rationalExit L D I S z).toReal z).card : Real) := by
  have he : (RationalProtectedExit.rationalExit L D I S z).untopA =
      (RationalProtectedExit.rationalExit L D I S z).toNNReal := by
    generalize hr : RationalProtectedExit.rationalExit L D I S z = r at *
    cases r with
    | top => exact False.elim (hfin rfl)
    | coe r =>
      change (WithTop.some r).untopA = r
      exact WithTop.untopA_eq_untop WithTop.coe_ne_top
  simp only [exitArea,stoppedValue,he,ENNReal.toReal]

theorem exitArea_nonnegative (L : Nat) (D I S : Finset Site) (z : Sample L) :
    0 ≤ exitArea L D I S z := by
  exact Nat.cast_nonneg _

theorem exitArea_le_initial_card (L : Nat) (D I S : Finset Site) (z : Sample L) :
    exitArea L D I S z ≤ (S.card : Real) := by
  change ((S \ ObservedFrozenProcess.state L D I S
    ((RationalProtectedExit.rationalExit L D I S z).untopA : Real) z).card : Real) ≤ (S.card : Real)
  exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := S))

theorem actual_exitArea_quadratic_on_finite_exit (L : Nat) (hL : 40 ≤ L) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hfin : RationalProtectedExit.rationalExit L (ClippedDiamondGeometry.clippedDomain L)
      (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L) z ≠ ⊤) :
    (L : Real)^2/1600 ≤ exitArea L (ClippedDiamondGeometry.clippedDomain L)
      (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L) z := by
  rw [exitArea_eq_of_finite L _ _ _ z hfin]
  apply ObservedFrozenProcess.quadratic_area_after_exit L hL z hg _ ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_toReal hfin]
end MathResearchAnalysis.ObservedProgressive
