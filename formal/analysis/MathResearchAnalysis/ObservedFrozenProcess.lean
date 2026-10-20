module
public import MathResearchAnalysis.RationalProtectedExit
set_option autoImplicit false
/-! A genuinely past-measurable version of the complete frozen state. The representative is defined on every sample and agrees with the original clock state at all real times on one common full-measure set. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.ObservedFrozenProcess
open MeasureTheory
open DropletClockLaw (Sample Event)
open InfiniteGridModel (Site)
open MarkedHistoryWords (fiber indexedEvents)

abbrev stateSpace : MeasurableSpace (Finset Site) := ⊤

theorem fiber_lists_eq (L : Nat) (t : Real) (z : Sample L)
    (l k : List (Event L)) (ξ : Fin l.length → Bool) (η : Fin k.length → Bool)
    (hl : fiber L t l ξ z) (hk : fiber L t k η z) : l = k := by
  have hln : l.Nodup := hl.2.1.imp (fun {a b} hlt heq => by subst b; exact lt_irrefl _ hlt)
  have hkn : k.Nodup := hk.2.1.imp (fun {a b} hlt heq => by subst b; exact lt_irrefl _ hlt)
  have hp : l.Perm k := (List.perm_ext_iff_of_nodup hln hkn).mpr
    (fun e => (hl.1 e).trans (hk.1 e).symm)
  exact List.Perm.eq_of_pairwise
    (fun a b _ _ hab hba => False.elim ((not_lt_of_gt hab) hba)) hl.2.1 hk.2.1 hp

theorem fiber_events_eq (L : Nat) (t : Real) (z : Sample L)
    (l k : List (Event L)) (ξ : Fin l.length → Bool) (η : Fin k.length → Bool)
    (hl : fiber L t l ξ z) (hk : fiber L t k η z) : indexedEvents L l ξ = indexedEvents L k η := by
  rw [MarkedHistoryWords.indexedEvents_eq_map L l ξ z (fun i => (hl.2.2 i).2),
    MarkedHistoryWords.indexedEvents_eq_map L k η z (fun i => (hk.2.2 i).2),
    fiber_lists_eq L t z l k ξ η hl hk]

def graph (L : Nat) (D I S : Finset Site) (t : Real) (T : Finset Site) : Set (Sample L) :=
  {z | ∃ l : List (Event L), ∃ ξ : Fin l.length → Bool, fiber L t l ξ z ∧
    DropletStoppedWord.stoppedWord D I S (indexedEvents L l ξ) = T}

theorem graph_measurable (L : Nat) (D I S : Finset Site) (t : Real) (T : Finset Site) :
    MeasurableSet[MarkedClockFiltration.history L t] (graph L D I S t T) := by
  let : MeasurableSpace (Sample L) := MarkedClockFiltration.history L t
  have heq : graph L D I S t T = ⋃ l : List (Event L), ⋃ ξ : Fin l.length → Bool,
      {z | fiber L t l ξ z} ∩
      {z : Sample L | DropletStoppedWord.stoppedWord D I S (indexedEvents L l ξ) = T} := by
    ext z
    simp only [graph,Set.mem_iUnion,Set.mem_inter_iff,Set.mem_ofPred_eq]
  rw [heq]
  exact MeasurableSet.iUnion fun l => MeasurableSet.iUnion fun ξ =>
    (MarkedHistoryWords.fiber_measurable L t l ξ).inter (MeasurableSet.const _)

theorem graph_unique (L : Nat) (D I S : Finset Site) (t : Real) (z : Sample L)
    (T U : Finset Site) (hT : z ∈ graph L D I S t T) (hU : z ∈ graph L D I S t U) : T = U := by
  rcases hT with ⟨l,ξ,hl,hT⟩
  rcases hU with ⟨k,η,hk,hU⟩
  rw [← hT,← hU,fiber_events_eq L t z l k ξ η hl hk]

def state (L : Nat) (D I S : Finset Site) (t : Real) (z : Sample L) : Finset Site := by
  classical
  exact if h : ∃ T, z ∈ graph L D I S t T then h.choose else S

theorem state_eq_of_graph (L : Nat) (D I S : Finset Site) (t : Real) (z : Sample L)
    (T : Finset Site) (hT : z ∈ graph L D I S t T) : state L D I S t z = T := by
  classical
  have hex : ∃ U, z ∈ graph L D I S t U := ⟨T,hT⟩
  simp only [state,dite_eq_left hex]
  exact graph_unique L D I S t z _ T hex.choose_spec hT

theorem state_eq_iff (L : Nat) (D I S : Finset Site) (t : Real) (z : Sample L) (T : Finset Site) :
    state L D I S t z = T ↔ z ∈ graph L D I S t T ∨
      (¬ (∃ U, z ∈ graph L D I S t U)) ∧ S = T := by
  classical
  by_cases hex : ∃ U, z ∈ graph L D I S t U
  · have hg : z ∈ graph L D I S t (state L D I S t z) := by
      simpa only [state,dite_eq_left hex] using hex.choose_spec
    exact ⟨fun h => Or.inl (h ▸ hg),fun h => h.elim
      (state_eq_of_graph L D I S t z T) (fun h => False.elim (h.1 hex))⟩
  · simp only [state,dite_eq_right hex]
    constructor
    · exact fun h => Or.inr ⟨hex,h⟩
    · rintro (h | h)
      · exact False.elim (hex ⟨T,h⟩)
      · exact h.2

theorem state_fiber_measurable (L : Nat) (D I S : Finset Site) (t : Real) (T : Finset Site) :
    MeasurableSet[MarkedClockFiltration.history L t] {z | state L D I S t z = T} := by
  let : MeasurableSpace (Sample L) := MarkedClockFiltration.history L t
  have heq : {z : Sample L | state L D I S t z = T} = graph L D I S t T ∪
      (⋃ U : Finset Site, graph L D I S t U)ᶜ ∩ {z : Sample L | S = T} := by
    ext z
    simp only [Set.mem_ofPred_eq,state_eq_iff,Set.mem_union,Set.mem_inter_iff,Set.mem_compl_iff,
      Set.mem_iUnion]
  rw [heq]
  exact (graph_measurable L D I S t T).union
    ((MeasurableSet.iUnion (fun U => graph_measurable L D I S t U)).compl.inter (MeasurableSet.const _))

theorem state_measurable (L : Nat) (D I S : Finset Site) (t : Real) :
    @Measurable (Sample L) (Finset Site) (MarkedClockFiltration.history L t) stateSpace
      (state L D I S t) := by
  let : MeasurableSpace (Sample L) := MarkedClockFiltration.history L t
  let : MeasurableSpace (Finset Site) := stateSpace
  exact measurable_to_countable' fun T => state_fiber_measurable L D I S t T

theorem graph_stateAt (L : Nat) (D I S : Finset Site) (t : Real) (z : Sample L)
    (hg : ClockEventWord.Good z.1 t) :
    z ∈ graph L D I S t (DropletStoppedClockLaw.stateAt L D I S t z) := by
  let l := (ClockEventWord.word z.1 t).reverse
  let ξ : Fin l.length → Bool := fun i => z.2 l[i]
  have hcov : ∀ e : Event L, e ∈ l ↔ ClockEventWord.eventTime z.1 e ≤ t := by
    intro e
    exact List.mem_reverse.trans (ClockEventWord.word_mem_iff z.1 t hg e)
  have hf : fiber L t l ξ z := ⟨hcov,MarkedHistoryWords.chronological_ordered L t z hg,
    fun i => ⟨(hcov l[i]).mp (List.getElem_mem _),rfl⟩⟩
  refine ⟨l,ξ,hf,?_⟩
  rw [MarkedHistoryWords.fiber_indexedEvents_eq L t z l ξ hg hf]
  rfl

theorem state_eq_stateAt (L : Nat) (D I S : Finset Site) (t : Real) (z : Sample L)
    (hg : ClockEventWord.Good z.1 t) : state L D I S t z = DropletStoppedClockLaw.stateAt L D I S t z :=
  state_eq_of_graph L D I S t z _ (graph_stateAt L D I S t z hg)

theorem state_all_times_ae (L : Nat) (D I S : Finset Site) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ t : Real,
      state L D I S t z = DropletStoppedClockLaw.stateAt L D I S t z := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L] with z hz
  exact fun t => state_eq_stateAt L D I S t z (hz t)

theorem observable_measurable (L : Nat) (D I S : Finset Site) (t : Real)
    {α : Type*} [MeasurableSpace α] (f : Finset Site → α) :
    @Measurable (Sample L) α (MarkedClockFiltration.history L t) inferInstance
      (fun z => f (state L D I S t z)) := by
  let : MeasurableSpace (Finset Site) := stateSpace
  have hf : Measurable f := fun _ _ => trivial
  exact hf.comp (state_measurable L D I S t)

theorem removed_area_measurable (L : Nat) (D I S : Finset Site) (t : Real) :
    @Measurable (Sample L) Nat (MarkedClockFiltration.history L t) inferInstance
      (fun z => (S \ state L D I S t z).card) := observable_measurable L D I S t (fun T : Finset Site => (S \ T).card)

theorem frozen_at_exit (L : Nat) (D I S : Finset Site) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hfin : RationalProtectedExit.rationalExit L D I S z ≠ ⊤) (t : Real)
    (ht : (RationalProtectedExit.rationalExit L D I S z).toReal ≤ t) :
    state L D I S t z = state L D I S (RationalProtectedExit.rationalExit L D I S z).toReal z := by
  have he := RationalProtectedExit.rationalExit_eq_physicalExit L D I S z hg
  rw [state_eq_stateAt L D I S t z (hg t),state_eq_stateAt L D I S _ z (hg _),he]
  exact FrozenPhysicalExit.frozen_at_physical_exit L D I S z hg (he ▸ hfin) t (he ▸ ht)
theorem state_adapted_nn (L : Nat) (D I S : Finset Site) :
    letI : MeasurableSpace (Finset Site) := stateSpace
    Adapted (RationalProtectedExit.nnHistory L) (fun t : NNReal => state L D I S (t : Real)) := by
  exact fun t => state_measurable L D I S (t : Real)

theorem state_adapted_right (L : Nat) (D I S : Finset Site) :
    letI : MeasurableSpace (Finset Site) := stateSpace
    Adapted (RationalProtectedExit.rightHistory L) (fun t : NNReal => state L D I S (t : Real)) := by
  intro t
  exact (state_measurable L D I S (t : Real)).mono
    ((RationalProtectedExit.nnHistory L).le_rightCont t) le_rfl

theorem state_right_locally_constant_ae (L : Nat) (D I S : Finset Site) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ t : Real,
      ∃ b : Real, t < b ∧ ∀ u : Real, t ≤ u → u < b → state L D I S u z = state L D I S t z := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L] with z hz
  intro t
  obtain ⟨b,htb,hb⟩ := ClockWordConsistency.stateAt_right_locally_constant L D I S z t (hz (t+1))
  refine ⟨b,htb,?_⟩
  intro u htu hub
  rw [state_eq_stateAt L D I S u z (hz u),state_eq_stateAt L D I S t z (hz t)]
  exact hb u htu hub

theorem state_zero_ae (L : Nat) (D I S : Finset Site) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), state L D I S 0 z = S := by
  filter_upwards [state_all_times_ae L D I S,ClockWordConsistency.stateAt_zero_ae L D I S] with z hz hzero
  exact (hz 0).trans hzero

theorem quadratic_area_after_exit (L : Nat) (hL : 40 ≤ L) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t) (t : Real) (ht : 0 ≤ t)
    (hexit : RationalProtectedExit.rationalExit L (ClippedDiamondGeometry.clippedDomain L)
      (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L) z ≤ ENNReal.ofReal t) :
    (L : Real)^2/1600 ≤ ((ClippedDiamondGeometry.clippedDomain L \
      state L (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
        (ClippedDiamondGeometry.clippedDomain L) t z).card : Real) := by
  rw [state_eq_stateAt L _ _ _ t z (hg t)]
  apply FrozenPhysicalExit.quadratic_area_of_physical_exit_le L hL z hg t ht
  rw [← RationalProtectedExit.rationalExit_eq_physicalExit L _ _ _ z hg]
  exact hexit

theorem geometricGood_before_exit {L : Nat} (hL : 2 ≤ L) {S : Finset Site}
    (hS : ProtectedEvolution.Shape S) (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    (z : Sample L) (hg : ∀ t : Real, ClockEventWord.Good z.1 t) (t : Real) (ht : 0 ≤ t)
    (hbefore : ENNReal.ofReal t < RationalProtectedExit.rationalExit L
      (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L) S z) :
    ClippedInitialContour.GeometricGood L (state L (ClippedDiamondGeometry.clippedDomain L)
      (ClippedProtectedGeometry.protectedSites L) S t z) := by
  rw [state_eq_stateAt L _ _ _ t z (hg t)]
  apply FrozenPhysicalExit.geometricGood_before_physical_exit hL hS hclip z hg t ht
  rw [← RationalProtectedExit.rationalExit_eq_physicalExit L _ _ _ z hg]
  exact hbefore
end MathResearchAnalysis.ObservedFrozenProcess
