module
public import MathResearchAnalysis.MarkedClockFiltration
public import MathResearchAnalysis.ClockWordConsistency
set_option autoImplicit false
/-! Finite observed histories determine actual frozen loss on the genuine clock-good samples. No future global-Good event is included in the history. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MarkedHistoryWords
open MeasureTheory
open DropletClockLaw (Sample Event)
open MarkedClockFiltration (history)

def censoredArrival (L : Nat) (t : Real) (e : Event L) (z : Sample L) : Real :=
  min (ClockEventWord.eventTime z.1 e) t

theorem censoredArrival_measurable (L : Nat) (t : Real) (e : Event L) :
    @Measurable (Sample L) Real (history L t) inferInstance (censoredArrival L t e) := by
  let : MeasurableSpace (Sample L) := history L t
  apply measurable_of_Iic
  intro x
  by_cases h : t ≤ x
  · have hset : (censoredArrival L t e) ⁻¹' Set.Iic x = Set.univ := by
      ext z
      simp only [Set.mem_preimage,Set.mem_Iic,Set.mem_univ,iff_true]
      exact (min_le_right _ _).trans h
    rw [hset]
    exact MeasurableSet.univ
  · have hset : (censoredArrival L t e) ⁻¹' Set.Iic x = {z | ClockEventWord.eventTime z.1 e ≤ x} := by
      ext z
      simp only [Set.mem_preimage,Set.mem_Iic,censoredArrival,min_le_iff,Set.mem_ofPred_eq,or_iff_left h]
    rw [hset]
    exact MarkedClockFiltration.arrival_event_measurable L e (le_of_not_ge h)

theorem censoredArrival_eq_of_arrived (L : Nat) (t : Real) (e : Event L) (z : Sample L)
    (he : ClockEventWord.eventTime z.1 e ≤ t) : censoredArrival L t e z = ClockEventWord.eventTime z.1 e := min_eq_left he

def ordered (L : Nat) (t : Real) (l : List (Event L)) (z : Sample L) : Prop :=
  l.Pairwise (fun a b => censoredArrival L t a z < censoredArrival L t b z)

theorem ordered_measurable (L : Nat) (t : Real) (l : List (Event L)) :
    MeasurableSet[history L t] {z | ordered L t l z} := by
  let : MeasurableSpace (Sample L) := history L t
  induction l with
  | nil =>
    have heq : {z : Sample L | ordered L t [] z} = Set.univ := by
      ext z
      exact ⟨fun _ => Set.mem_univ z,fun _ => List.Pairwise.nil⟩
    rw [heq]
    exact MeasurableSet.univ
  | cons e l ih =>
    have heq : {z : Sample L | ordered L t (e::l) z} =
        (⋂ b : Event L, ⋂ (_ : b ∈ l), {z | censoredArrival L t e z < censoredArrival L t b z}) ∩
          {z | ordered L t l z} := by
      ext z
      simp only [ordered,List.pairwise_cons,Set.mem_inter_iff,Set.mem_iInter,Set.mem_ofPred_eq]
    rw [heq]
    exact (MeasurableSet.iInter (fun b => MeasurableSet.iInter (fun _ =>
      measurableSet_lt (censoredArrival_measurable L t e) (censoredArrival_measurable L t b)))).inter ih

def fiber (L : Nat) (t : Real) (l : List (Event L)) (ξ : Fin l.length → Bool) (z : Sample L) : Prop :=
  (∀ e : Event L, e ∈ l ↔ ClockEventWord.eventTime z.1 e ≤ t) ∧ ordered L t l z ∧
    ∀ i : Fin l.length, ClockEventWord.eventTime z.1 l[i] ≤ t ∧ z.2 l[i] = ξ i

theorem fiber_measurable (L : Nat) (t : Real) (l : List (Event L)) (ξ : Fin l.length → Bool) :
    MeasurableSet[history L t] {z | fiber L t l ξ z} := by
  let : MeasurableSpace (Sample L) := history L t
  have hm : MeasurableSet[history L t] {z : Sample L | ∀ i : Fin l.length,
      ClockEventWord.eventTime z.1 l[i] ≤ t ∧ z.2 l[i] = ξ i} := by
    convert (MeasurableSet.iInter fun i : Fin l.length =>
      MarkedClockFiltration.marked_event_measurable L l[i] (ξ i) (u := t) (t := t) le_rfl) using 1
    ext z
    simp only [Set.mem_iInter,Set.mem_ofPred_eq]
  exact (MarkedClockFiltration.coverage_measurable L t l).inter ((ordered_measurable L t l).inter hm)

theorem chronological_ordered (L : Nat) (t : Real) (z : Sample L)
    (hg : ClockEventWord.Good z.1 t) : ordered L t (ClockEventWord.word z.1 t).reverse z := by
  apply (ClockEventWord.word_reverse_strictly_increasing z.1 t).imp_of_mem
  intro a b ha hb hab
  rw [censoredArrival_eq_of_arrived L t a z ((ClockEventWord.word_mem_iff z.1 t hg a).mp (List.mem_reverse.mp ha)),
    censoredArrival_eq_of_arrived L t b z ((ClockEventWord.word_mem_iff z.1 t hg b).mp (List.mem_reverse.mp hb))]
  exact hab

theorem identity_word_eq (L : Nat) (t : Real) (z : Sample L) (l : List (Event L))
    (hg : ClockEventWord.Good z.1 t)
    (hcov : ∀ e : Event L, e ∈ l ↔ ClockEventWord.eventTime z.1 e ≤ t) (ho : ordered L t l z) :
    l = (ClockEventWord.word z.1 t).reverse := by
  have hn : l.Nodup := ho.imp (fun {a b} hlt heq => by subst b; exact (lt_irrefl _ hlt))
  have hp := (List.perm_ext_iff_of_nodup hn (List.nodup_reverse.mpr (ClockEventWord.word_nodup z.1 t))).mpr
    (fun e => by simpa only [List.mem_reverse,ClockEventWord.word_mem_iff z.1 t hg e,ClockEventWord.eventSet,Set.mem_ofPred_eq] using hcov e)
  exact List.Perm.eq_of_pairwise
    (fun a b _ _ hab hba => False.elim ((not_lt_of_gt hab) hba)) ho (chronological_ordered L t z hg) hp

def indexedEvents (L : Nat) (l : List (Event L)) (ξ : Fin l.length → Bool) : List DropletModifiedWord.Event :=
  List.ofFn (fun i : Fin l.length => (ClippedSquareCoordinates.recenter L l[i].1,ξ i))

theorem indexedEvents_eq_map (L : Nat) (l : List (Event L)) (ξ : Fin l.length → Bool) (z : Sample L)
    (hmark : ∀ i : Fin l.length, z.2 l[i] = ξ i) :
    indexedEvents L l ξ = l.map (fun e => (ClippedSquareCoordinates.recenter L e.1,z.2 e)) := by
  apply List.ext_getElem
  · simp [indexedEvents]
  · intro i hi hj
    simp only [indexedEvents,List.getElem_ofFn,List.getElem_map]
    exact Prod.ext rfl (hmark ⟨i,by simpa only [indexedEvents,List.length_ofFn] using hi⟩).symm

theorem fiber_indexedEvents_eq (L : Nat) (t : Real) (z : Sample L) (l : List (Event L))
    (ξ : Fin l.length → Bool) (hg : ClockEventWord.Good z.1 t) (hf : fiber L t l ξ z) :
    indexedEvents L l ξ = DropletClockLaw.markedEvents L (ClockEventWord.word z.1 t) z.2 := by
  rw [indexedEvents_eq_map L l ξ z (fun i => (hf.2.2 i).2),identity_word_eq L t z l hg hf.1 hf.2.1]
  rfl

def observedLoss (L : Nat) (D I S : Finset InfiniteGridModel.Site) (t : Real) : Set (Sample L) :=
  {z | ∃ l : List (Event L), ∃ ξ : Fin l.length → Bool, fiber L t l ξ z ∧
    ¬ I ⊆ DropletStoppedWord.stoppedWord D I S (indexedEvents L l ξ)}

theorem observedLoss_measurable (L : Nat) (D I S : Finset InfiniteGridModel.Site) (t : Real) :
    MeasurableSet[history L t] (observedLoss L D I S t) := by
  let : MeasurableSpace (Sample L) := history L t
  have heq : observedLoss L D I S t = ⋃ l : List (Event L), ⋃ ξ : Fin l.length → Bool,
      {z | fiber L t l ξ z} ∩ {z : Sample L | ¬ I ⊆ DropletStoppedWord.stoppedWord D I S (indexedEvents L l ξ)} := by
    ext z
    simp only [observedLoss,Set.mem_iUnion,Set.mem_inter_iff,Set.mem_ofPred_eq]
  rw [heq]
  exact MeasurableSet.iUnion fun l => MeasurableSet.iUnion fun ξ =>
    (fiber_measurable L t l ξ).inter (MeasurableSet.const _)

theorem observedLoss_iff (L : Nat) (D I S : Finset InfiniteGridModel.Site) (t : Real) (z : Sample L)
    (hg : ClockEventWord.Good z.1 t) : z ∈ observedLoss L D I S t ↔
      ¬ I ⊆ DropletStoppedClockLaw.stateAt L D I S t z := by
  constructor
  · rintro ⟨l,ξ,hf,hloss⟩
    simpa only [DropletStoppedClockLaw.stateAt,← fiber_indexedEvents_eq L t z l ξ hg hf] using hloss
  · intro hloss
    let l := (ClockEventWord.word z.1 t).reverse
    let ξ : Fin l.length → Bool := fun i => z.2 l[i]
    have hcov : ∀ e : Event L, e ∈ l ↔ ClockEventWord.eventTime z.1 e ≤ t := by
      intro e
      exact List.mem_reverse.trans (ClockEventWord.word_mem_iff z.1 t hg e)
    have hf : fiber L t l ξ z := ⟨hcov,chronological_ordered L t z hg,
      fun i => ⟨(hcov l[i]).mp (List.getElem_mem _),rfl⟩⟩
    refine ⟨l,ξ,hf,?_⟩
    simpa only [fiber_indexedEvents_eq L t z l ξ hg hf,DropletStoppedClockLaw.stateAt] using hloss
end MathResearchAnalysis.MarkedHistoryWords
