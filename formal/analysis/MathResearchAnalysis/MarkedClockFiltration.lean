module
public import MathResearchAnalysis.DropletStoppedClockLaw
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
set_option autoImplicit false
/-! The actual joint arrival/mark observation filtration. Before a ring occurs its mark is unrevealed. No global clock-Good event or complete future field is included among the generators. This module does not assert adaptedness of the total clock word or stopping-time status of physicalExit. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MarkedClockFiltration
open MeasureTheory
open DropletClockLaw (Sample Event Vertex)

theorem arrival_measurable (L : Nat) (e : Event L) :
    Measurable (fun z : Sample L => ClockEventWord.eventTime z.1 e) :=
  (ClockEventWord.eventTime_measurable e).comp measurable_fst

theorem mark_measurable (L : Nat) (e : Event L) :
    Measurable (fun z : Sample L => z.2 e) := (measurable_pi_apply e).comp measurable_snd

def observations (L : Nat) (t : Real) : Set (Set (Sample L)) :=
  {B | ∃ e : Event L, ∃ u : Real, u ≤ t ∧
    (B = {z | ClockEventWord.eventTime z.1 e ≤ u} ∨
      ∃ b : Bool, B = {z | ClockEventWord.eventTime z.1 e ≤ u ∧ z.2 e = b})}

def history (L : Nat) : Filtration Real (inferInstance : MeasurableSpace (Sample L)) where
  seq t := MeasurableSpace.generateFrom (observations L t)
  mono' s t hst := MeasurableSpace.generateFrom_mono (by
    rintro B ⟨e,u,hu,hB⟩
    exact ⟨e,u,hu.trans hst,hB⟩)
  le' t := MeasurableSpace.generateFrom_le (by
    rintro B ⟨e,u,_,hB⟩
    rcases hB with rfl | ⟨b,rfl⟩
    · exact measurableSet_le (arrival_measurable L e) measurable_const
    · exact (measurableSet_le (arrival_measurable L e) measurable_const).inter
        (measurableSet_eq_fun (mark_measurable L e) measurable_const))

theorem arrival_event_measurable (L : Nat) (e : Event L) {u t : Real} (hut : u ≤ t) :
    MeasurableSet[history L t] {z | ClockEventWord.eventTime z.1 e ≤ u} :=
  MeasurableSpace.measurableSet_generateFrom ⟨e,u,hut,Or.inl rfl⟩

theorem marked_event_measurable (L : Nat) (e : Event L) (b : Bool) {u t : Real} (hut : u ≤ t) :
    MeasurableSet[history L t] {z | ClockEventWord.eventTime z.1 e ≤ u ∧ z.2 e = b} :=
  MeasurableSpace.measurableSet_generateFrom ⟨e,u,hut,Or.inr ⟨b,rfl⟩⟩

theorem arrival_isStoppingTime (L : Nat) (e : Event L) :
    IsStoppingTime (history L) (fun z : Sample L => (ClockEventWord.eventTime z.1 e : WithTop Real)) := by
  intro t
  convert arrival_event_measurable L e (u := t) le_rfl using 1
  ext z
  simp only [Set.mem_ofPred_eq,WithTop.coe_le_coe]

theorem history_le_of_observations (L : Nat)
    (F : Filtration Real (inferInstance : MeasurableSpace (Sample L)))
    (ha : ∀ e : Event L, ∀ u : Real, MeasurableSet[F u] {z | ClockEventWord.eventTime z.1 e ≤ u})
    (hm : ∀ e : Event L, ∀ u : Real, ∀ b : Bool,
      MeasurableSet[F u] {z | ClockEventWord.eventTime z.1 e ≤ u ∧ z.2 e = b}) (t : Real) :
    history L t ≤ F t := by
  apply MeasurableSpace.generateFrom_le
  rintro B ⟨e,u,hu,hB⟩
  rcases hB with rfl | ⟨b,rfl⟩
  · exact F.mono hu _ (ha e u)
  · exact F.mono hu _ (hm e u b)

/-- The three possible observations carry the discrete sigma algebra. -/
abbrev markSpace : MeasurableSpace (Option Bool) := ⊤

def revealedMark (L : Nat) (e : Event L) (u : Real) (z : Sample L) : Option Bool :=
  if ClockEventWord.eventTime z.1 e ≤ u then some (z.2 e) else none

@[simp] theorem revealedMark_none_iff (L : Nat) (e : Event L) (u : Real) (z : Sample L) :
    revealedMark L e u z = none ↔ ¬ ClockEventWord.eventTime z.1 e ≤ u := by
  by_cases h : ClockEventWord.eventTime z.1 e ≤ u <;> simp [revealedMark,h]

@[simp] theorem revealedMark_some_iff (L : Nat) (e : Event L) (u : Real) (z : Sample L) (b : Bool) :
    revealedMark L e u z = some b ↔ ClockEventWord.eventTime z.1 e ≤ u ∧ z.2 e = b := by
  by_cases h : ClockEventWord.eventTime z.1 e ≤ u <;> simp [revealedMark,h]

theorem revealedMark_measurable (L : Nat) (e : Event L) {u t : Real} (hut : u ≤ t) :
    @Measurable (Sample L) (Option Bool) (history L t) markSpace (revealedMark L e u) := by
  let : MeasurableSpace (Sample L) := history L t
  let : MeasurableSpace (Option Bool) := markSpace
  apply measurable_to_countable'
  intro b
  cases b with
  | none =>
    have hset : (revealedMark L e u) ⁻¹' {none} = {z | ClockEventWord.eventTime z.1 e ≤ u}ᶜ := by
      ext z
      simp only [Set.mem_preimage,Set.mem_singleton_iff,revealedMark_none_iff,Set.mem_compl_iff,Set.mem_ofPred_eq]
    rw [hset]
    exact (arrival_event_measurable L e hut).compl
  | some b =>
    have hset : (revealedMark L e u) ⁻¹' {some b} = {z | ClockEventWord.eventTime z.1 e ≤ u ∧ z.2 e = b} := by
      ext z
      simp only [Set.mem_preimage,Set.mem_singleton_iff,revealedMark_some_iff,Set.mem_ofPred_eq]
    rw [hset]
    exact marked_event_measurable L e b hut

theorem revealedMarks_measurable (L : Nat) {u t : Real} (hut : u ≤ t) :
    @Measurable (Sample L) (Event L → Option Bool) (history L t)
      (@MeasurableSpace.pi (Event L) (fun _ => Option Bool) (fun _ => markSpace))
      (fun z e => revealedMark L e u z) := by
  let : MeasurableSpace (Sample L) := history L t
  let : MeasurableSpace (Option Bool) := markSpace
  exact measurable_pi_iff.mpr (fun e => revealedMark_measurable L e hut)

theorem arrival_history_le (L : Nat) (t : Real) :
    ArrivalFiltration.history
      (fun (v : Vertex L) (k : Nat) (z : Sample L) => ClockEventWord.eventTime z.1 (v,k))
      (fun v k => arrival_measurable L (v,k)) t ≤ history L t :=
  ArrivalFiltration.history_le_of_arrivals_stopping _ _ (history L) (fun v k => arrival_isStoppingTime L (v,k)) t

/-- Every history-measurable event is invariant under changes invisible to the observed past. -/
theorem measurable_event_past_invariant (L : Nat) (t : Real) (z w : Sample L)
    (ha : ∀ e : Event L, ∀ u : Real, u ≤ t →
      (ClockEventWord.eventTime z.1 e ≤ u ↔ ClockEventWord.eventTime w.1 e ≤ u))
    (hm : ∀ e : Event L, ClockEventWord.eventTime z.1 e ≤ t → z.2 e = w.2 e)
    {B : Set (Sample L)} (hB : MeasurableSet[history L t] B) : z ∈ B ↔ w ∈ B := by
  have hobs : ∀ A ∈ observations L t, z ∈ A ↔ w ∈ A := by
    rintro A ⟨e,u,hu,hA⟩
    rcases hA with rfl | ⟨b,rfl⟩
    · exact ha e u hu
    · change (ClockEventWord.eventTime z.1 e ≤ u ∧ z.2 e = b) ↔
        (ClockEventWord.eventTime w.1 e ≤ u ∧ w.2 e = b)
      constructor
      · rintro ⟨hz,hzb⟩
        exact ⟨(ha e u hu).mp hz,(hm e (hz.trans hu)).symm.trans hzb⟩
      · rintro ⟨hw,hwb⟩
        have hz := (ha e u hu).mpr hw
        exact ⟨hz,(hm e (hz.trans hu)).trans hwb⟩
  exact (MeasurableSpace.forall_generateFrom_mem_iff_mem_iff
    (S := observations L t) (x := z) (y := w)).mpr hobs B hB

theorem coverage_measurable (L : Nat) (t : Real) (l : List (Event L)) :
    MeasurableSet[history L t] {z | ∀ e : Event L, e ∈ l ↔ ClockEventWord.eventTime z.1 e ≤ t} := by
  let : MeasurableSpace (Sample L) := history L t
  have heq : {z : Sample L | ∀ e : Event L, e ∈ l ↔ ClockEventWord.eventTime z.1 e ≤ t} =
      ⋂ e : Event L, {z : Sample L | e ∈ l ↔ ClockEventWord.eventTime z.1 e ≤ t} := by
    ext z
    simp
  rw [heq]
  exact MeasurableSet.iInter fun e => (MeasurableSet.const (e ∈ l)).iff
    (arrival_event_measurable L e (u := t) le_rfl)

theorem finite_arrivals_measurable (L : Nat) (t : Real) :
    MeasurableSet[history L t] {z | (ClockEventWord.eventSet z.1 t).Finite} := by
  classical
  let : MeasurableSpace (Sample L) := history L t
  have heq : {z : Sample L | (ClockEventWord.eventSet z.1 t).Finite} =
      ⋃ l : List (Event L), {z : Sample L | ∀ e : Event L, e ∈ l ↔ ClockEventWord.eventTime z.1 e ≤ t} := by
    ext z
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · intro hf
      refine ⟨hf.toFinset.toList,?_⟩
      intro e
      simp only [Finset.mem_toList,Set.Finite.mem_toFinset,ClockEventWord.eventSet,Set.mem_ofPred_eq]
    · rintro ⟨l,hl⟩
      apply l.finite_toSet.subset
      exact fun e he => (hl e).mpr he
  rw [heq]
  exact MeasurableSet.iUnion (coverage_measurable L t)
end MathResearchAnalysis.MarkedClockFiltration
