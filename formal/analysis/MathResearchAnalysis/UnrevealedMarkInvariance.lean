module
public import MathResearchAnalysis.MarkedStoppedResidual
public import MathResearchAnalysis.InfiniteGridComplement
set_option autoImplicit false
/-! Resampling an unrevealed identity mark preserves actual joint-past events and any actual marked-history stopping rule before that ring. Single-coordinate fair flips preserve the actual mark product law. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.UnrevealedMarkInvariance
open MeasureTheory
open DropletClockLaw (Sample Event)

def replaceMark (L : Nat) (e : Event L) (b : Bool) (z : Sample L) : Sample L :=
  (z.1,Function.update z.2 e b)

theorem history_invariant (L : Nat) (e : Event L) (b : Bool) (z : Sample L) (r : Real)
    (hf : r < ClockEventWord.eventTime z.1 e) (E : Set (Sample L))
    (hE : MeasurableSet[MarkedClockFiltration.history L r] E) :
    z ∈ E ↔ replaceMark L e b z ∈ E := by
  apply MarkedClockFiltration.measurable_event_past_invariant L r z (replaceMark L e b z) ?_ ?_ hE
  · intro d u _
    rfl
  · intro d hd
    have hde : d ≠ e := by
      intro he
      subst d
      exact not_le_of_gt hf hd
    simp only [replaceMark,Function.update_of_ne hde]

theorem stoppingTime_invariant (L : Nat) (e : Event L) (b : Bool) (z : Sample L)
    (R : Sample L → WithTop Real) (hR : IsStoppingTime (MarkedClockFiltration.history L) R)
    (r : Real) (hz : R z = (r : WithTop Real)) (hf : r < ClockEventWord.eventTime z.1 e) :
    R (replaceMark L e b z) = R z := by
  have hle : R (replaceMark L e b z) ≤ (r : WithTop Real) :=
    (history_invariant L e b z r hf {w | R w ≤ r} (hR r)).mp (by change R z ≤ (r : WithTop Real); rw [hz])
  rw [hz]
  apply le_antisymm hle
  by_contra h
  have hlt : R (replaceMark L e b z) < (r : WithTop Real) := lt_of_not_ge h
  cases hw : R (replaceMark L e b z) using WithTop.recTopCoe with
  | top => simp only [hw,not_top_lt] at hlt
  | coe s =>
    have hsr : s < r := by simpa only [hw,WithTop.coe_lt_coe] using hlt
    have hobs := history_invariant L e b z s (hsr.trans hf) {w | R w ≤ s} (hR s)
    have hzs : R z ≤ (s : WithTop Real) := hobs.mpr (by change R (replaceMark L e b z) ≤ (s : WithTop Real); rw [hw])
    rw [hz] at hzs
    exact not_le_of_gt hsr (WithTop.coe_le_coe.mp hzs)

theorem stopped_history_invariant (L : Nat) (e : Event L) (b : Bool) (z : Sample L)
    (R : Sample L → WithTop Real) (hR : IsStoppingTime (MarkedClockFiltration.history L) R)
    (r : Real) (hz : R z = (r : WithTop Real)) (hf : r < ClockEventWord.eventTime z.1 e)
    (E : Set (Sample L)) (hE : MeasurableSet[hR.measurableSpace] E) :
    z ∈ E ↔ replaceMark L e b z ∈ E := by
  have hw := stoppingTime_invariant L e b z R hR r hz hf
  have he := history_invariant L e b z r hf (E ∩ {w | R w ≤ r}) (((hR.measurableSet E).mp hE).2 r)
  simpa only [Set.mem_inter_iff,Set.mem_ofPred_eq,hw,hz,le_refl,and_true] using he

def flipField {I : Type*} [DecidableEq I] (e : I) (η : FairMarks.Sample I) : FairMarks.Sample I :=
  Function.update η e (!(η e))

theorem flipField_measurable {I : Type*} [DecidableEq I] (e : I) : Measurable (flipField e) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i = e
  · subst i
    simpa only [flipField,Function.update_self,Function.comp_def] using
      (measurable_of_countable Bool.not).comp (measurable_pi_apply e)
  · simpa only [flipField,Function.update_of_ne hi] using measurable_pi_apply i

theorem flipField_involutive {I : Type*} [DecidableEq I] (e : I) : Function.Involutive (flipField e) := by
  intro η
  funext i
  by_cases hi : i = e <;> simp [flipField,hi]

theorem flipField_map {I : Type*} [DecidableEq I] (e : I) :
    Measure.map (flipField e) (FairMarks.markMeasure I) = FairMarks.markMeasure I := by
  have heq : flipField e = (fun η : FairMarks.Sample I => fun i => if i = e then !(η i) else η i) := by
    funext η i
    by_cases hi : i = e <;> simp [flipField,hi]
  rw [heq]
  change (Measure.infinitePi (fun _ : I => FairMarks.fair)).map
    (fun η i => (fun b : Bool => if i = e then !b else b) (η i)) = Measure.infinitePi (fun _ : I => FairMarks.fair)
  rw [Measure.infinitePi_map_pi (f := fun i (b : Bool) => if i = e then !b else b)
    (fun _ : I => FairMarks.fair) (fun i => by
    by_cases hi : i = e
    · simpa only [hi,ite_true] using measurable_of_countable Bool.not
    · simpa only [hi,ite_false] using measurable_of_countable (fun b : Bool => b))]
  congr 1
  funext i
  by_cases hi : i = e
  · simp only [hi,ite_true,InfiniteGridComplement.fair_map_not]
  · simp only [hi,ite_false,Measure.map_id']

def flipSample (L : Nat) (e : Event L) (z : Sample L) : Sample L := (z.1,flipField e z.2)

theorem flipSample_measurable (L : Nat) (e : Event L) : Measurable (flipSample L e) :=
  measurable_fst.prodMk ((flipField_measurable e).comp measurable_snd)

theorem flipSample_involutive (L : Nat) (e : Event L) : Function.Involutive (flipSample L e) := by
  intro z
  exact Prod.ext rfl (flipField_involutive e z.2)

theorem flipSample_map (L : Nat) (e : Event L) :
    Measure.map (flipSample L e) (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  change Measure.map (Prod.map id (flipField e))
    ((ExponentialClocks.clockMeasure (DropletClockLaw.Vertex L)).prod (FairMarks.markMeasure (Event L))) = _
  rw [← Measure.map_prod_map _ _ measurable_id (flipField_measurable e),Measure.map_id,flipField_map]
  rfl
end MathResearchAnalysis.UnrevealedMarkInvariance
