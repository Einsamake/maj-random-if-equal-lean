module
public import MathResearchAnalysis.ActualAreaTelescope
public import MathResearchAnalysis.RealPredictableCompensation
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
set_option autoImplicit false
/-! The actual finite area telescope equals the sum of the actual marked
arrival scores. Reindexing is justified by the genuine finite horizon word,
not by an assumed signed-sum interchange. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MarkedAreaSum
open MeasureTheory
open DropletClockLaw (Sample Event Vertex)
open InfiniteGridModel (Site)

/-- An actual identity contributes only if its strictly positive ring is
inside the horizon, and uses its own original mark. -/
def eventScore (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (e : Event L) : Real :=
  if 0 < ClockEventWord.eventTime z.1 e ∧ ClockEventWord.eventTime z.1 e ≤ (T : Real) then
    PredictableAreaContribution.increment L D I S e.1 (z.2 e)
      ((ClockEventWord.eventTime z.1 e).toNNReal,z)
  else 0

/-- Precisely one Boolean-mark window matches the identity's actual mark. -/
theorem bool_sum_term (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (v : Vertex L) (k : Nat) :
    (∑ b : Bool, RealPredictableCompensation.term L v b T
      (PredictableAreaContribution.increment L D I S v b) k z) =
      eventScore L D I S T z (v,k) := by
  classical
  by_cases ht : 0 < ClockEventWord.eventTime z.1 (v,k) ∧
      ClockEventWord.eventTime z.1 (v,k) ≤ (T : Real)
  · cases hm : z.2 (v,k) <;>
      simp [RealPredictableCompensation.term,
        MarkedClockPointMeasure.window,MarkedClockPointMeasure.point,eventScore,ht,hm]
  · have hz (b : Bool) : z ∉ MarkedClockPointMeasure.window L v b T k := by
      intro h
      exact ht ⟨h.1,h.2.1⟩
    simp only [RealPredictableCompensation.term,Set.indicator_of_notMem (hz _),
      Finset.sum_const_zero,eventScore,ite_eq_right ht]

theorem eventScore_zero_outside_word (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real))
    (e : Event L) (he : e ∉ (ClockEventWord.word z.1 (T : Real)).toFinset) :
    eventScore L D I S T z e = 0 := by
  have hnot : ¬ ClockEventWord.eventTime z.1 e ≤ (T : Real) := by
    intro ht
    exact he (List.mem_toFinset.mpr ((ClockEventWord.word_mem_iff z.1 (T : Real) hg e).mpr ht))
  simp [eventScore,hnot]

/-- The genuine finite horizon word proves signed summability pathwise. -/
theorem eventScore_summable (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real)) :
    Summable (eventScore L D I S T z) :=
  summable_of_ne_finset_zero (s := (ClockEventWord.word z.1 (T : Real)).toFinset)
    (eventScore_zero_outside_word L D I S T z hg)

/-- Each actual site/mark series is supported on the finite projection of the
true word. This proves the hypothesis needed before exchanging sum orders. -/
theorem term_summable (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real))
    (v : Vertex L) (b : Bool) :
    Summable (fun k : Nat => RealPredictableCompensation.term L v b T
      (PredictableAreaContribution.increment L D I S v b) k z) := by
  classical
  apply summable_of_ne_finset_zero
    (s := (ClockEventWord.word z.1 (T : Real)).toFinset.image Prod.snd)
  intro k hk
  have hz : z ∉ MarkedClockPointMeasure.window L v b T k := by
    intro h
    exact hk (Finset.mem_image.mpr ⟨(v,k),List.mem_toFinset.mpr
      ((ClockEventWord.word_mem_iff z.1 (T : Real) hg (v,k)).mpr h.2.1),rfl⟩)
  exact Set.indicator_of_notMem hz _

theorem sum_pathSums_eq_tsum_eventScore (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real)) :
    (∑ v : Vertex L, ∑ b : Bool, RealPredictableCompensation.pathSum L v b T
      (PredictableAreaContribution.increment L D I S v b) z) =
      ∑' e : Event L, eventScore L D I S T z e := by
  classical
  rw [(eventScore_summable L D I S T z hg).tsum_prod,tsum_fintype]
  apply Finset.sum_congr rfl
  intro v _
  unfold RealPredictableCompensation.pathSum
  rw [← Summable.tsum_finsetSum (s := Finset.univ)
    (f := fun b : Bool => fun k : Nat => RealPredictableCompensation.term L v b T
      (PredictableAreaContribution.increment L D I S v b) k z)
    (fun b _ => term_summable L D I S T z hg v b)]
  apply tsum_congr
  intro k
  exact bool_sum_term L D I S T z v k

theorem tsum_eventScore_eq_word_sum (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real))
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) :
    (∑' e : Event L, eventScore L D I S T z e) =
    ∑ e ∈ (ClockEventWord.word z.1 (T : Real)).toFinset,
      PredictableAreaContribution.increment L D I S e.1 (z.2 e)
        ((ClockEventWord.eventTime z.1 e).toNNReal,z) := by
  classical
  rw [tsum_eq_sum (s := (ClockEventWord.word z.1 (T : Real)).toFinset)
    (eventScore_zero_outside_word L D I S T z hg)]
  apply Finset.sum_congr rfl
  intro e he
  have ht := (ClockEventWord.word_mem_iff z.1 (T : Real) hg e).mp (List.mem_toFinset.mp he)
  change ClockEventWord.eventTime z.1 e ≤ (T : Real) at ht
  simp only [eventScore,hp e,ht,and_self,↓reduceIte]

theorem sum_pathSums_eq_word_sum (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real))
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) :
    (∑ v : Vertex L, ∑ b : Bool, RealPredictableCompensation.pathSum L v b T
      (PredictableAreaContribution.increment L D I S v b) z) =
    ∑ e ∈ (ClockEventWord.word z.1 (T : Real)).toFinset,
      PredictableAreaContribution.increment L D I S e.1 (z.2 e)
        ((ClockEventWord.eventTime z.1 e).toNNReal,z) :=
  (sum_pathSums_eq_tsum_eventScore L D I S T z hg).trans
    (tsum_eventScore_eq_word_sum L D I S T z hg hp)

/-- The actual full area change is exactly the sum of the site's true marked
pathwise contributions, including the event at the first-loss freeze. -/
theorem area_eq_pathSums (L : Nat) (D I S : Finset Site) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) (T : NNReal) :
    ((D \ DropletStoppedClockLaw.stateAt L D I S (T : Real) z).card : Real) -
      ((D \ S).card : Real) =
    ∑ v : Vertex L, ∑ b : Bool, RealPredictableCompensation.pathSum L v b T
      (PredictableAreaContribution.increment L D I S v b) z :=
  (ActualAreaTelescope.area_telescope_finset L D I S z hg hp T).trans
    (sum_pathSums_eq_word_sum L D I S T z (hg _) hp).symm

/-- One full-probability set works at every horizon, with the original sample
law. No separate exceptional set is chosen for a random observation time. -/
theorem area_eq_pathSums_all_times_ae (L : Nat) (D I S : Finset Site) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ T : NNReal,
    ((D \ DropletStoppedClockLaw.stateAt L D I S (T : Real) z).card : Real) -
      ((D \ S).card : Real) =
    ∑ v : Vertex L, ∑ b : Bool, RealPredictableCompensation.pathSum L v b T
      (PredictableAreaContribution.increment L D I S v b) z := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L,
    ActualPreState.marked_all_events_positive_ae L] with z hg hp
  exact fun T => area_eq_pathSums L D I S z hg hp T
end MathResearchAnalysis.MarkedAreaSum

#print axioms MathResearchAnalysis.MarkedAreaSum.eventScore
#print axioms MathResearchAnalysis.MarkedAreaSum.bool_sum_term
#print axioms MathResearchAnalysis.MarkedAreaSum.eventScore_zero_outside_word
#print axioms MathResearchAnalysis.MarkedAreaSum.eventScore_summable
#print axioms MathResearchAnalysis.MarkedAreaSum.term_summable
#print axioms MathResearchAnalysis.MarkedAreaSum.sum_pathSums_eq_tsum_eventScore
#print axioms MathResearchAnalysis.MarkedAreaSum.tsum_eventScore_eq_word_sum
#print axioms MathResearchAnalysis.MarkedAreaSum.sum_pathSums_eq_word_sum
#print axioms MathResearchAnalysis.MarkedAreaSum.area_eq_pathSums
#print axioms MathResearchAnalysis.MarkedAreaSum.area_eq_pathSums_all_times_ae
