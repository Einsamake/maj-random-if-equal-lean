module
public import MathResearchAnalysis.RealPredictableCompensation
public import MathResearchAnalysis.ActualAreaTelescope
set_option autoImplicit false
/-! Exact reindexing of arbitrary real scores evaluated at the original marked
clock arrivals. On genuinely locally finite, positive clock paths the actual
identity sum equals the original site/mark path sums. No measurability,
compensator, state update or recovery assertion is assumed in these finite
pathwise identities. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MachineEventScores
open MeasureTheory
open DropletClockLaw (Sample Event Vertex)

def eventScore (L : Nat) (score : Vertex L → Bool → NNReal × Sample L → Real) (T : NNReal)
    (z : Sample L) (e : Event L) : Real :=
  if 0 < ClockEventWord.eventTime z.1 e ∧ ClockEventWord.eventTime z.1 e ≤ (T : Real) then
    score e.1 (z.2 e)
      ((ClockEventWord.eventTime z.1 e).toNNReal,z)
  else 0

/-- Precisely one Boolean-mark window matches the identity's actual mark. -/
theorem bool_sum_term (L : Nat) (score : Vertex L → Bool → NNReal × Sample L → Real) (T : NNReal)
    (z : Sample L) (v : Vertex L) (k : Nat) :
    (∑ b : Bool, RealPredictableCompensation.term L v b T
      (score v b) k z) =
      eventScore L score T z (v,k) := by
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

theorem eventScore_zero_outside_word (L : Nat) (score : Vertex L → Bool → NNReal × Sample L → Real) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real))
    (e : Event L) (he : e ∉ (ClockEventWord.word z.1 (T : Real)).toFinset) :
    eventScore L score T z e = 0 := by
  have hnot : ¬ ClockEventWord.eventTime z.1 e ≤ (T : Real) := by
    intro ht
    exact he (List.mem_toFinset.mpr ((ClockEventWord.word_mem_iff z.1 (T : Real) hg e).mpr ht))
  simp [eventScore,hnot]

/-- The genuine finite horizon word proves signed summability pathwise. -/
theorem eventScore_summable (L : Nat) (score : Vertex L → Bool → NNReal × Sample L → Real) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real)) :
    Summable (eventScore L score T z) :=
  summable_of_ne_finset_zero (s := (ClockEventWord.word z.1 (T : Real)).toFinset)
    (eventScore_zero_outside_word L score T z hg)

/-- Each actual site/mark series is supported on the finite projection of the
true word. This proves the hypothesis needed before exchanging sum orders. -/
theorem term_summable (L : Nat) (score : Vertex L → Bool → NNReal × Sample L → Real) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real))
    (v : Vertex L) (b : Bool) :
    Summable (fun k : Nat => RealPredictableCompensation.term L v b T
      (score v b) k z) := by
  classical
  apply summable_of_ne_finset_zero
    (s := (ClockEventWord.word z.1 (T : Real)).toFinset.image Prod.snd)
  intro k hk
  have hz : z ∉ MarkedClockPointMeasure.window L v b T k := by
    intro h
    exact hk (Finset.mem_image.mpr ⟨(v,k),List.mem_toFinset.mpr
      ((ClockEventWord.word_mem_iff z.1 (T : Real) hg (v,k)).mpr h.2.1),rfl⟩)
  exact Set.indicator_of_notMem hz _

theorem sum_pathSums_eq_tsum_eventScore (L : Nat) (score : Vertex L → Bool → NNReal × Sample L → Real) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real)) :
    (∑ v : Vertex L, ∑ b : Bool, RealPredictableCompensation.pathSum L v b T
      (score v b) z) =
      ∑' e : Event L, eventScore L score T z e := by
  classical
  rw [(eventScore_summable L score T z hg).tsum_prod,tsum_fintype]
  apply Finset.sum_congr rfl
  intro v _
  unfold RealPredictableCompensation.pathSum
  rw [← Summable.tsum_finsetSum (s := Finset.univ)
    (f := fun b : Bool => fun k : Nat => RealPredictableCompensation.term L v b T
      (score v b) k z)
    (fun b _ => term_summable L score T z hg v b)]
  apply tsum_congr
  intro k
  exact bool_sum_term L score T z v k

theorem tsum_eventScore_eq_word_sum (L : Nat) (score : Vertex L → Bool → NNReal × Sample L → Real) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real))
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) :
    (∑' e : Event L, eventScore L score T z e) =
    ∑ e ∈ (ClockEventWord.word z.1 (T : Real)).toFinset,
      score e.1 (z.2 e)
        ((ClockEventWord.eventTime z.1 e).toNNReal,z) := by
  classical
  rw [tsum_eq_sum (s := (ClockEventWord.word z.1 (T : Real)).toFinset)
    (eventScore_zero_outside_word L score T z hg)]
  apply Finset.sum_congr rfl
  intro e he
  have ht := (ClockEventWord.word_mem_iff z.1 (T : Real) hg e).mp (List.mem_toFinset.mp he)
  change ClockEventWord.eventTime z.1 e ≤ (T : Real) at ht
  simp only [eventScore,hp e,ht,and_self,↓reduceIte]

theorem sum_pathSums_eq_word_sum (L : Nat) (score : Vertex L → Bool → NNReal × Sample L → Real) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real))
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) :
    (∑ v : Vertex L, ∑ b : Bool, RealPredictableCompensation.pathSum L v b T
      (score v b) z) =
    ∑ e ∈ (ClockEventWord.word z.1 (T : Real)).toFinset,
      score e.1 (z.2 e)
        ((ClockEventWord.eventTime z.1 e).toNNReal,z) :=
  (sum_pathSums_eq_tsum_eventScore L score T z hg).trans
    (tsum_eventScore_eq_word_sum L score T z hg hp)

end MathResearchAnalysis.MachineEventScores
