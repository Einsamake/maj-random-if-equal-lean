module

public import MathResearchAnalysis.FairMarks
public import MathResearchAnalysis.ClockEventWord
public import MathResearchAnalysis.SquareTasks
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Nodup

set_option autoImplicit false

/-!
# Fair marks on the actual bounded-time clock word

The clock-word prefix is a measurable clock-only identity selection. Its
pointwise absence of repeated identities is proved from the actual word.
On the event that at least r rings occurred, the selected marks have their
fresh fair product law jointly with every measurable clock event.
No conditional-mark-law conclusion is supplied as an input.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace MathResearchAnalysis.ClockWordMarks

abbrev Site (n : Nat) := SquareTasks.Vertex n
abbrev Event (n : Nat) := Site n × Nat
abbrev Sample (n : Nat) := ExponentialClocks.Sample (Site n) × FairMarks.Sample (Event n)

def measure (n : Nat) : Measure (Sample n) :=
  (ExponentialClocks.clockMeasure (Site n)).prod (FairMarks.markMeasure (Event n))

instance measure_probability (n : Nat) : IsProbabilityMeasure (measure n) := by
  unfold measure
  infer_instance

def fallback (n : Nat) : Event n := ((⟨0, by omega⟩, ⟨0, by omega⟩), 0)

def prefixSelection (n : Nat) (t : ℝ) (r : Nat)
    (ω : ExponentialClocks.Sample (Site n)) : Fin r → Event n :=
  fun k => (ClockEventWord.word ω t).getD k.val (fallback n)

theorem prefixSelection_measurable (n : Nat) (t : ℝ) (r : Nat) :
    Measurable (prefixSelection n t r) := by
  exact measurable_pi_iff.mpr fun k =>
    ClockEventWord.word_getD_measurable t k.val (fallback n)

def enough (n : Nat) (t : ℝ) (r : Nat) : Set (ExponentialClocks.Sample (Site n)) :=
  {ω | r ≤ (ClockEventWord.word ω t).length}

theorem enough_measurable (n : Nat) (t : ℝ) (r : Nat) :
    MeasurableSet (enough n t r) := ClockEventWord.measurableSet_word_length_ge t r

theorem prefixSelection_injective (n : Nat) (t : ℝ) (r : Nat)
    (ω : ExponentialClocks.Sample (Site n)) (hω : ω ∈ enough n t r) :
    Function.Injective (prefixSelection n t r ω) := by
  intro a b hab
  have ha : a.val < (ClockEventWord.word ω t).length := lt_of_lt_of_le a.isLt hω
  have hb : b.val < (ClockEventWord.word ω t).length := lt_of_lt_of_le b.isLt hω
  have heq : (ClockEventWord.word ω t).get ⟨a.val, ha⟩ =
      (ClockEventWord.word ω t).get ⟨b.val, hb⟩ := by
    simpa only [prefixSelection, List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb,
      List.get_eq_getElem] using hab
  have hi := (ClockEventWord.word_nodup ω t).injective_get heq
  apply Fin.ext
  exact congrArg (fun k : Fin (ClockEventWord.word ω t).length => k.val) hi

def prefixMarks (n : Nat) (t : ℝ) (r : Nat) (z : Sample n) : Fin r → Bool :=
  FairMarks.selected (prefixSelection n t r) z

theorem prefixMarks_measurable (n : Nat) (t : ℝ) (r : Nat) :
    Measurable (prefixMarks n t r) :=
  FairMarks.selected_measurable _ (prefixSelection_measurable n t r)

/-- Every additional measurable clock event can be retained in the joint law.
Only the actual word length and its proven identity injectivity are used. -/
theorem prefixMarks_joint_measure (n : Nat) (t : ℝ) (r : Nat)
    (E : Set (ExponentialClocks.Sample (Site n))) (hE : MeasurableSet E)
    (B : Set (Fin r → Bool)) (hB : MeasurableSet B) :
    measure n {z | z.1 ∈ E ∩ enough n t r ∧ prefixMarks n t r z ∈ B} =
      ExponentialClocks.clockMeasure (Site n) (E ∩ enough n t r) *
        FairMarks.vectorMeasure r B := by
  exact FairMarks.selected_joint_measure (ExponentialClocks.clockMeasure (Site n))
    (prefixSelection n t r) (prefixSelection_measurable n t r) (E ∩ enough n t r)
    (hE.inter (enough_measurable n t r))
    (ae_of_all _ fun ω hω => prefixSelection_injective n t r ω hω.2) B hB

theorem prefixMarks_on_enough (n : Nat) (t : ℝ) (r : Nat)
    (B : Set (Fin r → Bool)) (hB : MeasurableSet B) :
    measure n {z | z.1 ∈ enough n t r ∧ prefixMarks n t r z ∈ B} =
      ExponentialClocks.clockMeasure (Site n) (enough n t r) *
        FairMarks.vectorMeasure r B := by
  simpa only [Set.univ_inter] using
    prefixMarks_joint_measure n t r Set.univ MeasurableSet.univ B hB

end MathResearchAnalysis.ClockWordMarks
