module
public import MathResearchAnalysis.ClockWordConsistency
set_option autoImplicit false
/-! Strict past event words. The left gap and single-event jump below are proved
from the finite actual word and its injective chronological times. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.StrictClockPrefix
open MeasureTheory
open ClockEventWord

/-- Actual identities strictly before `t`, retaining newest-first order. -/
def strictWord {V : Type*} (ω : ExponentialClocks.Sample V) (t : Real) : List (Event V) :=
  (word ω t).filter (fun e => decide (eventTime ω e < t))

theorem strictWord_mem_iff {V : Type*} (ω : ExponentialClocks.Sample V) (t : Real)
    (ht : Good ω t) (e : Event V) :
    e ∈ strictWord ω t ↔ eventTime ω e < t := by
  simp only [strictWord,List.mem_filter,decide_eq_true_eq,word_mem_iff ω t ht]
  change (eventTime ω e ≤ t ∧ eventTime ω e < t) ↔ eventTime ω e < t
  exact ⟨fun h => h.2,fun h => ⟨h.le,h⟩⟩

theorem strictWord_nodup {V : Type*} (ω : ExponentialClocks.Sample V) (t : Real) :
    (strictWord ω t).Nodup := (word_nodup ω t).filter _

theorem strictWord_strictly_decreasing {V : Type*}
    (ω : ExponentialClocks.Sample V) (t : Real) :
    (strictWord ω t).Pairwise (fun a b => eventTime ω b < eventTime ω a) :=
  (word_strictly_decreasing ω t).sublist List.filter_sublist

/-- There is an actual empty time gap just before each positive finite bound.
It is constructed as the greatest strict-past event time, with zero adjoined. -/
theorem word_left_locally_strict {V : Type*} (ω : ExponentialClocks.Sample V)
    (t : Real) (ht : Good ω t) (hpos : 0 < t) :
    ∃ a : Real, 0 ≤ a ∧ a < t ∧ ∀ u, a < u → u < t →
      word ω u = strictWord ω t := by
  classical
  let F : Finset Real := insert 0 ((strictWord ω t).toFinset.image (eventTime ω))
  have hF : F.Nonempty := ⟨0,Finset.mem_insert_self _ _⟩
  let a := F.max' hF
  have hzero : 0 ≤ a := Finset.le_max' F 0 (Finset.mem_insert_self _ _)
  have hat : a < t := by
    apply (Finset.max'_lt_iff _ _).mpr
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hpos
    · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hx
      exact (strictWord_mem_iff ω t ht e).mp (List.mem_toFinset.mp he)
  refine ⟨a,hzero,hat,?_⟩
  intro u hau hut
  have hu : Good ω u := ClockWordConsistency.good_mono ω hut.le ht
  apply (word_eq_iff ω u (strictWord ω t)).mpr
  right
  refine ⟨hu,strictWord_strictly_decreasing ω t,?_⟩
  intro e
  rw [strictWord_mem_iff ω t ht]
  constructor
  · intro het
    have hea : eventTime ω e ≤ a := Finset.le_max' F _
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨e,List.mem_toFinset.mpr ((strictWord_mem_iff ω t ht e).mpr het),rfl⟩))
    exact hea.trans hau.le
  · intro heu
    exact heu.trans_lt hut

/-- At an actual event time, the sole event at the endpoint is the newest head. -/
theorem word_at_event_eq_cons_strict {V : Type*}
    (ω : ExponentialClocks.Sample V) (e : Event V)
    (hGood : Good ω (eventTime ω e)) :
    word ω (eventTime ω e) = e :: strictWord ω (eventTime ω e) := by
  apply (word_eq_iff ω (eventTime ω e) _).mpr
  right
  refine ⟨hGood,?_,?_⟩
  · apply List.pairwise_cons.mpr
    exact ⟨fun f hf => (strictWord_mem_iff ω _ hGood f).mp hf,
      strictWord_strictly_decreasing ω _⟩
  · intro f
    rw [List.mem_cons,strictWord_mem_iff ω _ hGood]
    constructor
    · rintro (rfl | hf)
      · exact le_rfl
      · exact hf.le
    · intro hf
      rcases lt_or_eq_of_le hf with hlt | heq
      · exact Or.inr hlt
      · exact Or.inl (hGood.2 heq)

theorem strictWord_zero_of_positive {V : Type*}
    (ω : ExponentialClocks.Sample V) (hp : ∀ e, 0 < eventTime ω e) :
    strictWord ω 0 = [] := by
  simp only [strictWord,ClockWordConsistency.word_zero_of_positive ω hp,List.filter_nil]

end MathResearchAnalysis.StrictClockPrefix

#print axioms MathResearchAnalysis.StrictClockPrefix.strictWord
#print axioms MathResearchAnalysis.StrictClockPrefix.strictWord_mem_iff
#print axioms MathResearchAnalysis.StrictClockPrefix.strictWord_nodup
#print axioms MathResearchAnalysis.StrictClockPrefix.strictWord_strictly_decreasing
#print axioms MathResearchAnalysis.StrictClockPrefix.word_left_locally_strict
#print axioms MathResearchAnalysis.StrictClockPrefix.word_at_event_eq_cons_strict
#print axioms MathResearchAnalysis.StrictClockPrefix.strictWord_zero_of_positive
