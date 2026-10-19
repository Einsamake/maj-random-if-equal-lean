module
public import MathResearchAnalysis.DropletStoppedClockLaw
set_option autoImplicit false
/-! Compatibility of actual clock words at distinct physical times. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.ClockWordConsistency
open MeasureTheory
open ClockEventWord

theorem threshold_filter_prefix {α : Type*} (f : α → Real) (s : Real) {l : List α}
    (hl : l.Pairwise (fun a b => f a < f b)) :
    (l.filter (fun a => decide (f a ≤ s))).IsPrefix l := by
  classical
  induction l with
  | nil => exact ⟨[],rfl⟩
  | cons a l ih =>
    obtain ⟨ha,ht⟩ := List.pairwise_cons.mp hl
    by_cases h : f a ≤ s
    · obtain ⟨u,hu⟩ := ih ht
      refine ⟨u,?_⟩
      simpa [h] using congrArg (List.cons a) hu
    · have he : l.filter (fun b => decide (f b ≤ s)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro b hb
        simpa only [decide_eq_true_eq] using (not_le_of_gt ((lt_of_not_ge h).trans (ha b hb)))
      exact ⟨a::l,by simp [h,he]⟩

theorem good_mono {V : Type*} (ω : ExponentialClocks.Sample V) {s t : Real}
    (hst : s ≤ t) (ht : Good ω t) : Good ω s :=
  ⟨ht.1.subset (fun _ he => he.trans hst),ht.2⟩

theorem reverse_word_eq_filter {V : Type*} (ω : ExponentialClocks.Sample V) {s t : Real}
    (hst : s ≤ t) (ht : Good ω t) :
    (word ω s).reverse = (word ω t).reverse.filter (fun e => decide (eventTime ω e ≤ s)) := by
  classical
  have hs := good_mono ω hst ht
  have hmem : ∀ e, e ∈ (word ω s).reverse ↔
      e ∈ (word ω t).reverse.filter (fun e => decide (eventTime ω e ≤ s)) := by
    intro e
    simp only [List.mem_filter,List.mem_reverse,decide_eq_true_eq,word_mem_iff ω s hs,word_mem_iff ω t ht]
    change eventTime ω e ≤ s ↔ eventTime ω e ≤ t ∧ eventTime ω e ≤ s
    exact ⟨fun h => ⟨h.trans hst,h⟩,fun h => h.2⟩
  have hp := (List.perm_ext_iff_of_nodup (List.nodup_reverse.mpr (word_nodup ω s))
    ((List.nodup_reverse.mpr (word_nodup ω t)).filter _)).mpr hmem
  exact List.Perm.eq_of_pairwise
    (fun a b _ _ hab hba => False.elim ((not_lt_of_gt hab) hba))
    (word_reverse_strictly_increasing ω s)
    ((word_reverse_strictly_increasing ω t).sublist List.filter_sublist) hp

theorem reverse_word_prefix {V : Type*} (ω : ExponentialClocks.Sample V) {s t : Real}
    (hst : s ≤ t) (ht : Good ω t) : (word ω s).reverse.IsPrefix (word ω t).reverse := by
  rw [reverse_word_eq_filter ω hst ht]
  exact threshold_filter_prefix (eventTime ω) s (word_reverse_strictly_increasing ω t)

theorem markedEvents_prefix (L : Nat) (z : DropletClockLaw.Sample L) {s t : Real}
    (hst : s ≤ t) (ht : Good z.1 t) :
    (DropletClockLaw.markedEvents L (word z.1 s) z.2).IsPrefix
      (DropletClockLaw.markedEvents L (word z.1 t) z.2) := by
  simpa only [DropletClockLaw.markedEvents] using
    (reverse_word_prefix z.1 hst ht).map (fun e : DropletClockLaw.Event L => (ClippedSquareCoordinates.recenter L e.1,z.2 e))

theorem frozen_state_consistent (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (z : DropletClockLaw.Sample L) {s t : Real} (hst : s ≤ t) (ht : Good z.1 t) :
    ∃ suffix : List DropletModifiedWord.Event,
      DropletStoppedClockLaw.stateAt L D I S t z =
        DropletStoppedWord.stoppedWord D I (DropletStoppedClockLaw.stateAt L D I S s z) suffix := by
  obtain ⟨suffix,heq⟩ := markedEvents_prefix L z hst ht
  exact ⟨suffix,by rw [DropletStoppedClockLaw.stateAt,← heq,DropletStoppedWord.stoppedWord_append]; rfl⟩

theorem frozen_loss_persistent (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (z : DropletClockLaw.Sample L) {s t : Real} (hst : s ≤ t) (ht : Good z.1 t)
    (hmissing : ¬ I ⊆ DropletStoppedClockLaw.stateAt L D I S s z) :
    DropletStoppedClockLaw.stateAt L D I S t z = DropletStoppedClockLaw.stateAt L D I S s z := by
  obtain ⟨suffix,heq⟩ := frozen_state_consistent L D I S z hst ht
  rw [heq,DropletStoppedWord.stoppedWord_of_missing hmissing]

theorem reverse_word_prefix_ae {V : Type*} [Fintype V] :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ s t : Real, s ≤ t →
      (word ω s).reverse.IsPrefix (word ω t).reverse := by
  filter_upwards [ClockEventWord.good_ae (V := V)] with ω hω
  exact fun s t hst => reverse_word_prefix ω hst (hω t)

theorem marked_sample_good_ae (L : Nat) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      ∀ t : Real, Good z.1 t :=
  (Measure.quasiMeasurePreserving_fst (μ := ExponentialClocks.clockMeasure (DropletClockLaw.Vertex L))
    (ν := FairMarks.markMeasure (DropletClockLaw.Event L)) ).ae
    (ClockEventWord.good_ae (V := DropletClockLaw.Vertex L))

theorem frozen_state_consistent_ae (L : Nat) (D I S : Finset InfiniteGridModel.Site) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ s t : Real, s ≤ t →
      ∃ suffix : List DropletModifiedWord.Event,
        DropletStoppedClockLaw.stateAt L D I S t z =
          DropletStoppedWord.stoppedWord D I (DropletStoppedClockLaw.stateAt L D I S s z) suffix := by
  filter_upwards [marked_sample_good_ae L] with z hz
  exact fun s t hst => frozen_state_consistent L D I S z hst (hz t)

theorem frozen_loss_persistent_ae (L : Nat) (D I S : Finset InfiniteGridModel.Site) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ s t : Real, s ≤ t →
      (¬ I ⊆ DropletStoppedClockLaw.stateAt L D I S s z) →
      DropletStoppedClockLaw.stateAt L D I S t z = DropletStoppedClockLaw.stateAt L D I S s z := by
  filter_upwards [marked_sample_good_ae L] with z hz
  exact fun s t hst hm => frozen_loss_persistent L D I S z hst (hz t) hm

theorem word_zero_of_positive {V : Type*} (ω : ExponentialClocks.Sample V)
    (hp : ∀ e, 0 < eventTime ω e) : word ω 0 = [] := by
  by_cases hg : Good ω 0
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro e he
    exact (not_le_of_gt (hp e)) ((word_mem_iff ω 0 hg e).mp he)
  · exact word_eq_empty_of_not_good ω 0 hg

theorem stateAt_zero_of_positive (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (z : DropletClockLaw.Sample L) (hp : ∀ e, 0 < eventTime z.1 e) :
    DropletStoppedClockLaw.stateAt L D I S 0 z = S := by
  simp only [DropletStoppedClockLaw.stateAt,word_zero_of_positive z.1 hp,
    DropletClockLaw.markedEvents,List.reverse_nil,List.map_nil,DropletStoppedWord.stoppedWord_nil]

theorem stateAt_zero_ae (L : Nat) (D I S : Finset InfiniteGridModel.Site) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      DropletStoppedClockLaw.stateAt L D I S 0 z = S := by
  have hp := (Measure.quasiMeasurePreserving_fst (μ := ExponentialClocks.clockMeasure (DropletClockLaw.Vertex L))
    (ν := FairMarks.markMeasure (DropletClockLaw.Event L)) ).ae
    (ClockEventWord.eventTime_positive_ae (V := DropletClockLaw.Vertex L))
  filter_upwards [hp] with z hz
  exact stateAt_zero_of_positive L D I S z hz

theorem next_event_gap {V : Type*} (ω : ExponentialClocks.Sample V) (t : Real) (ht : Good ω (t+1)) :
    ∃ b : Real, t < b ∧ b ≤ t+1 ∧ ∀ e, eventTime ω e ≤ t+1 → t < eventTime ω e → b ≤ eventTime ω e := by
  classical
  let F := ht.1.toFinset.filter (fun e => t < eventTime ω e)
  by_cases hF : F.Nonempty
  · let T := F.image (eventTime ω)
    have hT : T.Nonempty := hF.image (eventTime ω)
    obtain ⟨e,he,heq⟩ := Finset.mem_image.mp (Finset.min'_mem T hT)
    have heF := Finset.mem_filter.mp he
    have het : eventTime ω e ≤ t+1 := (Set.Finite.mem_toFinset ht.1).mp heF.1
    refine ⟨T.min' hT,by simpa only [← heq] using heF.2,by simpa only [← heq] using het,?_⟩
    intro e heT het
    exact Finset.min'_le T (eventTime ω e) (Finset.mem_image.mpr
      ⟨e,Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset ht.1).mpr heT,het⟩,rfl⟩)
  · refine ⟨t+1,by linarith,le_rfl,?_⟩
    intro e heT het
    exact False.elim (hF ⟨e,Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset ht.1).mpr heT,het⟩⟩)

theorem word_eq_of_no_new_event {V : Type*} (ω : ExponentialClocks.Sample V) {s t : Real}
    (hst : s ≤ t) (ht : Good ω t) (hbound : ∀ e ∈ word ω t, eventTime ω e ≤ s) : word ω s = word ω t := by
  apply List.reverse_inj.mp
  rw [reverse_word_eq_filter ω hst ht]
  apply List.filter_eq_self.mpr
  intro e he
  exact decide_eq_true (hbound e (List.mem_reverse.mp he))

theorem word_right_locally_constant {V : Type*} (ω : ExponentialClocks.Sample V) (t : Real)
    (ht : Good ω (t+1)) : ∃ b : Real, t < b ∧ ∀ u, t ≤ u → u < b → word ω u = word ω t := by
  obtain ⟨b,htb,hb,hgap⟩ := next_event_gap ω t ht
  refine ⟨b,htb,?_⟩
  intro u htu hub
  have hu := good_mono ω (le_trans hub.le hb) ht
  apply (word_eq_of_no_new_event ω htu hu ?_).symm
  intro e he
  have heu : eventTime ω e ≤ u := (word_mem_iff ω u hu e).mp he
  by_contra het
  have hbe := hgap e (heu.trans (le_trans hub.le hb)) (lt_of_not_ge het)
  exact (not_le_of_gt hub) (hbe.trans heu)

theorem stateAt_right_locally_constant (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (z : DropletClockLaw.Sample L) (t : Real) (ht : Good z.1 (t+1)) :
    ∃ b : Real, t < b ∧ ∀ u, t ≤ u → u < b →
      DropletStoppedClockLaw.stateAt L D I S u z = DropletStoppedClockLaw.stateAt L D I S t z := by
  obtain ⟨b,htb,hb⟩ := word_right_locally_constant z.1 t ht
  exact ⟨b,htb,fun u htu hub => by simp only [DropletStoppedClockLaw.stateAt,hb u htu hub]⟩

theorem stateAt_right_locally_constant_ae (L : Nat) (D I S : Finset InfiniteGridModel.Site) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ t : Real,
      ∃ b : Real, t < b ∧ ∀ u, t ≤ u → u < b →
        DropletStoppedClockLaw.stateAt L D I S u z = DropletStoppedClockLaw.stateAt L D I S t z := by
  filter_upwards [marked_sample_good_ae L] with z hz
  exact fun t => stateAt_right_locally_constant L D I S z t (hz (t+1))

theorem frozen_loss_measure_mono (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    {s t : Real} (hst : s ≤ t) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | ¬ I ⊆ DropletStoppedClockLaw.stateAt L D I S s z} ≤
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | ¬ I ⊆ DropletStoppedClockLaw.stateAt L D I S t z} := by
  apply measure_mono_ae
  filter_upwards [marked_sample_good_ae L] with z hz
  intro hm
  change ¬ I ⊆ DropletStoppedClockLaw.stateAt L D I S s z at hm
  rw [frozen_loss_persistent L D I S z hst (hz t) hm]
  exact hm
end MathResearchAnalysis.ClockWordConsistency
