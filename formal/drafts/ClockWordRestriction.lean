module

public import MathResearchAnalysis.ClockSampleRestriction

set_option autoImplicit false

/-!
# Restricting the true bounded clock word to retained event identities

On a good large-square clock sample, mapping the smaller word back into the
large event space gives exactly the filtered large word in the same order.
Arrival indices are preserved. This is a common-almost-sure statement for all
real time bounds under the true original law, and makes no pointwise claim
about the exceptional empty-word fallback. No update coupling is asserted.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.ClockWordRestriction

open MeasureTheory Set
open SquareTasks (Vertex)
open ClockWordMarks (Event Sample)
open ClockSampleRestriction
open ClockEventWord (word eventTime Good)

/-- The Boolean filter tests membership in the retained event injection's range. -/
def retained {n m : Nat} (ι : Vertex n → Vertex m) (e : Event m) : Bool := by
  classical
  exact decide (e ∈ Set.range (eventι ι))

@[simp] theorem retained_eq_true_iff {n m : Nat} (ι : Vertex n → Vertex m) (e : Event m) :
    retained ι e = true ↔ e ∈ Set.range (eventι ι) := by
  classical
  simp [retained]

/-- Both words use their actual chronological construction. Only the big
sample's good condition is needed; it proves the smaller one is good too. -/
theorem word_map_eq_filter {n m : Nat} (ι : Vertex n → Vertex m) (hι : Function.Injective ι)
    (ω : ExponentialClocks.Sample (Vertex m)) (t : Real) (hbig : Good ω t) :
    (word (projectClock ι ω) t).map (eventι ι) = (word ω t).filter (retained ι) := by
  classical
  have hsmall := projected_good ι hι ω t hbig
  let r : Event m → Event m → Prop := fun a b => eventTime ω b < eventTime ω a
  let : Std.Irrefl r := ⟨fun _ => lt_irrefl _⟩
  let : Std.Antisymm r := ⟨fun _ _ hab hba => False.elim ((not_lt_of_gt hab) hba)⟩
  have hleft : ((word (projectClock ι ω) t).map (eventι ι)).Pairwise r :=
    List.pairwise_map.mpr (ClockEventWord.word_strictly_decreasing (projectClock ι ω) t)
  have hright : ((word ω t).filter (retained ι)).Pairwise r :=
    (ClockEventWord.word_strictly_decreasing ω t).sublist List.filter_sublist
  apply List.Pairwise.eq_of_mem_iff hleft hright
  intro e
  rw [List.mem_map,List.mem_filter,retained_eq_true_iff]
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨?_,⟨a,rfl⟩⟩
    apply (ClockEventWord.word_mem_iff ω t hbig (eventι ι a)).mpr
    exact (ClockEventWord.word_mem_iff (projectClock ι ω) t hsmall a).mp ha
  · rintro ⟨he,a,ha⟩
    refine ⟨a,?_,ha⟩
    apply (ClockEventWord.word_mem_iff (projectClock ι ω) t hsmall a).mpr
    change eventTime ω (eventι ι a) ≤ t
    rw [ha]
    exact (ClockEventWord.word_mem_iff ω t hbig e).mp he

/-- The same exact filtering relation holds in chronological execution order. -/
theorem reverse_word_map_eq_filter {n m : Nat} (ι : Vertex n → Vertex m) (hι : Function.Injective ι)
    (ω : ExponentialClocks.Sample (Vertex m)) (t : Real) (hbig : Good ω t) :
    (word (projectClock ι ω) t).reverse.map (eventι ι) =
      (word ω t).reverse.filter (retained ι) := by
  rw [List.map_reverse,List.filter_reverse,word_map_eq_filter ι hι ω t hbig]

/-- A single original-clock probability-one set covers every real time bound. -/
theorem word_map_eq_filter_ae {n m : Nat} (ι : Vertex n → Vertex m) (hι : Function.Injective ι) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure (Vertex m), ∀ t : Real,
      (word (projectClock ι ω) t).map (eventι ι) = (word ω t).filter (retained ι) := by
  filter_upwards [ClockEventWord.good_ae (V := Vertex m)] with ω hω
  exact fun t => word_map_eq_filter ι hι ω t (hω t)

/-- The original joint clock/mark law has the same common-time word relation;
retaining marks neither changes the selected event identities nor resamples them. -/
theorem marked_word_map_eq_filter_ae {n m : Nat} (ι : Vertex n → Vertex m) (hι : Function.Injective ι) :
    ∀ᵐ z ∂ClockWordMarks.measure m, ∀ t : Real,
      (word (projectSample ι z).1 t).map (eventι ι) = (word z.1 t).filter (retained ι) := by
  exact (Measure.quasiMeasurePreserving_fst
    (μ := ExponentialClocks.clockMeasure (Vertex m)) (ν := FairMarks.markMeasure (Event m))).ae
      (word_map_eq_filter_ae ι hι)

end MathResearchAnalysis.ClockWordRestriction
