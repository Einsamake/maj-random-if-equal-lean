module

public import MathResearchAnalysis.MixedSquareModel
public import MathResearchAnalysis.MixedSquareCorners
public import MathResearchAnalysis.ClockExecutionLaw

set_option autoImplicit false

/-!
# Mixed-boundary endpoints under the actual clock and identity-mark law

The same actual finite rate-one clock word and original identity-indexed fair
mark field are used. No exclusion law, cross-size clock restriction or time
bound is inferred from this same-size comparison.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.MixedSquareClockLaw

open MeasureTheory

theorem execute_eq_of_marks_agree {n : Nat} (η ξ : SquareSpin.Event n → Bool)
    (w : List (SquareSpin.Event n)) (h : ∀ e ∈ w, η e = ξ e)
    (f : SquareSpin.Config n) :
    MixedSquareModel.execute η w f = MixedSquareModel.execute ξ w f := by
  induction w generalizing f with
  | nil => rfl
  | cons e w ih =>
    simp only [MixedSquareModel.execute_cons]
    have he : MixedSquareModel.updateEvent η e f = MixedSquareModel.updateEvent ξ e f := by
      simp only [MixedSquareModel.updateEvent,h e List.mem_cons_self]
    rw [he]
    exact ih (fun a ha => h a (List.mem_cons_of_mem _ ha)) _

/-- Fixed vector entries retain the original event identities. -/
def freshRun {n : Nat} (events : List (SquareSpin.Event n))
    (ξ : Fin events.length → Bool) (initial : SquareSpin.Config n) : SquareSpin.Config n :=
  MixedSquareModel.execute (ClockExecutionLaw.freshMarks events ξ) events.reverse initial

theorem freshRun_fixedVector {n : Nat} (events : List (SquareSpin.Event n))
    (η : SquareSpin.Event n → Bool) (initial : SquareSpin.Config n) :
    freshRun events (ClockExecutionLaw.fixedVector events η) initial =
      MixedSquareModel.execute η events.reverse initial := by
  apply execute_eq_of_marks_agree
  intro e he
  exact ClockExecutionLaw.freshMarks_fixedVector events η e (List.mem_reverse.mp he)

theorem freshRun_measurable {n : Nat} (events : List (SquareSpin.Event n))
    (initial : SquareSpin.Config n) :
    Measurable (fun ξ => freshRun events ξ initial) := measurable_of_countable _

theorem fixedRun_measurable {n : Nat} (events : List (SquareSpin.Event n))
    (initial : SquareSpin.Config n) :
    Measurable (fun η => MixedSquareModel.execute η events.reverse initial) := by
  have h := (freshRun_measurable events initial).comp
    (ClockExecutionLaw.fixedVector_measurable events)
  simpa only [Function.comp_def,freshRun_fixedVector] using h

/-- The actual total word has exactly the same fallback as the original law. -/
def endpoint (n : Nat) (t : Real) (initial : SquareSpin.Config n)
    (z : ClockWordMarks.Sample n) : SquareSpin.Config n :=
  MixedSquareModel.execute z.2 (ClockEventWord.word z.1 t).reverse initial

theorem endpoint_measurable (n : Nat) (t : Real) (initial : SquareSpin.Config n) :
    Measurable (endpoint n t initial) := by
  have hrun : Measurable (fun z : List (SquareSpin.Event n) ×
      FairMarks.Sample (SquareSpin.Event n) =>
      MixedSquareModel.execute z.2 z.1.reverse initial) :=
    measurable_from_prod_countable_right fun events => fixedRun_measurable events initial
  exact hrun.comp (((ClockEventWord.word_measurable t).comp measurable_fst).prodMk
    measurable_snd)

/-- The word comparison includes every original zero-boundary update. -/
theorem original_execute_le_mixed {n : Nat} (η : SquareSpin.Event n → Bool)
    (w : List (SquareSpin.Event n)) {f g : SquareSpin.Config n} (h : f ≤ g) :
    MarkedEventTrace.execute η w f ≤ MixedSquareModel.execute η w g := by
  induction w generalizing f g with
  | nil => exact h
  | cons e w ih =>
    change MarkedEventTrace.execute η w (SquareSpin.updateEvent η e f) ≤
      MixedSquareModel.execute η w (MixedSquareModel.updateEvent η e g)
    exact ih (MixedSquareModel.zeroBoundary_cellUpdate_le h e.1 (η e))

theorem original_endpoint_le_mixed (n : Nat) (t : Real)
    {f g : SquareSpin.Config n} (h : f ≤ g) (z : ClockWordMarks.Sample n) :
    ClockExecutionLaw.endpoint n t f z ≤ endpoint n t g z := by
  exact original_execute_le_mixed z.2 (ClockEventWord.word z.1 t).reverse h

theorem endpoint_mono (n : Nat) (t : Real) {f g : SquareSpin.Config n} (h : f ≤ g)
    (z : ClockWordMarks.Sample n) : endpoint n t f z ≤ endpoint n t g z :=
  MixedSquareModel.execute_mono z.2 _ h

/-- A true original-law probability comparison, still at the same finite side. -/
theorem original_nonzero_probability_le_mixed (n : Nat) (t : Real)
    {f g : SquareSpin.Config n} (h : f ≤ g) :
    (ClockWordMarks.measure n).real
      {z | ClockExecutionLaw.endpoint n t f z ≠ (fun _ => false)} ≤
    (ClockWordMarks.measure n).real {z | endpoint n t g z ≠ (fun _ => false)} := by
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro z hz hm
  have ho : ClockExecutionLaw.endpoint n t f z = fun _ => false :=
    le_antisymm (by simpa only [hm] using original_endpoint_le_mixed n t h z)
      (fun _ => Bool.false_le _)
  exact hz ho


/-- Every actual sample has the staircase shape at each fixed time. -/
theorem endpoint_monotone_shape (n : Nat) (t : Real) (initial : SquareSpin.Config n)
    (h : Monotone initial) (z : ClockWordMarks.Sample n) :
    Monotone (endpoint n t initial z) :=
  MixedSquareCorners.execute_monotone z.2 _ h

/-- No exceptional set or hidden stopping convention is needed for this
deterministic shape statement under the actual total-word execution. -/
theorem all_times_top_shape (n : Nat) (z : ClockWordMarks.Sample n) :
    ∀ t : Real, Monotone (endpoint n t (fun _ => true) z) := by
  intro t
  exact endpoint_monotone_shape n t _ (fun _ _ _ => le_refl _) z

end MathResearchAnalysis.MixedSquareClockLaw


