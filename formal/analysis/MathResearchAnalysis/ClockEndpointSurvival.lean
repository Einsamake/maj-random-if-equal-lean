module
public import MathResearchAnalysis.ClockWordConsistency
public import MathResearchAnalysis.ClockExecutionLaw
public import MathResearchAnalysis.ClockRecoveryComparison
public import Mathlib.Tactic
set_option autoImplicit false
/-! True zero-boundary endpoint survival decreases with physical clock time.
The almost-sure prefix relation is used; the exceptional total-word fallback
is not asserted to have a monotone trajectory. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.ClockEndpointSurvival
open MeasureTheory

theorem execute_zero (n : Nat) (η : SquareSpin.Event n → Bool)
    (w : List (SquareSpin.Event n)) :
    MarkedEventTrace.execute η w (fun _ => false) = (fun _ => false) := by
  induction w with
  | nil => rfl
  | cons e w ih =>
    change MarkedEventTrace.execute η w (SquareSpin.updateEvent η e (fun _ => false)) = _
    simpa only [SquareSpin.updateEvent,SquareSpin.cellUpdate_zero] using ih

theorem sample_good_ae (n : Nat) :
    ∀ᵐ z ∂ClockWordMarks.measure n, ∀ t : Real, ClockEventWord.Good z.1 t :=
  (Measure.quasiMeasurePreserving_fst
    (μ := ExponentialClocks.clockMeasure (SquareTasks.Vertex n))
    (ν := FairMarks.markMeasure (SquareSpin.Event n))).ae
      (ClockEventWord.good_ae (V := SquareTasks.Vertex n))

theorem zero_persists (n : Nat) (initial : SquareSpin.Config n)
    (z : ClockWordMarks.Sample n) (s t : Real) (hst : s≤t)
    (hgood : ClockEventWord.Good z.1 t)
    (hz : ClockExecutionLaw.endpoint n s initial z=(fun _ => false)) :
    ClockExecutionLaw.endpoint n t initial z=(fun _ => false) := by
  obtain ⟨suffix,hw⟩ := ClockWordConsistency.reverse_word_prefix z.1 hst hgood
  simp only [ClockExecutionLaw.endpoint,MarkedEventTrace.executeClockWord,MarkedEventTrace.execute] at hz ⊢
  rw [←hw,EventTrace.execute_append,hz]
  exact execute_zero n z.2 suffix

/-- Original-law survival, unlike the mixed auxiliary local event, is monotone. -/
theorem clockProbability_antitone (n : Nat) :
    Antitone (ClockRecoveryComparison.clockProbability n) := by
  intro s t hst
  have hp : ClockWordMarks.measure n
      {z | ClockExecutionLaw.endpoint n t (SquarePWMeasure.topConfig n) z≠(fun _ => false)} ≤
      ClockWordMarks.measure n
      {z | ClockExecutionLaw.endpoint n s (SquarePWMeasure.topConfig n) z≠(fun _ => false)} := by
    apply measure_mono_ae
    filter_upwards [sample_good_ae n] with z hz
    intro hn hs
    exact hn (zero_persists n (SquarePWMeasure.topConfig n) z s t hst (hz t) hs)
  exact ENNReal.toReal_mono (measure_ne_top _ _) hp
end MathResearchAnalysis.ClockEndpointSurvival
