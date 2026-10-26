module
public import MathResearchAnalysis.ClockRestrictedExecution
public import MathResearchAnalysis.ClockEndpointSurvival
public import MathResearchAnalysis.MixedClearingProbability
public import Mathlib.Tactic
set_option autoImplicit false
/-! True cross-size endpoint comparison and a concrete original clock bound.
The injection, four-neighbour step relation and ordered retained word are all
proved; no coupling or block success probability is a final input. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.CrossSquareClockBound
open MeasureTheory Set
open ClippedSquareCoordinates (parameter)
open ClockSampleRestriction (projectSample)
open SquareInclusion (site Rel)
open MixedLocalClearing (localWhite)

theorem endpoint_rel {n m : Nat} (hnm : n≤m) (f : SquareSpin.Config n)
    (g : SquareSpin.Config m) (hrel : Rel hnm f g) (z : ClockWordMarks.Sample m)
    (t : Real) (hgood : ClockEventWord.Good z.1 t) :
    Rel hnm (ClockExecutionLaw.endpoint n t f (projectSample (site hnm) z))
      (MixedSquareClockLaw.endpoint m t g z) := by
  apply ClockRestrictedExecution.square_execute_rel hnm z.2
    (ClockEventWord.word (ClockSampleRestriction.projectClock (site hnm) z.1) t).reverse
    (ClockEventWord.word z.1 t).reverse
    (ClockWordRestriction.reverse_word_map_eq_filter (site hnm) (SquareInclusion.site_injective hnm)
      z.1 t hgood) f g hrel

theorem endpoint_rel_ae {n m : Nat} (hnm : n≤m) (f : SquareSpin.Config n)
    (g : SquareSpin.Config m) (hrel : Rel hnm f g) :
    ∀ᵐ z ∂ClockWordMarks.measure m, ∀ t : Real,
      Rel hnm (ClockExecutionLaw.endpoint n t f (projectSample (site hnm) z))
        (MixedSquareClockLaw.endpoint m t g z) := by
  filter_upwards [ClockEndpointSurvival.sample_good_ae m] with z hz
  exact fun t => endpoint_rel hnm f g hrel z t (hz t)

/-- The original smaller-square law is obtained by an actual sample map.
Its nonzero event is bounded by local failure in the larger mixed square. -/
theorem original_nonzero_probability_le_local_failure {n m : Nat} (hnm : n≤m)
    (t : Real) (f : SquareSpin.Config n) :
    ClockWordMarks.measure n {z | ClockExecutionLaw.endpoint n t f z≠(fun _ => false)} ≤
      ClockWordMarks.measure m {z | ¬localWhite (n+2)
        (MixedSquareClockLaw.endpoint m t (fun _ => true) z)} := by
  have hE : MeasurableSet {z | ClockExecutionLaw.endpoint n t f z≠(fun _ => false)} :=
    ((ClockExecutionLaw.endpoint_measurable n t f) (measurableSet_singleton _)).compl
  rw [←ClockSampleRestriction.projectSample_map (site hnm) (SquareInclusion.site_injective hnm),
    Measure.map_apply (ClockSampleRestriction.projectSample_measurable (site hnm)) hE]
  apply measure_mono_ae
  filter_upwards [endpoint_rel_ae hnm f (fun _ => true) (SquareInclusion.initial_rel_top hnm f)] with z hz
  intro hn hw
  apply hn
  funext v
  have hc := hz t v
  have hv := hw (site hnm v) v.1.isLt v.2.isLt
  rw [hv] at hc
  exact le_antisymm hc (Bool.false_le _)

/-- A concrete genuine-clock survival bound for the original side-N square.
The initial square is fully black; stochastic integrability and probability
inputs have already been discharged in the auxiliary local theorem. -/
theorem original_clock_survival_le_eighth (N : Nat) (hN : 16≤N) :
    ClockRecoveryComparison.clockProbability (N-2) (MixedHeatDecay.mixingTime (4*N)) ≤ (1/8 : Real) := by
  have hNs : N-2+2=N := by omega
  have hinc : N-2≤parameter (4*N) := by unfold parameter; omega
  have hs := MixedClearingProbability.auxiliary_side N (by omega)
  have hsr : (parameter (4*N)+2 : Real)=8*(N : Real)+1 := by exact_mod_cast hs
  have hNr : (16 : Real)≤N := by exact_mod_cast hN
  have hp := original_nonzero_probability_le_local_failure hinc (MixedHeatDecay.mixingTime (4*N))
    (SquarePWMeasure.topConfig (N-2))
  rw [hNs] at hp
  have haux := MixedClearingProbability.failure_probability_le (4*N) (fun _ => true)
    (show Monotone (fun _ : DropletClockLaw.Vertex (4*N) => true) from fun _ _ _ => le_rfl) N
    (by rw [hsr]; linarith)
  have hbound : ENNReal.ofReal (16/(parameter (4*N)+2 : Real))≤ENNReal.ofReal (1/8 : Real) := by
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ (MixedHeatDecay.side_pos (4*N))).mpr
    rw [hsr]
    linarith
  have hreal := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) ((hp.trans haux).trans hbound)
  simpa only [ClockRecoveryComparison.clockProbability,Measure.real,ENNReal.toReal_ofReal (by norm_num : (0:Real)≤1/8)] using hreal
end MathResearchAnalysis.CrossSquareClockBound
