module
public import MathResearchAnalysis.MixedRightCountHeat
public import MathResearchAnalysis.MixedLocalClearing
public import MathResearchAnalysis.CountLowerTail
public import Mathlib.Tactic
set_option autoImplicit false
/-! A genuine fixed-time local-clearing probability under the original marked
clock law. No cross-size law or original-process upper bound is assumed. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MixedClearingProbability
open MeasureTheory Set
open DropletClockLaw (Config Sample)
open ClippedSquareCoordinates (parameter)
open MixedRightCountMoments (count)
open MixedHeatDecay (mixingTime)
open MixedLocalClearing (localWhite)

theorem failure_measurable (L : Nat) (initial : Config L) (N : Nat) (t : Real) :
    MeasurableSet {z : Sample L |
      ¬localWhite N (MixedSquareClockLaw.endpoint (parameter L) t initial z)} := by
  exact (Set.to_countable {f : Config L | ¬localWhite N f}).measurableSet.preimage
    (MixedSquareClockLaw.endpoint_measurable (parameter L) t initial)

theorem failure_subset_count (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (N : Nat) (t : Real) :
    {z : Sample L | ¬localWhite N (MixedSquareClockLaw.endpoint (parameter L) t initial z)} ⊆
      {z | count L initial t z<(N : Real)} := by
  intro z hz
  by_contra hn
  exact hz (MixedLocalClearing.endpoint_localWhite_of_count_le L initial hinit t z N
    (le_of_not_gt hn))

/-- A process probability, with all mean, variance and integrability inputs
proved for the actual original joint law. -/
theorem failure_probability_le (L : Nat) (initial : Config L) (hinit : Monotone initial)
    (N : Nat) (hN : (N : Real)≤(parameter L+2 : Real)/8) :
    ClockWordMarks.measure (parameter L)
      {z | ¬localWhite N (MixedSquareClockLaw.endpoint (parameter L) (mixingTime L) initial z)} ≤
        ENNReal.ofReal (16/(parameter L+2 : Real)) := by
  apply (measure_mono (failure_subset_count L initial hinit N (mixingTime L))).trans
  exact CountLowerTail.lower_tail (ClockWordMarks.measure (parameter L))
    (count L initial (mixingTime L)) (MixedRightCountMoments.count_memLp_two L initial _)
    (parameter L+2 : Real) N (MixedHeatDecay.side_pos L) hN
    (MixedRightCountHeat.mean_at_mixingTime L initial hinit)
    (MixedRightCountMoments.standard_variance_le_side_quarter L initial hinit _
      (MixedHeatDecay.mixingTime_nonneg L))

theorem auxiliary_side (N : Nat) (hN : 1≤N) : parameter (4*N)+2=8*N+1 := by
  unfold parameter
  omega

/-- The auxiliary square has side 8N+1. At time 16(8N+1)² its southwest
side-N block is white with failure probability at most one quarter. This is
not yet a probability statement for the smaller original square. -/
theorem auxiliary_failure_quarter (N : Nat) (hN : 8≤N)
    (initial : Config (4*N)) (hinit : Monotone initial) :
    ClockWordMarks.measure (parameter (4*N))
      {z | ¬localWhite N (MixedSquareClockLaw.endpoint (parameter (4*N))
        (mixingTime (4*N)) initial z)} ≤ ENNReal.ofReal (1/4 : Real) := by
  have hs := auxiliary_side N (by omega)
  have hsr : (parameter (4*N)+2 : Real)=8*(N : Real)+1 := by exact_mod_cast hs
  have hNr : (8 : Real)≤N := by exact_mod_cast hN
  apply (failure_probability_le (4*N) initial hinit N (by rw [hsr]; linarith)).trans
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (MixedHeatDecay.side_pos (4*N))).mpr
  rw [hsr]
  linarith

theorem auxiliary_time_le_quadratic (N : Nat) (hN : 1≤N) :
    mixingTime (4*N) ≤ 1296*(N : Real)^2 := by
  have hs := auxiliary_side N hN
  have hsr : (parameter (4*N)+2 : Real)=8*(N : Real)+1 := by exact_mod_cast hs
  have hNr : (1 : Real)≤N := by exact_mod_cast hN
  unfold mixingTime
  rw [hsr]
  nlinarith [sq_nonneg ((N : Real)-1)]
end MathResearchAnalysis.MixedClearingProbability
