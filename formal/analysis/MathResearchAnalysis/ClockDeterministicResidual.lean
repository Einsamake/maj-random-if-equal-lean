module

public import MathResearchAnalysis.ClockGapReset

set_option autoImplicit false

/-!
# Residual survival at a deterministic time in the actual common history

Each current gap is fixed before factorization. Resetting that gap preserves
all past observations on its candidate interval. The intervals partition
almost every true clock path; their disjoint sum proves history factorization.
No independent-increment, residual-law or strong-Markov premise is supplied.
-/

public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace MathResearchAnalysis.ClockDeterministicResidual

variable {V : Type*}

@[expose] def restEvent (v : V) (k : Nat) (r : ℝ)
    (E : Set (ExponentialClocks.Sample V)) : Set (RandomThresholdSurvival.RestSample V v k) :=
  {h | ClockGapReset.prior v k h ≤ r ∧ ClockGapReset.reset v k r h ∈ E}

theorem restEvent_measurable (v : V) (k : Nat) (r : ℝ)
    (E : Set (ExponentialClocks.Sample V))
    (hE : MeasurableSet[ArrivalFiltration.clockHistory V r] E) :
    MeasurableSet (restEvent v k r E) :=
  (measurableSet_le (ClockGapReset.prior_measurable v k) measurable_const).inter
    (((ArrivalFiltration.clockHistory V).le r E hE).preimage
      (ClockGapReset.reset_measurable v k r))

theorem candidate_iff_rest_gap (v : V) (k : Nat) (r : ℝ)
    (ω : ExponentialClocks.Sample V) :
    ClockCandidateIntervals.candidate v r k ω ↔
      ClockGapReset.prior v k (RandomThresholdSurvival.restCoordinates v k ω) ≤ r ∧
        ClockGapReset.cutoff v k r (RandomThresholdSurvival.restCoordinates v k ω) <
          ExponentialClocks.gap v k ω := by
  rw [ClockGapReset.prior_rest_eq_before]
  constructor
  · intro hc
    refine ⟨hc.1, ?_⟩
    have hp : ClockGapReset.prior v k (RandomThresholdSurvival.restCoordinates v k ω) ≤ r := by
      simpa only [ClockGapReset.prior_rest_eq_before] using hc.1
    rw [ClockGapReset.cutoff_eq_sub v k r _ hp, ClockGapReset.prior_rest_eq_before]
    have hg := ClockCandidateIntervals.gap_positive_of_candidate v r k ω hc
    have ha := hc.2
    rw [ClockCandidateIntervals.arrival_eq_before_add, max_eq_left hg.le] at ha
    linarith
  · rintro ⟨hp, hg⟩
    have hp' : ClockGapReset.prior v k (RandomThresholdSurvival.restCoordinates v k ω) ≤ r := by
      simpa only [ClockGapReset.prior_rest_eq_before] using hp
    have hpos : 0 < ExponentialClocks.gap v k ω :=
      (ClockGapReset.cutoff_nonnegative v k r _).trans_lt hg
    rw [ClockGapReset.cutoff_eq_sub v k r _ hp', ClockGapReset.prior_rest_eq_before] at hg
    refine ⟨hp, ?_⟩
    rw [ClockCandidateIntervals.arrival_eq_before_add, max_eq_left hpos.le]
    linarith

theorem candidate_history_base_eq (v : V) (k : Nat) (r : ℝ)
    (E : Set (ExponentialClocks.Sample V))
    (hE : MeasurableSet[ArrivalFiltration.clockHistory V r] E) :
    E ∩ {ω | ClockCandidateIntervals.candidate v r k ω} =
      {ω | RandomThresholdSurvival.restCoordinates v k ω ∈ restEvent v k r E ∧
        ClockGapReset.cutoff v k r (RandomThresholdSurvival.restCoordinates v k ω) <
          ExponentialClocks.gap v k ω} := by
  ext ω
  change (ω ∈ E ∧ ClockCandidateIntervals.candidate v r k ω) ↔
    ((ClockGapReset.prior v k (RandomThresholdSurvival.restCoordinates v k ω) ≤ r ∧
      ClockGapReset.reset v k r (RandomThresholdSurvival.restCoordinates v k ω) ∈ E) ∧ _)
  constructor
  · rintro ⟨hωE, hc⟩
    have h := (candidate_iff_rest_gap v k r ω).mp hc
    exact ⟨⟨h.1, (ClockGapReset.reset_history_event_iff v k r ω hc E hE).mp hωE⟩, h.2⟩
  · rintro ⟨⟨hp, hreset⟩, hg⟩
    have hc := (candidate_iff_rest_gap v k r ω).mpr ⟨hp, hg⟩
    exact ⟨(ClockGapReset.reset_history_event_iff v k r ω hc E hE).mpr hreset, hc⟩

theorem candidate_history_survival_eq (v : V) (k : Nat) (r t : ℝ) (ht : 0 ≤ t)
    (E : Set (ExponentialClocks.Sample V))
    (hE : MeasurableSet[ArrivalFiltration.clockHistory V r] E) :
    E ∩ {ω | ClockCandidateIntervals.candidate v r k ω ∧
      r + t - ClockCandidateIntervals.before v k ω < ExponentialClocks.gap v k ω} =
      {ω | RandomThresholdSurvival.restCoordinates v k ω ∈ restEvent v k r E ∧
        ClockGapReset.cutoff v k r (RandomThresholdSurvival.restCoordinates v k ω) + t <
          ExponentialClocks.gap v k ω} := by
  ext ω
  change (ω ∈ E ∧ ClockCandidateIntervals.candidate v r k ω ∧
    r + t - ClockCandidateIntervals.before v k ω < ExponentialClocks.gap v k ω) ↔
    ((ClockGapReset.prior v k (RandomThresholdSurvival.restCoordinates v k ω) ≤ r ∧
      ClockGapReset.reset v k r (RandomThresholdSurvival.restCoordinates v k ω) ∈ E) ∧ _)
  constructor
  · rintro ⟨hωE, hc, hg⟩
    have hp := ((candidate_iff_rest_gap v k r ω).mp hc).1
    refine ⟨⟨hp, (ClockGapReset.reset_history_event_iff v k r ω hc E hE).mp hωE⟩, ?_⟩
    rw [ClockGapReset.cutoff_eq_sub v k r _ hp, ClockGapReset.prior_rest_eq_before]
    linarith
  · rintro ⟨⟨hp, hreset⟩, hg⟩
    have hg0 : ClockGapReset.cutoff v k r (RandomThresholdSurvival.restCoordinates v k ω) <
        ExponentialClocks.gap v k ω := by linarith
    have hc := (candidate_iff_rest_gap v k r ω).mpr ⟨hp, hg0⟩
    refine ⟨(ClockGapReset.reset_history_event_iff v k r ω hc E hE).mpr hreset, hc, ?_⟩
    rw [ClockGapReset.cutoff_eq_sub v k r _ hp, ClockGapReset.prior_rest_eq_before] at hg
    linarith

theorem candidate_history_factorization (v : V) (k : Nat) (r t : ℝ) (ht : 0 ≤ t)
    (E : Set (ExponentialClocks.Sample V))
    (hE : MeasurableSet[ArrivalFiltration.clockHistory V r] E) :
    ExponentialClocks.clockMeasure V (E ∩ {ω | ClockCandidateIntervals.candidate v r k ω ∧
      r + t - ClockCandidateIntervals.before v k ω < ExponentialClocks.gap v k ω}) =
      ENNReal.ofReal (Real.exp (-t)) *
        ExponentialClocks.clockMeasure V (E ∩ {ω | ClockCandidateIntervals.candidate v r k ω}) := by
  rw [candidate_history_survival_eq v k r t ht E hE, candidate_history_base_eq v k r E hE]
  exact RandomThresholdSurvival.actual_gap_survival_factorization v k
    (ClockGapReset.cutoff v k r) (ClockGapReset.cutoff_measurable v k r)
    (ClockGapReset.cutoff_nonnegative v k r) (restEvent v k r E)
    (restEvent_measurable v k r E hE) ht

theorem candidate_inter_measure_tsum [Countable V] (v : V) (r : ℝ) (hr : 0 ≤ r)
    (E : Set (ExponentialClocks.Sample V)) (hE : MeasurableSet E) :
    (∑' k : Nat, ExponentialClocks.clockMeasure V
      (E ∩ {ω | ClockCandidateIntervals.candidate v r k ω})) = ExponentialClocks.clockMeasure V E := by
  have hcover : (E ∩ ⋃ k : Nat, {ω | ClockCandidateIntervals.candidate v r k ω})
      =ᵐ[ExponentialClocks.clockMeasure V] E := by
    filter_upwards [ClockCandidateIntervals.candidate_iUnion_ae_univ v r hr] with ω hω
    simp only [Set.mem_inter_iff, hω, Set.mem_univ, and_true]
  calc
    _ = ExponentialClocks.clockMeasure V
        (⋃ k : Nat, E ∩ {ω | ClockCandidateIntervals.candidate v r k ω}) := by
      symm
      apply measure_iUnion
      · intro i j hij
        apply Set.disjoint_left.mpr
        intro ω hi hj
        exact hij (ClockCandidateIntervals.candidate_unique v r i j ω hi.2 hj.2)
      · exact fun k => hE.inter (ClockCandidateIntervals.candidate_measurableSet v r k)
    _ = _ := by rw [← Set.inter_iUnion, measure_congr hcover]

/-- The true shared-history residual factorization at every nonnegative deterministic time. -/
theorem clock_next_joint_survival [Countable V] (v : V) (r t : ℝ)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (E : Set (ExponentialClocks.Sample V))
    (hE : MeasurableSet[ArrivalFiltration.clockHistory V r] E) :
    ExponentialClocks.clockMeasure V (E ∩ {ω | ((r + t : ℝ) : WithTop ℝ) <
      NextRing.extendedNextRing (ArrivalFiltration.chronologicalArrival v) (fun _ => r) ω}) =
      ENNReal.ofReal (Real.exp (-t)) * ExponentialClocks.clockMeasure V E := by
  rw [ClockCandidateIntervals.next_survival_inter_measure_tsum v r t hr E
    ((ArrivalFiltration.clockHistory V).le r E hE)]
  simp_rw [candidate_history_factorization v _ r t ht E hE]
  rw [ENNReal.tsum_mul_left, candidate_inter_measure_tsum v r hr E
    ((ArrivalFiltration.clockHistory V).le r E hE)]

end MathResearchAnalysis.ClockDeterministicResidual
