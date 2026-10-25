module
public import MathResearchAnalysis.FiniteMachinePreState
public import MathResearchAnalysis.MachineTraceTelescope
public import MathResearchAnalysis.MachineEventScores
set_option autoImplicit false
/-! Finite-state physical-time Dynkin under the actual original joint clock
and identity-mark law. Bounded predictable increments are constructed from
the genuine strict past; their real event telescope and integrability are
proved before signed compensation or exchange of integrals is used. No
moment equation, generator estimate or recovery bound is a premise. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.MachineClockDynkin
open MeasureTheory
open DropletClockLaw (Sample Event Vertex)
variable {A : Type*}
variable (observable : A → Real)

def bound [Fintype A] : Real := ∑ a : A, ‖observable a‖

theorem value_norm_le [Fintype A] (a : A) : ‖observable a‖ ≤ bound observable := by
  classical
  exact Finset.single_le_sum (fun b _ => norm_nonneg (observable b)) (Finset.mem_univ a)

def increment (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) (v : Vertex L) (b : Bool)
    (p : NNReal × Sample L) : Real :=
  observable (step v b (FiniteMachinePreState.beforeState L step initial p.1 p.2)) -
  observable (FiniteMachinePreState.beforeState L step initial p.1 p.2)

theorem increment_stronglyMeasurable [Fintype A] (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (v : Vertex L) (b : Bool) :
    StronglyMeasurable[(RationalProtectedExit.nnHistory L).predictable]
      (increment observable L step initial v b) :=
  (FiniteMachinePreState.observable_measurable L step initial (fun U : A =>
    observable (step v b U) - observable U)).stronglyMeasurable

theorem increment_norm_le [Fintype A] (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (v : Vertex L) (b : Bool) (p : NNReal × Sample L) :
    ‖increment observable L step initial v b p‖ ≤ 2 * bound observable := by
  unfold increment
  exact (norm_sub_le _ _).trans (by
    have h1 := value_norm_le observable (step v b (FiniteMachinePreState.beforeState L step initial p.1 p.2))
    have h2 := value_norm_le observable (FiniteMachinePreState.beforeState L step initial p.1 p.2)
    linarith)

theorem increment_eq_horizon_filter (L : Nat) (step : Vertex L → Bool → A → A)
    (initial : A) (z : Sample L) (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e)
    (T : Real) (e : Event L) (he : e ∈ ClockEventWord.word z.1 T) :
    increment observable L step initial e.1 (z.2 e)
      ((ClockEventWord.eventTime z.1 e).toNNReal,z) =
      observable (step e.1 (z.2 e) (EventTrace.execute
        (fun f : Event L => step f.1 (z.2 f))
        ((ClockEventWord.word z.1 T).filter
          (fun f => decide (ClockEventWord.eventTime z.1 f < ClockEventWord.eventTime z.1 e))).reverse initial)) -
      observable (EventTrace.execute (fun f : Event L => step f.1 (z.2 f))
        ((ClockEventWord.word z.1 T).filter
          (fun f => decide (ClockEventWord.eventTime z.1 f < ClockEventWord.eventTime z.1 e))).reverse initial) := by
  unfold increment
  rw [FiniteMachinePreState.beforeState_eq_strictStateAt L step initial z hg hp,
    Real.coe_toNNReal _ (hp e).le]
  unfold FiniteMachinePreState.strictStateAt
  rw [ActualAreaTelescope.strictWord_eq_filter_horizon z.1
    ((ClockEventWord.word_mem_iff z.1 T (hg T) e).mp he) (hg T)]

theorem observable_telescope (L : Nat) (step : Vertex L → Bool → A → A)
    (initial : A) (z : Sample L) (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) (T : NNReal) :
    observable (FiniteObservedClockState.endpoint L step initial (T : Real) z) - observable initial =
    ((ClockEventWord.word z.1 (T : Real)).map (fun e =>
      increment observable L step initial e.1 (z.2 e)
        ((ClockEventWord.eventTime z.1 e).toNNReal,z))).sum := by
  have h := MachineTraceTelescope.telescope (ClockEventWord.eventTime z.1)
    (fun e : Event L => step e.1 (z.2 e)) observable initial
    (ClockEventWord.word z.1 (T : Real))
    (ClockEventWord.word_strictly_decreasing z.1 (T : Real))
  change _ = _ at h
  unfold FiniteObservedClockState.endpoint
  rw [h]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  exact (increment_eq_horizon_filter observable L step initial z hg hp (T : Real) e he).symm

/-- One common full-probability set supports the signed identity at all horizons. -/
theorem observable_telescope_all_times_ae (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ T : NNReal,
    observable (FiniteObservedClockState.endpoint L step initial (T : Real) z) -
      observable initial =
    ((ClockEventWord.word z.1 (T : Real)).map (fun e =>
      increment observable L step initial e.1 (z.2 e)
        ((ClockEventWord.eventTime z.1 e).toNNReal,z))).sum := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L,
    ActualPreState.marked_all_events_positive_ae L] with z hg hp
  exact fun T => observable_telescope observable L step initial z hg hp T
theorem observable_telescope_finset (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) (T : NNReal) :
    observable (FiniteObservedClockState.endpoint L step initial (T : Real) z) -
      observable initial =
    ∑ e ∈ (ClockEventWord.word z.1 (T : Real)).toFinset,
      increment observable L step initial e.1 (z.2 e)
        ((ClockEventWord.eventTime z.1 e).toNNReal,z) := by
  rw [observable_telescope observable L step initial z hg hp T,
    ActualAreaTelescope.sum_map_eq_sum_toFinset _ (ClockEventWord.word_nodup z.1 (T : Real))]

/-- All horizons share the same exceptional null set; the finite identity
sum therefore remains valid when a later argument observes a random horizon. -/
theorem observable_telescope_finset_all_times_ae (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ T : NNReal,
    observable (FiniteObservedClockState.endpoint L step initial (T : Real) z) -
      observable initial =
    ∑ e ∈ (ClockEventWord.word z.1 (T : Real)).toFinset,
      increment observable L step initial e.1 (z.2 e)
        ((ClockEventWord.eventTime z.1 e).toNNReal,z) := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L,
    ActualPreState.marked_all_events_positive_ae L] with z hg hp
  exact fun T => observable_telescope_finset observable L step initial z hg hp T

/-- The actual full area change is exactly the sum of the site's true marked
pathwise contributions, at the actual physical horizon. -/
theorem observable_eq_pathSums (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) (T : NNReal) :
    observable (FiniteObservedClockState.endpoint L step initial (T : Real) z) -
      observable initial =
    ∑ v : Vertex L, ∑ b : Bool, RealPredictableCompensation.pathSum L v b T
      (increment observable L step initial v b) z :=
  (observable_telescope_finset observable L step initial z hg hp T).trans
    (MachineEventScores.sum_pathSums_eq_word_sum L
      (increment observable L step initial) T z (hg _) hp).symm

/-- One full-probability set works at every horizon, with the original sample
law. No separate exceptional set is chosen for a random observation time. -/
theorem observable_eq_pathSums_all_times_ae (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ T : NNReal,
    observable (FiniteObservedClockState.endpoint L step initial (T : Real) z) -
      observable initial =
    ∑ v : Vertex L, ∑ b : Bool, RealPredictableCompensation.pathSum L v b T
      (increment observable L step initial v b) z := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L,
    ActualPreState.marked_all_events_positive_ae L] with z hg hp
  exact fun T => observable_eq_pathSums observable L step initial z hg hp T
theorem marked_pathSum_integrable [Fintype A] (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (v : Vertex L) (b : Bool) (T : NNReal) :
    Integrable (RealPredictableCompensation.pathSum L v b T
      (increment observable L step initial v b))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  RealPredictableCompensation.bounded_predictable_integrable L v b T
    (increment observable L step initial v b)
    (increment_stronglyMeasurable observable L step initial v b)
    (2 * bound observable) (increment_norm_le observable L step initial v b)

theorem total_pathSum_integrable [Fintype A] (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) (T : NNReal) :
    Integrable (fun z : Sample L => ∑ v : Vertex L, ∑ b : Bool,
      RealPredictableCompensation.pathSum L v b T
        (increment observable L step initial v b) z)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  exact integrable_finsetSum _ fun v _ => integrable_finsetSum _ fun b _ =>
    marked_pathSum_integrable observable L step initial v b T

theorem observable_change_integrable [Fintype A] (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) (T : NNReal) :
    Integrable (fun z : Sample L =>
      observable (FiniteObservedClockState.endpoint L step initial (T : Real) z) -
        observable initial)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  apply (total_pathSum_integrable observable L step initial T).congr
  filter_upwards [observable_eq_pathSums_all_times_ae observable L step initial] with z hz
  exact (hz T).symm

theorem observable_integrable [Fintype A] (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) (T : NNReal) :
    Integrable (fun z : Sample L =>
      observable (FiniteObservedClockState.endpoint L step initial (T : Real) z))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  convert (observable_change_integrable observable L step initial T).add
    (integrable_const (observable initial)) using 1
  ext z
  simp only [Pi.add_apply]
  ring

/-- Exact physical signed compensation, with integrability established first.
Each half rate belongs to one specified fair mark at one original site. -/
theorem observable_change_dynkin [Fintype A] (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) (T : NNReal) :
    (∫ z : Sample L,
      observable (FiniteObservedClockState.endpoint L step initial (T : Real) z) -
        observable initial
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    ∑ v : Vertex L, ∑ b : Bool, (1 / 2 : Real) * ∫ u : Real in Set.Ioc 0 (T : Real),
      ∫ z : Sample L, increment observable L step initial v b (u.toNNReal,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  calc
    _ = ∫ z : Sample L, ∑ v : Vertex L, ∑ b : Bool,
        RealPredictableCompensation.pathSum L v b T
          (increment observable L step initial v b) z
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
      apply integral_congr_ae
      filter_upwards [observable_eq_pathSums_all_times_ae observable L step initial] with z hz
      exact hz T
    _ = _ := by
      rw [integral_finsetSum _ (fun v _ =>
        integrable_finsetSum _ (fun b _ => marked_pathSum_integrable observable L step initial v b T))]
      apply Finset.sum_congr rfl
      intro v _
      rw [integral_finsetSum _ (fun b _ => marked_pathSum_integrable observable L step initial v b T)]
      apply Finset.sum_congr rfl
      intro b _
      exact RealPredictableCompensation.bounded_predictable_integral_eq_time L v b T
        (increment observable L step initial v b)
        (increment_stronglyMeasurable observable L step initial v b)
        (2 * bound observable) (increment_norm_le observable L step initial v b)

theorem time_mean_increment_integrable [Fintype A] (L : Nat) (step : Vertex L → Bool → A → A) (initial : A)
    (v : Vertex L) (b : Bool) (T : NNReal) :
    Integrable (fun u : Real => ∫ z : Sample L,
      increment observable L step initial v b (u.toNNReal,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L))
      ((volume : Measure Real).restrict (Set.Ioc 0 (T : Real))) :=
  RealPredictableCompensation.time_mean_integrable L T
    (increment observable L step initial v b)
    ((increment_stronglyMeasurable observable L step initial v b).mono
      (PredictableClockSigma.predictable_le_ambient L))
    (2 * bound observable) (increment_norm_le observable L step initial v b)

theorem observable_change_dynkin_single_integral [Fintype A] (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) (T : NNReal) :
    (∫ z : Sample L,
      observable (FiniteObservedClockState.endpoint L step initial (T : Real) z) -
        observable initial
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    (1 / 2 : Real) * ∫ u : Real in Set.Ioc 0 (T : Real), ∑ v : Vertex L, ∑ b : Bool,
      ∫ z : Sample L, increment observable L step initial v b (u.toNNReal,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  rw [observable_change_dynkin observable]
  have hsum : (∫ u : Real in Set.Ioc 0 (T : Real), ∑ v : Vertex L, ∑ b : Bool,
      ∫ z : Sample L, increment observable L step initial v b (u.toNNReal,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      ∑ v : Vertex L, ∑ b : Bool, ∫ u : Real in Set.Ioc 0 (T : Real),
        ∫ z : Sample L, increment observable L step initial v b (u.toNNReal,z)
          ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
    rw [integral_finsetSum _ (fun v _ => integrable_finsetSum _
      (fun b _ => time_mean_increment_integrable observable L step initial v b T))]
    apply Finset.sum_congr rfl
    intro v _
    exact integral_finsetSum _ (fun b _ => time_mean_increment_integrable observable L step initial v b T)
  rw [hsum]
  simp only [Finset.mul_sum]

theorem expected_observable_dynkin [Fintype A] (L : Nat) (step : Vertex L → Bool → A → A) (initial : A) (T : NNReal) :
    (∫ z : Sample L, observable (FiniteObservedClockState.endpoint L step initial (T : Real) z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    observable initial +
      ∑ v : Vertex L, ∑ b : Bool, (1 / 2 : Real) * ∫ u : Real in Set.Ioc 0 (T : Real),
        ∫ z : Sample L, increment observable L step initial v b (u.toNNReal,z)
          ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  have h := observable_change_dynkin observable L step initial T
  rw [integral_sub (observable_integrable observable L step initial T) (integrable_const _)] at h
  simpa only [integral_const,probReal_univ,one_smul] using (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
end MathResearchAnalysis.MachineClockDynkin
