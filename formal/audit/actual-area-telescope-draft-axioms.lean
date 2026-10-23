module
public import MathResearchAnalysis.PredictableAreaContribution
set_option autoImplicit false
/-! A pathwise, signed area telescope for the genuine finite marked clock word.
The before state is identified at every actual event on one common good sample.
No expectation, compensation, geometric drift or finite recovery is assumed. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.ActualAreaTelescope
open MeasureTheory
open DropletClockLaw (Sample Event)
open InfiniteGridModel (Site)

/-- Filtering the genuine horizon word at a strictly earlier threshold gives
exactly the genuine strict-past word, in the same newest-first order. -/
theorem strictWord_eq_filter_horizon {V : Type*} (ω : ExponentialClocks.Sample V)
    {s t : Real} (hst : s ≤ t) (ht : ClockEventWord.Good ω t) :
    StrictClockPrefix.strictWord ω s =
      (ClockEventWord.word ω t).filter (fun e => decide (ClockEventWord.eventTime ω e < s)) := by
  classical
  let r : ClockEventWord.Event V → ClockEventWord.Event V → Prop :=
    fun a b => ClockEventWord.eventTime ω b < ClockEventWord.eventTime ω a
  let : Std.Irrefl r := ⟨fun _ => lt_irrefl _⟩
  let : Std.Antisymm r := ⟨fun _ _ hab hba => False.elim ((not_lt_of_ge hab.le) hba)⟩
  apply List.Pairwise.eq_of_mem_iff (r := r)
    (StrictClockPrefix.strictWord_strictly_decreasing ω s)
    ((ClockEventWord.word_strictly_decreasing ω t).sublist List.filter_sublist)
  intro e
  rw [StrictClockPrefix.strictWord_mem_iff ω s (ClockWordConsistency.good_mono ω hst ht),
    List.mem_filter,ClockEventWord.word_mem_iff ω t ht,decide_eq_true_eq]
  change ClockEventWord.eventTime ω e < s ↔
    ClockEventWord.eventTime ω e ≤ t ∧ ClockEventWord.eventTime ω e < s
  exact ⟨fun h => ⟨h.le.trans hst,h⟩,fun h => h.2⟩

/-- An arbitrary strictly ordered finite word telescopes even if the step is
already frozen. The strict-past filter is part of the expression, not a premise. -/
theorem stoppedWord_area_telescope {α : Type*} (time : α → Real)
    (mark : α → DropletModifiedWord.Event) (D I S : Finset Site)
    (w : List α) (hw : w.Pairwise (fun a b => time b < time a)) :
    ((D \ DropletStoppedWord.stoppedWord D I S (w.reverse.map mark)).card : Real) -
      ((D \ S).card : Real) =
    (w.map (fun e =>
      ((D \ DropletStoppedWord.stoppedStep D I
        (DropletStoppedWord.stoppedWord D I S
          ((w.filter (fun f => decide (time f < time e))).reverse.map mark)) (mark e)).card : Real) -
      ((D \ DropletStoppedWord.stoppedWord D I S
        ((w.filter (fun f => decide (time f < time e))).reverse.map mark)).card : Real))).sum := by
  classical
  induction w with
  | nil => simp
  | cons e w ih =>
    obtain ⟨he,hw⟩ := List.pairwise_cons.mp hw
    have hfilter : (e :: w).filter (fun f => decide (time f < time e)) = w := by
      simp only [List.filter_cons,lt_self_iff_false,decide_false,Bool.false_eq_true,
        ↓reduceIte]
      exact List.filter_eq_self.mpr (fun f hf => decide_eq_true (he f hf))
    have htail : w.map (fun f =>
        ((D \ DropletStoppedWord.stoppedStep D I
          (DropletStoppedWord.stoppedWord D I S
            (((e :: w).filter (fun g => decide (time g < time f))).reverse.map mark)) (mark f)).card : Real) -
        ((D \ DropletStoppedWord.stoppedWord D I S
          (((e :: w).filter (fun g => decide (time g < time f))).reverse.map mark)).card : Real)) =
      w.map (fun f =>
        ((D \ DropletStoppedWord.stoppedStep D I
          (DropletStoppedWord.stoppedWord D I S
            ((w.filter (fun g => decide (time g < time f))).reverse.map mark)) (mark f)).card : Real) -
        ((D \ DropletStoppedWord.stoppedWord D I S
          ((w.filter (fun g => decide (time g < time f))).reverse.map mark)).card : Real)) := by
      apply List.map_congr_left
      intro f hf
      have hnot : ¬ time e < time f := not_lt_of_gt (he f hf)
      simp only [List.filter_cons,decide_eq_false hnot,Bool.false_eq_true,↓reduceIte]
    rw [List.reverse_cons,List.map_append,List.map_singleton,
      DropletStoppedWord.stoppedWord_append,DropletStoppedWord.stoppedWord_cons,
      DropletStoppedWord.stoppedWord_nil,List.map_cons,List.sum_cons,hfilter,htail,
      ← ih hw]
    ring

/-- The predictable increment at each real event uses precisely that event's
identity-indexed mark and the genuine strict-past horizon prefix. -/
theorem increment_eq_horizon_filter (L : Nat) (D I S : Finset Site)
    (z : Sample L) (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e)
    (T : Real) (e : Event L) (he : e ∈ ClockEventWord.word z.1 T) :
    PredictableAreaContribution.increment L D I S e.1 (z.2 e)
      ((ClockEventWord.eventTime z.1 e).toNNReal,z) =
      ((D \ DropletStoppedWord.stoppedStep D I
        (DropletStoppedWord.stoppedWord D I S
          (((ClockEventWord.word z.1 T).filter
            (fun f => decide (ClockEventWord.eventTime z.1 f < ClockEventWord.eventTime z.1 e))).reverse.map
              (fun f => (ClippedSquareCoordinates.recenter L f.1,z.2 f))))
        (ClippedSquareCoordinates.recenter L e.1,z.2 e)).card : Real) -
      ((D \ DropletStoppedWord.stoppedWord D I S
          (((ClockEventWord.word z.1 T).filter
            (fun f => decide (ClockEventWord.eventTime z.1 f < ClockEventWord.eventTime z.1 e))).reverse.map
              (fun f => (ClippedSquareCoordinates.recenter L f.1,z.2 f)))).card : Real) := by
  unfold PredictableAreaContribution.increment
  rw [ActualPreState.beforeState_eq_strictStateAt L D I S z hg hp,
    Real.coe_toNNReal _ (hp e).le]
  unfold ActualPreState.strictStateAt DropletClockLaw.markedEvents
  rw [strictWord_eq_filter_horizon z.1
    ((ClockEventWord.word_mem_iff z.1 T (hg T) e).mp he) (hg T)]

/-- Exact signed sum over all genuine identities by `T`; first-loss freezing is
already included in every stopped step. No probability or drift premise enters. -/
theorem area_telescope (L : Nat) (D I S : Finset Site) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) (T : NNReal) :
    ((D \ DropletStoppedClockLaw.stateAt L D I S (T : Real) z).card : Real) -
      ((D \ S).card : Real) =
    ((ClockEventWord.word z.1 (T : Real)).map (fun e =>
      PredictableAreaContribution.increment L D I S e.1 (z.2 e)
        ((ClockEventWord.eventTime z.1 e).toNNReal,z))).sum := by
  have h := stoppedWord_area_telescope (ClockEventWord.eventTime z.1)
    (fun e : Event L => (ClippedSquareCoordinates.recenter L e.1,z.2 e)) D I S
    (ClockEventWord.word z.1 (T : Real))
    (ClockEventWord.word_strictly_decreasing z.1 (T : Real))
  change _ = _ at h
  rw [show DropletStoppedClockLaw.stateAt L D I S (T : Real) z =
      DropletStoppedWord.stoppedWord D I S
        ((ClockEventWord.word z.1 (T : Real)).reverse.map
          (fun e => (ClippedSquareCoordinates.recenter L e.1,z.2 e))) from rfl]
  rw [h]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  exact (increment_eq_horizon_filter L D I S z hg hp (T : Real) e he).symm

/-- One common full-probability set supports the signed identity at all horizons. -/
theorem area_telescope_all_times_ae (L : Nat) (D I S : Finset Site) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ T : NNReal,
    ((D \ DropletStoppedClockLaw.stateAt L D I S (T : Real) z).card : Real) -
      ((D \ S).card : Real) =
    ((ClockEventWord.word z.1 (T : Real)).map (fun e =>
      PredictableAreaContribution.increment L D I S e.1 (z.2 e)
        ((ClockEventWord.eventTime z.1 e).toNNReal,z))).sum := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L,
    ActualPreState.marked_all_events_positive_ae L] with z hg hp
  exact fun T => area_telescope L D I S z hg hp T
/-- The finite list has no repeated identities, so its signed sum is exactly
the finite-set sum, without accidental multiplicities. -/
theorem sum_map_eq_sum_toFinset {α : Type*} [DecidableEq α] (w : List α) (hw : w.Nodup)
    (f : α → Real) : (w.map f).sum = ∑ e ∈ w.toFinset, f e := by
  classical
  induction w with
  | nil => simp
  | cons e w ih =>
    obtain ⟨he,hw⟩ := List.nodup_cons.mp hw
    simp only [List.map_cons,List.sum_cons,List.toFinset_cons]
    rw [Finset.sum_insert (by simpa only [List.mem_toFinset] using he),ih hw]

/-- The exact genuine finite identity set version, ready for comparison with
nonnegative marked arrival sums. -/
theorem area_telescope_finset (L : Nat) (D I S : Finset Site) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) (T : NNReal) :
    ((D \ DropletStoppedClockLaw.stateAt L D I S (T : Real) z).card : Real) -
      ((D \ S).card : Real) =
    ∑ e ∈ (ClockEventWord.word z.1 (T : Real)).toFinset,
      PredictableAreaContribution.increment L D I S e.1 (z.2 e)
        ((ClockEventWord.eventTime z.1 e).toNNReal,z) := by
  rw [area_telescope L D I S z hg hp T,
    sum_map_eq_sum_toFinset _ (ClockEventWord.word_nodup z.1 (T : Real))]

/-- All horizons share the same exceptional null set; the finite identity
sum therefore remains valid when a later argument observes a random horizon. -/
theorem area_telescope_finset_all_times_ae (L : Nat) (D I S : Finset Site) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ T : NNReal,
    ((D \ DropletStoppedClockLaw.stateAt L D I S (T : Real) z).card : Real) -
      ((D \ S).card : Real) =
    ∑ e ∈ (ClockEventWord.word z.1 (T : Real)).toFinset,
      PredictableAreaContribution.increment L D I S e.1 (z.2 e)
        ((ClockEventWord.eventTime z.1 e).toNNReal,z) := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L,
    ActualPreState.marked_all_events_positive_ae L] with z hg hp
  exact fun T => area_telescope_finset L D I S z hg hp T

/-- The event term can also be read directly as post-event minus strict-past
missing area. No future state or later mark enters the before state. -/
theorem increment_eq_actual_jump (L : Nat) (D I S : Finset Site) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) (e : Event L) :
    PredictableAreaContribution.increment L D I S e.1 (z.2 e)
      ((ClockEventWord.eventTime z.1 e).toNNReal,z) =
    ((D \ DropletStoppedClockLaw.stateAt L D I S
      (ClockEventWord.eventTime z.1 e) z).card : Real) -
    ((D \ ActualPreState.strictStateAt L D I S
      (ClockEventWord.eventTime z.1 e) z).card : Real) := by
  unfold PredictableAreaContribution.increment
  rw [← ActualPreState.stateAt_event_update L D I S z hg hp e,
    ActualPreState.beforeState_eq_strictStateAt L D I S z hg hp,
    Real.coe_toNNReal _ (hp e).le]

/-- A genuine finite sum of actual state jumps equals the whole area change. -/
theorem area_telescope_actual_jumps (L : Nat) (D I S : Finset Site) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) (T : NNReal) :
    ((D \ DropletStoppedClockLaw.stateAt L D I S (T : Real) z).card : Real) -
      ((D \ S).card : Real) =
    ∑ e ∈ (ClockEventWord.word z.1 (T : Real)).toFinset,
      (((D \ DropletStoppedClockLaw.stateAt L D I S
          (ClockEventWord.eventTime z.1 e) z).card : Real) -
        ((D \ ActualPreState.strictStateAt L D I S
          (ClockEventWord.eventTime z.1 e) z).card : Real)) := by
  rw [area_telescope_finset L D I S z hg hp T]
  apply Finset.sum_congr rfl
  intro e _
  exact increment_eq_actual_jump L D I S z hg hp e
end MathResearchAnalysis.ActualAreaTelescope

#print axioms MathResearchAnalysis.ActualAreaTelescope.strictWord_eq_filter_horizon
#print axioms MathResearchAnalysis.ActualAreaTelescope.stoppedWord_area_telescope
#print axioms MathResearchAnalysis.ActualAreaTelescope.increment_eq_horizon_filter
#print axioms MathResearchAnalysis.ActualAreaTelescope.area_telescope
#print axioms MathResearchAnalysis.ActualAreaTelescope.area_telescope_all_times_ae
#print axioms MathResearchAnalysis.ActualAreaTelescope.sum_map_eq_sum_toFinset
#print axioms MathResearchAnalysis.ActualAreaTelescope.area_telescope_finset
#print axioms MathResearchAnalysis.ActualAreaTelescope.area_telescope_finset_all_times_ae
#print axioms MathResearchAnalysis.ActualAreaTelescope.increment_eq_actual_jump
#print axioms MathResearchAnalysis.ActualAreaTelescope.area_telescope_actual_jumps
