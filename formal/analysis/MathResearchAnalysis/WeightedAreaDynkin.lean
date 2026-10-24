module
public import MathResearchAnalysis.PhysicalAreaGenerator
public import MathResearchAnalysis.CumulativeCleanupBudget
public import MathResearchAnalysis.ForbiddenBirthControl
set_option autoImplicit false
/-! Physical Dynkin for a genuinely bounded finite-mask observable, followed by
vanishing-boundary weighted missing mass. All probabilities are the original
joint clock/mark law and all event scores use the actual strict past.
No drift estimate, compensator identity or recovery assertion is assumed. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.WeightedAreaDynkin
open MeasureTheory
open DropletClockLaw (Sample Event Vertex)
open InfiniteGridModel (Site)
variable (observable : Finset Site → Real)

/-- Only the finite mask is visible to the observable. -/
def value (D U : Finset Site) : Real := observable (U ∩ D)

/-- A finite, explicit bound; it is constructed, not required as a premise. -/
def bound (D : Finset Site) : Real := ∑ U ∈ D.powerset, ‖observable U‖

theorem value_norm_le (D U : Finset Site) : ‖value observable D U‖ ≤ bound observable D := by
  unfold value bound
  exact Finset.single_le_sum (fun W _ => norm_nonneg (observable W))
    (Finset.mem_powerset.mpr Finset.inter_subset_right)

def increment (L : Nat) (D I S : Finset Site) (v : Vertex L) (b : Bool)
    (p : NNReal × Sample L) : Real :=
  value observable D (DropletStoppedWord.stoppedStep D I
    (ObservedPreState.beforeState L D I S p.1 p.2)
    (ClippedSquareCoordinates.recenter L v,b)) -
  value observable D (ObservedPreState.beforeState L D I S p.1 p.2)

theorem increment_stronglyMeasurable (L : Nat) (D I S : Finset Site)
    (v : Vertex L) (b : Bool) :
    StronglyMeasurable[(RationalProtectedExit.nnHistory L).predictable]
      (increment observable L D I S v b) :=
  (ObservedPreState.observable_measurable L D I S (fun U : Finset Site =>
    value observable D (DropletStoppedWord.stoppedStep D I U
      (ClippedSquareCoordinates.recenter L v,b)) - value observable D U)).stronglyMeasurable

theorem increment_norm_le (L : Nat) (D I S : Finset Site)
    (v : Vertex L) (b : Bool) (p : NNReal × Sample L) :
    ‖increment observable L D I S v b p‖ ≤ 2 * bound observable D := by
  unfold increment
  exact (norm_sub_le _ _).trans (by
    have h1 := value_norm_le observable D (DropletStoppedWord.stoppedStep D I
      (ObservedPreState.beforeState L D I S p.1 p.2)
      (ClippedSquareCoordinates.recenter L v,b))
    have h2 := value_norm_le observable D (ObservedPreState.beforeState L D I S p.1 p.2)
    linarith)

theorem stoppedWord_observable_telescope {α : Type*} (time : α → Real)
    (mark : α → DropletModifiedWord.Event) (D I S : Finset Site)
    (w : List α) (hw : w.Pairwise (fun a b => time b < time a)) :
    value observable D (DropletStoppedWord.stoppedWord D I S (w.reverse.map mark)) -
      value observable D (S) =
    (w.map (fun e =>
      value observable D (DropletStoppedWord.stoppedStep D I
        (DropletStoppedWord.stoppedWord D I S
          ((w.filter (fun f => decide (time f < time e))).reverse.map mark)) (mark e)) -
      value observable D (DropletStoppedWord.stoppedWord D I S
        ((w.filter (fun f => decide (time f < time e))).reverse.map mark)))).sum := by
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
        value observable D (DropletStoppedWord.stoppedStep D I
          (DropletStoppedWord.stoppedWord D I S
            (((e :: w).filter (fun g => decide (time g < time f))).reverse.map mark)) (mark f)) -
        value observable D (DropletStoppedWord.stoppedWord D I S
          (((e :: w).filter (fun g => decide (time g < time f))).reverse.map mark))) =
      w.map (fun f =>
        value observable D (DropletStoppedWord.stoppedStep D I
          (DropletStoppedWord.stoppedWord D I S
            ((w.filter (fun g => decide (time g < time f))).reverse.map mark)) (mark f)) -
        value observable D (DropletStoppedWord.stoppedWord D I S
          ((w.filter (fun g => decide (time g < time f))).reverse.map mark))) := by
      apply List.map_congr_left
      intro f hf
      have hnot : ¬ time e < time f := not_lt_of_gt (he f hf)
      simp only [List.filter_cons,decide_eq_false hnot,Bool.false_eq_true,↓reduceIte]
    rw [List.reverse_cons,List.map_append,List.map_singleton,
      DropletStoppedWord.stoppedWord_append,DropletStoppedWord.stoppedWord_cons,
      DropletStoppedWord.stoppedWord_nil,List.map_cons,List.sum_cons,hfilter,htail,
      ← ih hw]
    ring

theorem increment_eq_horizon_filter (L : Nat) (D I S : Finset Site)
    (z : Sample L) (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e)
    (T : Real) (e : Event L) (he : e ∈ ClockEventWord.word z.1 T) :
    increment observable L D I S e.1 (z.2 e)
      ((ClockEventWord.eventTime z.1 e).toNNReal,z) =
      value observable D (DropletStoppedWord.stoppedStep D I
        (DropletStoppedWord.stoppedWord D I S
          (((ClockEventWord.word z.1 T).filter
            (fun f => decide (ClockEventWord.eventTime z.1 f < ClockEventWord.eventTime z.1 e))).reverse.map
              (fun f => (ClippedSquareCoordinates.recenter L f.1,z.2 f))))
        (ClippedSquareCoordinates.recenter L e.1,z.2 e)) -
      value observable D (DropletStoppedWord.stoppedWord D I S
          (((ClockEventWord.word z.1 T).filter
            (fun f => decide (ClockEventWord.eventTime z.1 f < ClockEventWord.eventTime z.1 e))).reverse.map
              (fun f => (ClippedSquareCoordinates.recenter L f.1,z.2 f)))) := by
  unfold increment
  rw [ActualPreState.beforeState_eq_strictStateAt L D I S z hg hp,
    Real.coe_toNNReal _ (hp e).le]
  unfold ActualPreState.strictStateAt DropletClockLaw.markedEvents
  rw [ActualAreaTelescope.strictWord_eq_filter_horizon z.1
    ((ClockEventWord.word_mem_iff z.1 T (hg T) e).mp he) (hg T)]

/-- Exact signed sum over all genuine identities by `T`; first-loss freezing is
already included in every stopped step. No probability or drift premise enters. -/
theorem observable_telescope (L : Nat) (D I S : Finset Site) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) (T : NNReal) :
    value observable D (DropletStoppedClockLaw.stateAt L D I S (T : Real) z) -
      value observable D (S) =
    ((ClockEventWord.word z.1 (T : Real)).map (fun e =>
      increment observable L D I S e.1 (z.2 e)
        ((ClockEventWord.eventTime z.1 e).toNNReal,z))).sum := by
  have h := stoppedWord_observable_telescope observable (ClockEventWord.eventTime z.1)
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
  exact (increment_eq_horizon_filter observable L D I S z hg hp (T : Real) e he).symm

/-- One common full-probability set supports the signed identity at all horizons. -/
theorem observable_telescope_all_times_ae (L : Nat) (D I S : Finset Site) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ T : NNReal,
    value observable D (DropletStoppedClockLaw.stateAt L D I S (T : Real) z) -
      value observable D (S) =
    ((ClockEventWord.word z.1 (T : Real)).map (fun e =>
      increment observable L D I S e.1 (z.2 e)
        ((ClockEventWord.eventTime z.1 e).toNNReal,z))).sum := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L,
    ActualPreState.marked_all_events_positive_ae L] with z hg hp
  exact fun T => observable_telescope observable L D I S z hg hp T
theorem observable_telescope_finset (L : Nat) (D I S : Finset Site) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) (T : NNReal) :
    value observable D (DropletStoppedClockLaw.stateAt L D I S (T : Real) z) -
      value observable D (S) =
    ∑ e ∈ (ClockEventWord.word z.1 (T : Real)).toFinset,
      increment observable L D I S e.1 (z.2 e)
        ((ClockEventWord.eventTime z.1 e).toNNReal,z) := by
  rw [observable_telescope observable L D I S z hg hp T,
    ActualAreaTelescope.sum_map_eq_sum_toFinset _ (ClockEventWord.word_nodup z.1 (T : Real))]

/-- All horizons share the same exceptional null set; the finite identity
sum therefore remains valid when a later argument observes a random horizon. -/
theorem observable_telescope_finset_all_times_ae (L : Nat) (D I S : Finset Site) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ T : NNReal,
    value observable D (DropletStoppedClockLaw.stateAt L D I S (T : Real) z) -
      value observable D (S) =
    ∑ e ∈ (ClockEventWord.word z.1 (T : Real)).toFinset,
      increment observable L D I S e.1 (z.2 e)
        ((ClockEventWord.eventTime z.1 e).toNNReal,z) := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L,
    ActualPreState.marked_all_events_positive_ae L] with z hg hp
  exact fun T => observable_telescope_finset observable L D I S z hg hp T

def eventScore (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (e : Event L) : Real :=
  if 0 < ClockEventWord.eventTime z.1 e ∧ ClockEventWord.eventTime z.1 e ≤ (T : Real) then
    increment observable L D I S e.1 (z.2 e)
      ((ClockEventWord.eventTime z.1 e).toNNReal,z)
  else 0

/-- Precisely one Boolean-mark window matches the identity's actual mark. -/
theorem bool_sum_term (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (v : Vertex L) (k : Nat) :
    (∑ b : Bool, RealPredictableCompensation.term L v b T
      (increment observable L D I S v b) k z) =
      eventScore observable L D I S T z (v,k) := by
  classical
  by_cases ht : 0 < ClockEventWord.eventTime z.1 (v,k) ∧
      ClockEventWord.eventTime z.1 (v,k) ≤ (T : Real)
  · cases hm : z.2 (v,k) <;>
      simp [RealPredictableCompensation.term,
        MarkedClockPointMeasure.window,MarkedClockPointMeasure.point,eventScore,ht,hm]
  · have hz (b : Bool) : z ∉ MarkedClockPointMeasure.window L v b T k := by
      intro h
      exact ht ⟨h.1,h.2.1⟩
    simp only [RealPredictableCompensation.term,Set.indicator_of_notMem (hz _),
      Finset.sum_const_zero,eventScore,ite_eq_right ht]

theorem eventScore_zero_outside_word (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real))
    (e : Event L) (he : e ∉ (ClockEventWord.word z.1 (T : Real)).toFinset) :
    eventScore observable L D I S T z e = 0 := by
  have hnot : ¬ ClockEventWord.eventTime z.1 e ≤ (T : Real) := by
    intro ht
    exact he (List.mem_toFinset.mpr ((ClockEventWord.word_mem_iff z.1 (T : Real) hg e).mpr ht))
  simp [eventScore,hnot]

/-- The genuine finite horizon word proves signed summability pathwise. -/
theorem eventScore_summable (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real)) :
    Summable (eventScore observable L D I S T z) :=
  summable_of_ne_finset_zero (s := (ClockEventWord.word z.1 (T : Real)).toFinset)
    (eventScore_zero_outside_word observable L D I S T z hg)

/-- Each actual site/mark series is supported on the finite projection of the
true word. This proves the hypothesis needed before exchanging sum orders. -/
theorem term_summable (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real))
    (v : Vertex L) (b : Bool) :
    Summable (fun k : Nat => RealPredictableCompensation.term L v b T
      (increment observable L D I S v b) k z) := by
  classical
  apply summable_of_ne_finset_zero
    (s := (ClockEventWord.word z.1 (T : Real)).toFinset.image Prod.snd)
  intro k hk
  have hz : z ∉ MarkedClockPointMeasure.window L v b T k := by
    intro h
    exact hk (Finset.mem_image.mpr ⟨(v,k),List.mem_toFinset.mpr
      ((ClockEventWord.word_mem_iff z.1 (T : Real) hg (v,k)).mpr h.2.1),rfl⟩)
  exact Set.indicator_of_notMem hz _

theorem sum_pathSums_eq_tsum_eventScore (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real)) :
    (∑ v : Vertex L, ∑ b : Bool, RealPredictableCompensation.pathSum L v b T
      (increment observable L D I S v b) z) =
      ∑' e : Event L, eventScore observable L D I S T z e := by
  classical
  rw [(eventScore_summable observable L D I S T z hg).tsum_prod,tsum_fintype]
  apply Finset.sum_congr rfl
  intro v _
  unfold RealPredictableCompensation.pathSum
  rw [← Summable.tsum_finsetSum (s := Finset.univ)
    (f := fun b : Bool => fun k : Nat => RealPredictableCompensation.term L v b T
      (increment observable L D I S v b) k z)
    (fun b _ => term_summable observable L D I S T z hg v b)]
  apply tsum_congr
  intro k
  exact bool_sum_term observable L D I S T z v k

theorem tsum_eventScore_eq_word_sum (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real))
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) :
    (∑' e : Event L, eventScore observable L D I S T z e) =
    ∑ e ∈ (ClockEventWord.word z.1 (T : Real)).toFinset,
      increment observable L D I S e.1 (z.2 e)
        ((ClockEventWord.eventTime z.1 e).toNNReal,z) := by
  classical
  rw [tsum_eq_sum (s := (ClockEventWord.word z.1 (T : Real)).toFinset)
    (eventScore_zero_outside_word observable L D I S T z hg)]
  apply Finset.sum_congr rfl
  intro e he
  have ht := (ClockEventWord.word_mem_iff z.1 (T : Real) hg e).mp (List.mem_toFinset.mp he)
  change ClockEventWord.eventTime z.1 e ≤ (T : Real) at ht
  simp only [eventScore,hp e,ht,and_self,↓reduceIte]

theorem sum_pathSums_eq_word_sum (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real))
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) :
    (∑ v : Vertex L, ∑ b : Bool, RealPredictableCompensation.pathSum L v b T
      (increment observable L D I S v b) z) =
    ∑ e ∈ (ClockEventWord.word z.1 (T : Real)).toFinset,
      increment observable L D I S e.1 (z.2 e)
        ((ClockEventWord.eventTime z.1 e).toNNReal,z) :=
  (sum_pathSums_eq_tsum_eventScore observable L D I S T z hg).trans
    (tsum_eventScore_eq_word_sum observable L D I S T z hg hp)

/-- The actual full area change is exactly the sum of the site's true marked
pathwise contributions, including the event at the first-loss freeze. -/
theorem observable_eq_pathSums (L : Nat) (D I S : Finset Site) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) (T : NNReal) :
    value observable D (DropletStoppedClockLaw.stateAt L D I S (T : Real) z) -
      value observable D (S) =
    ∑ v : Vertex L, ∑ b : Bool, RealPredictableCompensation.pathSum L v b T
      (increment observable L D I S v b) z :=
  (observable_telescope_finset observable L D I S z hg hp T).trans
    (sum_pathSums_eq_word_sum observable L D I S T z (hg _) hp).symm

/-- One full-probability set works at every horizon, with the original sample
law. No separate exceptional set is chosen for a random observation time. -/
theorem observable_eq_pathSums_all_times_ae (L : Nat) (D I S : Finset Site) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ T : NNReal,
    value observable D (DropletStoppedClockLaw.stateAt L D I S (T : Real) z) -
      value observable D (S) =
    ∑ v : Vertex L, ∑ b : Bool, RealPredictableCompensation.pathSum L v b T
      (increment observable L D I S v b) z := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L,
    ActualPreState.marked_all_events_positive_ae L] with z hg hp
  exact fun T => observable_eq_pathSums observable L D I S z hg hp T
theorem marked_pathSum_integrable (L : Nat) (D I S : Finset Site)
    (v : Vertex L) (b : Bool) (T : NNReal) :
    Integrable (RealPredictableCompensation.pathSum L v b T
      (increment observable L D I S v b))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  RealPredictableCompensation.bounded_predictable_integrable L v b T
    (increment observable L D I S v b)
    (increment_stronglyMeasurable observable L D I S v b)
    (2 * bound observable D) (increment_norm_le observable L D I S v b)

theorem total_pathSum_integrable (L : Nat) (D I S : Finset Site) (T : NNReal) :
    Integrable (fun z : Sample L => ∑ v : Vertex L, ∑ b : Bool,
      RealPredictableCompensation.pathSum L v b T
        (increment observable L D I S v b) z)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  exact integrable_finsetSum _ fun v _ => integrable_finsetSum _ fun b _ =>
    marked_pathSum_integrable observable L D I S v b T

theorem observable_change_integrable (L : Nat) (D I S : Finset Site) (T : NNReal) :
    Integrable (fun z : Sample L =>
      value observable D (DropletStoppedClockLaw.stateAt L D I S (T : Real) z) -
        value observable D (S))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  apply (total_pathSum_integrable observable L D I S T).congr
  filter_upwards [observable_eq_pathSums_all_times_ae observable L D I S] with z hz
  exact (hz T).symm

theorem observable_integrable (L : Nat) (D I S : Finset Site) (T : NNReal) :
    Integrable (fun z : Sample L =>
      value observable D (DropletStoppedClockLaw.stateAt L D I S (T : Real) z))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  convert (observable_change_integrable observable L D I S T).add
    (integrable_const (value observable D (S))) using 1
  ext z
  simp only [Pi.add_apply]
  ring

/-- Exact physical signed compensation, with integrability established first.
Each half rate belongs to one specified fair mark at one original site. -/
theorem observable_change_dynkin (L : Nat) (D I S : Finset Site) (T : NNReal) :
    (∫ z : Sample L,
      value observable D (DropletStoppedClockLaw.stateAt L D I S (T : Real) z) -
        value observable D (S)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    ∑ v : Vertex L, ∑ b : Bool, (1 / 2 : Real) * ∫ u : Real in Set.Ioc 0 (T : Real),
      ∫ z : Sample L, increment observable L D I S v b (u.toNNReal,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  calc
    _ = ∫ z : Sample L, ∑ v : Vertex L, ∑ b : Bool,
        RealPredictableCompensation.pathSum L v b T
          (increment observable L D I S v b) z
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
      apply integral_congr_ae
      filter_upwards [observable_eq_pathSums_all_times_ae observable L D I S] with z hz
      exact hz T
    _ = _ := by
      rw [integral_finsetSum _ (fun v _ =>
        integrable_finsetSum _ (fun b _ => marked_pathSum_integrable observable L D I S v b T))]
      apply Finset.sum_congr rfl
      intro v _
      rw [integral_finsetSum _ (fun b _ => marked_pathSum_integrable observable L D I S v b T)]
      apply Finset.sum_congr rfl
      intro b _
      exact RealPredictableCompensation.bounded_predictable_integral_eq_time L v b T
        (increment observable L D I S v b)
        (increment_stronglyMeasurable observable L D I S v b)
        (2 * bound observable D) (increment_norm_le observable L D I S v b)

theorem time_mean_increment_integrable (L : Nat) (D I S : Finset Site)
    (v : Vertex L) (b : Bool) (T : NNReal) :
    Integrable (fun u : Real => ∫ z : Sample L,
      increment observable L D I S v b (u.toNNReal,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L))
      ((volume : Measure Real).restrict (Set.Ioc 0 (T : Real))) :=
  RealPredictableCompensation.time_mean_integrable L T
    (increment observable L D I S v b)
    ((increment_stronglyMeasurable observable L D I S v b).mono
      (PredictableClockSigma.predictable_le_ambient L))
    (2 * bound observable D) (increment_norm_le observable L D I S v b)

theorem observable_change_dynkin_single_integral (L : Nat) (D I S : Finset Site) (T : NNReal) :
    (∫ z : Sample L,
      value observable D (DropletStoppedClockLaw.stateAt L D I S (T : Real) z) -
        value observable D (S)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    (1 / 2 : Real) * ∫ u : Real in Set.Ioc 0 (T : Real), ∑ v : Vertex L, ∑ b : Bool,
      ∫ z : Sample L, increment observable L D I S v b (u.toNNReal,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  rw [observable_change_dynkin observable]
  have hsum : (∫ u : Real in Set.Ioc 0 (T : Real), ∑ v : Vertex L, ∑ b : Bool,
      ∫ z : Sample L, increment observable L D I S v b (u.toNNReal,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      ∑ v : Vertex L, ∑ b : Bool, ∫ u : Real in Set.Ioc 0 (T : Real),
        ∫ z : Sample L, increment observable L D I S v b (u.toNNReal,z)
          ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
    rw [integral_finsetSum _ (fun v _ => integrable_finsetSum _
      (fun b _ => time_mean_increment_integrable observable L D I S v b T))]
    apply Finset.sum_congr rfl
    intro v _
    exact integral_finsetSum _ (fun b _ => time_mean_increment_integrable observable L D I S v b T)
  rw [hsum]
  simp only [Finset.mul_sum]

theorem expected_observable_dynkin (L : Nat) (D I S : Finset Site) (T : NNReal) :
    (∫ z : Sample L, value observable D (DropletStoppedClockLaw.stateAt L D I S (T : Real) z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    value observable D (S) +
      ∑ v : Vertex L, ∑ b : Bool, (1 / 2 : Real) * ∫ u : Real in Set.Ioc 0 (T : Real),
        ∫ z : Sample L, increment observable L D I S v b (u.toNNReal,z)
          ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  have h := observable_change_dynkin observable L D I S T
  rw [integral_sub (observable_integrable observable L D I S T) (integrable_const _)] at h
  simpa only [integral_const,probReal_univ,one_smul] using (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
theorem observable_rate_eq_generator (L : Nat) (D I S : Finset Site)
    (hD : D ⊆ ClippedSquareCoordinates.centeredSites L) (p : NNReal × Sample L) :
    (1 / 2 : Real) * ∑ v : Vertex L, ∑ b : Bool,
      increment observable L D I S v b p =
    MaskedAreaGenerator.frozenGenerator D I
      (ObservedPreState.beforeState L D I S p.1 p.2)
      (fun U => value observable D (U)) := by
  simpa only [increment] using
    PhysicalAreaGenerator.finite_vertex_generator_eq L D I
      (ObservedPreState.beforeState L D I S p.1 p.2)
      (fun U : Finset Site => value observable D (U)) hD

theorem generator_sample_integrable (L : Nat) (D I S : Finset Site)
    (hD : D ⊆ ClippedSquareCoordinates.centeredSites L) (u : NNReal) :
    Integrable (fun z : Sample L => MaskedAreaGenerator.frozenGenerator D I
      (ObservedPreState.beforeState L D I S u z) (fun U => value observable D (U)))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  have hi (v : Vertex L) (b : Bool) : Integrable (fun z : Sample L =>
      increment observable L D I S v b (u,z))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
    RealPredictableCompensation.sample_integrable L _
      ((increment_stronglyMeasurable observable L D I S v b).mono
        (PredictableClockSigma.predictable_le_ambient L))
      (2 * bound observable D) (increment_norm_le observable L D I S v b) u
  have hs := integrable_finsetSum Finset.univ (fun v _ =>
    integrable_finsetSum Finset.univ (fun b _ => hi v b))
  apply (hs.const_mul (1 / 2 : Real)).congr
  exact Filter.Eventually.of_forall (fun z => observable_rate_eq_generator observable L D I S hD (u,z))

theorem expected_rate_eq_generator (L : Nat) (D I S : Finset Site)
    (hD : D ⊆ ClippedSquareCoordinates.centeredSites L) (u : NNReal) :
    (1 / 2 : Real) * ∑ v : Vertex L, ∑ b : Bool,
      ∫ z : Sample L, increment observable L D I S v b (u,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) =
    ∫ z : Sample L, MaskedAreaGenerator.frozenGenerator D I
      (ObservedPreState.beforeState L D I S u z) (fun U => value observable D (U))
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  have hi (v : Vertex L) (b : Bool) : Integrable (fun z : Sample L =>
      increment observable L D I S v b (u,z))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
    RealPredictableCompensation.sample_integrable L _
      ((increment_stronglyMeasurable observable L D I S v b).mono
        (PredictableClockSigma.predictable_le_ambient L))
      (2 * bound observable D) (increment_norm_le observable L D I S v b) u
  have hs : (∫ z : Sample L, ∑ v : Vertex L, ∑ b : Bool,
      increment observable L D I S v b (u,z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      ∑ v : Vertex L, ∑ b : Bool, ∫ z : Sample L,
        increment observable L D I S v b (u,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
    rw [integral_finsetSum _ (fun v _ => integrable_finsetSum _ (fun b _ => hi v b))]
    apply Finset.sum_congr rfl
    intro v _
    exact integral_finsetSum _ (fun b _ => hi v b)
  rw [← hs, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (fun z => observable_rate_eq_generator observable L D I S hD (u,z)))

theorem generator_time_mean_integrable (L : Nat) (D I S : Finset Site)
    (hD : D ⊆ ClippedSquareCoordinates.centeredSites L) (T : NNReal) :
    Integrable (fun u : Real => ∫ z : Sample L, MaskedAreaGenerator.frozenGenerator D I
      (ObservedPreState.beforeState L D I S u.toNNReal z) (fun U => value observable D (U))
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L))
      ((volume : Measure Real).restrict (Set.Ioc 0 (T : Real))) := by
  have hs := integrable_finsetSum Finset.univ (fun v _ =>
    integrable_finsetSum Finset.univ (fun b _ =>
      time_mean_increment_integrable observable L D I S v b T))
  apply (hs.const_mul (1 / 2 : Real)).congr
  exact Filter.Eventually.of_forall
    (fun u => expected_rate_eq_generator observable L D I S hD u.toNNReal)

theorem observable_change_dynkin_generator (L : Nat) (D I S : Finset Site)
    (hD : D ⊆ ClippedSquareCoordinates.centeredSites L) (T : NNReal) :
    (∫ z : Sample L,
      value observable D (DropletStoppedClockLaw.stateAt L D I S (T : Real) z) -
        value observable D (S)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    ∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L,
      MaskedAreaGenerator.frozenGenerator D I
        (ObservedPreState.beforeState L D I S u.toNNReal z)
        (fun U => value observable D (U))
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  rw [observable_change_dynkin_single_integral observable, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (fun u => expected_rate_eq_generator observable L D I S hD u.toNNReal))


def missing (L : Nat) (U : Finset Site) : Real :=
  ForbiddenBirthControl.mass (ForbiddenBirthControl.weight L)
    (ClippedDiamondGeometry.clippedDomain L \ U)

theorem value_missing_eq (L : Nat) (U : Finset Site) :
    value (missing L) (ClippedDiamondGeometry.clippedDomain L) U = missing L U := by
  unfold value missing
  have he : ClippedDiamondGeometry.clippedDomain L \ (U ∩ ClippedDiamondGeometry.clippedDomain L) =
      ClippedDiamondGeometry.clippedDomain L \ U := by
    ext v
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    tauto
  rw [he]

theorem missing_initial (L : Nat) : missing L (ClippedDiamondGeometry.clippedDomain L) = 0 := by
  simp [missing,ForbiddenBirthControl.mass]

/-- The true weighted missing mass has a physical finite-time Dynkin formula. -/
theorem actual_weighted_area_dynkin (L : Nat) (hL : 1 ≤ L) (T : NNReal) :
    (∫ z : Sample L, missing L (DropletStoppedClockLaw.stateAt L
      (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
      (ClippedDiamondGeometry.clippedDomain L) (T : Real) z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    ∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L,
      MaskedAreaGenerator.frozenGenerator (ClippedDiamondGeometry.clippedDomain L)
        (ClippedProtectedGeometry.protectedSites L)
        (ObservedPreState.beforeState L (ClippedDiamondGeometry.clippedDomain L)
          (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L)
          u.toNNReal z) (missing L)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  have h := observable_change_dynkin_generator (missing L) L
    (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
    (ClippedDiamondGeometry.clippedDomain L)
    (ClippedSquareCoordinates.clippedDomain_subset_centeredSites L hL) T
  simpa only [value_missing_eq,missing_initial,sub_zero] using h


theorem actual_weighted_area_integrable (L : Nat) (T : NNReal) :
    Integrable (fun z : Sample L => missing L (DropletStoppedClockLaw.stateAt L
      (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
      (ClippedDiamondGeometry.clippedDomain L) (T : Real) z))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  simpa only [value_missing_eq] using observable_integrable (missing L) L
    (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
    (ClippedDiamondGeometry.clippedDomain L) T

theorem weighted_generator_sample_integrable (L : Nat) (hL : 1 ≤ L) (u : NNReal) :
    Integrable (fun z : Sample L => MaskedAreaGenerator.frozenGenerator
      (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
      (ObservedPreState.beforeState L (ClippedDiamondGeometry.clippedDomain L)
        (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L)
        u z) (missing L))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  simpa only [value_missing_eq] using generator_sample_integrable (missing L) L
    (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
    (ClippedDiamondGeometry.clippedDomain L)
    (ClippedSquareCoordinates.clippedDomain_subset_centeredSites L hL) u

theorem weighted_generator_time_mean_integrable (L : Nat) (hL : 1 ≤ L) (T : NNReal) :
    Integrable (fun u : Real => ∫ z : Sample L,
      MaskedAreaGenerator.frozenGenerator (ClippedDiamondGeometry.clippedDomain L)
        (ClippedProtectedGeometry.protectedSites L)
        (ObservedPreState.beforeState L (ClippedDiamondGeometry.clippedDomain L)
          (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L)
          u.toNNReal z) (missing L)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L))
      ((volume : Measure Real).restrict (Set.Ioc 0 (T : Real))) := by
  simpa only [value_missing_eq] using generator_time_mean_integrable (missing L) L
    (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
    (ClippedDiamondGeometry.clippedDomain L)
    (ClippedSquareCoordinates.clippedDomain_subset_centeredSites L hL) T

theorem missing_nonnegative (L : Nat) (U : Finset Site) : 0 ≤ missing L U := by
  unfold missing ForbiddenBirthControl.mass
  apply Finset.sum_nonneg
  intro v hv
  exact (by norm_num : (0 : Real) ≤ 1).trans
    (ForbiddenBirthControl.weight_nonnegative_on_domain L v (Finset.mem_sdiff.mp hv).1)

theorem mass_sub_of_subset (w : Site → Real) {A B : Finset Site} (hAB : A ⊆ B) :
    ForbiddenBirthControl.mass w B - ForbiddenBirthControl.mass w A =
      ForbiddenBirthControl.mass w (B \ A) := by
  have h := Finset.sum_sdiff (f := w) hAB
  unfold ForbiddenBirthControl.mass
  linarith

/-- Actual weighted occupied mass erased by this event's cleanup. -/
def weightedLoss (L : Nat) (U : Finset Site) (e : DropletModifiedWord.Event) : Real :=
  ForbiddenBirthControl.mass (ForbiddenBirthControl.weight L)
    (DropletModifiedWord.maskedRawStep (ClippedDiamondGeometry.clippedDomain L) U e.1 e.2) -
  ForbiddenBirthControl.mass (ForbiddenBirthControl.weight L)
    (DropletModifiedWord.modifiedStep (ClippedDiamondGeometry.clippedDomain L) U e.1 e.2)

theorem weightedLoss_nonnegative {L : Nat} {U : Finset Site}
    (hUD : U ⊆ ClippedDiamondGeometry.clippedDomain L) (e : DropletModifiedWord.Event) :
    0 ≤ weightedLoss L U e := by
  unfold weightedLoss
  rw [mass_sub_of_subset (ForbiddenBirthControl.weight L)
    (DropletModifiedWord.modifiedStep_subset_maskedRawStep _ _ _ _)]
  unfold ForbiddenBirthControl.mass
  apply Finset.sum_nonneg
  intro v hv
  exact (by norm_num : (0 : Real) ≤ 1).trans
    (ForbiddenBirthControl.weight_nonnegative_on_domain L v
      (DropletModifiedWord.maskedRawStep_supported hUD e.1 e.2 (Finset.mem_sdiff.mp hv).1))

/-- Cleanup may erase many sites; every erased site's weight is paid. -/
theorem weightedLoss_le (L : Nat) (U : Finset Site) (e : DropletModifiedWord.Event) :
    weightedLoss L U e ≤ ((L : Real) + 2) *
      (GridPerimeterDynamics.eventLoss (ClippedDiamondGeometry.clippedDomain L) U e : Real) := by
  let A := DropletModifiedWord.maskedRawStep (ClippedDiamondGeometry.clippedDomain L) U e.1 e.2
  let B := DropletModifiedWord.modifiedStep (ClippedDiamondGeometry.clippedDomain L) U e.1 e.2
  have hBA : B ⊆ A := DropletModifiedWord.modifiedStep_subset_maskedRawStep _ _ _ _
  have hc : ((A \ B).card : Real) =
      (GridPerimeterDynamics.eventLoss (ClippedDiamondGeometry.clippedDomain L) U e : Real) := by
    rw [Finset.card_sdiff_of_subset hBA]
    rfl
  unfold weightedLoss
  rw [mass_sub_of_subset (ForbiddenBirthControl.weight L) hBA]
  calc
    _ ≤ ∑ v ∈ A \ B, ((L : Real) + 2) :=
      Finset.sum_le_sum (fun v _ => ForbiddenBirthControl.weight_upper_bound L v)
    _ = ((A \ B).card : Real) * ((L : Real) + 2) := by simp; ring
    _ = _ := by rw [hc]; ring

/-- The actual first-loss-frozen weighted cleanup rate. -/
def cleanupRate (L : Nat) (I U : Finset Site) : Real :=
  if I ⊆ U then ∑ v ∈ ClippedDiamondGeometry.clippedDomain L,
    (weightedLoss L U (v,false) + weightedLoss L U (v,true)) / 2 else 0

theorem cleanupRate_nonnegative {L : Nat} (I : Finset Site) {U : Finset Site}
    (hUD : U ⊆ ClippedDiamondGeometry.clippedDomain L) : 0 ≤ cleanupRate L I U := by
  unfold cleanupRate
  split_ifs
  · apply Finset.sum_nonneg
    intro v _
    exact div_nonneg (add_nonneg (weightedLoss_nonnegative hUD (v,false))
      (weightedLoss_nonnegative hUD (v,true))) (by norm_num)
  · exact le_rfl

theorem cleanupRate_le (L : Nat) (I U : Finset Site) :
    cleanupRate L I U ≤ ((L : Real) + 2) *
      CumulativeCleanupBudget.rate (ClippedDiamondGeometry.clippedDomain L) I U := by
  unfold cleanupRate CumulativeCleanupBudget.rate
  split_ifs
  · unfold MaskedAreaGenerator.cleanupRate
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    have h0 := weightedLoss_le L U (v,false)
    have h1 := weightedLoss_le L U (v,true)
    linarith
  · simp

def cleanupContribution (L : Nat) (I : Finset Site) (p : NNReal × Sample L) : Real :=
  cleanupRate L I (ObservedPreState.beforeState L (ClippedDiamondGeometry.clippedDomain L)
    I (ClippedDiamondGeometry.clippedDomain L) p.1 p.2)

theorem cleanupContribution_stronglyMeasurable (L : Nat) (I : Finset Site) :
    StronglyMeasurable[(RationalProtectedExit.nnHistory L).predictable]
      (cleanupContribution L I) :=
  (ObservedPreState.observable_measurable L (ClippedDiamondGeometry.clippedDomain L)
    I (ClippedDiamondGeometry.clippedDomain L) (cleanupRate L I)).stronglyMeasurable

/-- The powerset bound also covers all exceptional and fallback samples. -/
theorem cleanupContribution_norm_le (L : Nat) (I : Finset Site) (p : NNReal × Sample L) :
    ‖cleanupContribution L I p‖ ≤ bound (cleanupRate L I) (ClippedDiamondGeometry.clippedDomain L) := by
  have hs := ObservedPreState.state_supported L (ClippedDiamondGeometry.clippedDomain L) I
    (Finset.Subset.refl _) p.1 p.2
  simpa only [value,cleanupContribution,Finset.inter_eq_left.mpr hs] using
    value_norm_le (cleanupRate L I) (ClippedDiamondGeometry.clippedDomain L)
      (ObservedPreState.beforeState L (ClippedDiamondGeometry.clippedDomain L)
        I (ClippedDiamondGeometry.clippedDomain L) p.1 p.2)

theorem cleanup_sample_integrable (L : Nat) (I : Finset Site) (u : NNReal) :
    Integrable (fun z : Sample L => cleanupContribution L I (u,z))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  RealPredictableCompensation.sample_integrable L (cleanupContribution L I)
    ((cleanupContribution_stronglyMeasurable L I).mono (PredictableClockSigma.predictable_le_ambient L))
    (bound (cleanupRate L I) (ClippedDiamondGeometry.clippedDomain L))
    (cleanupContribution_norm_le L I) u

theorem cleanup_time_mean_integrable (L : Nat) (I : Finset Site) (T : NNReal) :
    Integrable (fun u : Real => ∫ z : Sample L, cleanupContribution L I (u.toNNReal,z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L))
      ((volume : Measure Real).restrict (Set.Ioc 0 (T : Real))) :=
  RealPredictableCompensation.time_mean_integrable L T (cleanupContribution L I)
    ((cleanupContribution_stronglyMeasurable L I).mono (PredictableClockSigma.predictable_le_ambient L))
    (bound (cleanupRate L I) (ClippedDiamondGeometry.clippedDomain L))
    (cleanupContribution_norm_le L I)

/-- True physical-time weighted cleanup is bounded by (L+2)(4L+2). -/
theorem actual_weighted_cleanup_le (L : Nat) (hL : 1 ≤ L) (T : NNReal) :
    (∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L,
      cleanupContribution L (ClippedProtectedGeometry.protectedSites L) (u.toNNReal,z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) ≤
      ((L : Real) + 2) * (4 * L + 2) := by
  let D := ClippedDiamondGeometry.clippedDomain L
  let I := ClippedProtectedGeometry.protectedSites L
  let C : Real := (L : Real) + 2
  have hD : D ⊆ ClippedSquareCoordinates.centeredSites L :=
    ClippedSquareCoordinates.clippedDomain_subset_centeredSites L hL
  have hi (u : NNReal) := cleanup_sample_integrable L I u
  have hj (u : NNReal) := CumulativeCleanupBudget.rate_sample_integrable L
    (D := D) (I := I) (S := D) (Finset.Subset.refl _) hD u
  have hlocal (u : NNReal) :
      (∫ z : Sample L, cleanupContribution L I (u,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) ≤
      C * ∫ z : Sample L, CumulativeCleanupBudget.rate D I
        (ObservedPreState.beforeState L D I D u z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
    have h := integral_mono_ae (hi u) ((hj u).const_mul C)
      (Filter.Eventually.of_forall (fun z : Sample L =>
        cleanupRate_le L I (ObservedPreState.beforeState L D I D u z)))
    rw [integral_const_mul] at h
    exact h
  have htime := integral_mono_ae (cleanup_time_mean_integrable L I T)
    ((CumulativeCleanupBudget.time_mean_rate_integrable L (D := D) (I := I) (S := D)
      (Finset.Subset.refl _) hD T).const_mul C)
    (Filter.Eventually.of_forall (fun u : Real => hlocal u.toNNReal))
  rw [integral_const_mul] at htime
  exact htime.trans (mul_le_mul_of_nonneg_left
    (CumulativeCleanupBudget.actual_clipped_cleanup_rate_le L hL T) (by dsimp [C]; positivity))

end MathResearchAnalysis.WeightedAreaDynkin
