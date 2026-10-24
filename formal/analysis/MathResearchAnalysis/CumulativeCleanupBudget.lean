module
public import MathResearchAnalysis.ClippedPerimeterBudget
public import MathResearchAnalysis.MarkedAreaSum
set_option autoImplicit false
/-! Actual first-loss-frozen cleanup costs are paid by physical perimeter.
The clock scores use the true original-law predictable strict pre-event state.
This module does not bound forbidden births or prove quadratic recovery. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.CumulativeCleanupBudget
open MeasureTheory
open DropletClockLaw (Sample Event Vertex)
open InfiniteGridModel (Site)
open GridCellBoundary (perimeter)

/-- Cleanup deletion count, disabled after the first loss of protection. -/
def loss (D I U : Finset Site) (e : DropletModifiedWord.Event) : Nat :=
  if I ⊆ U then GridPerimeterDynamics.eventLoss D U e else 0

/-- Cumulative genuine cleanup count along the frozen word. -/
def wordLoss (D I U : Finset Site) : List DropletModifiedWord.Event → Nat
  | [] => 0
  | e :: w => loss D I U e + wordLoss D I (DropletStoppedWord.stoppedStep D I U e) w

theorem loss_of_not_mem (D I U : Finset Site) (e : DropletModifiedWord.Event)
    (he : e.1 ∉ D) : loss D I U e = 0 := by
  unfold loss
  split_ifs <;> simp [GridPerimeterDynamics.eventLoss_of_not_mem D U e he]

theorem step_budget (D I U : Finset Site) (e : DropletModifiedWord.Event) :
    perimeter (DropletStoppedWord.stoppedStep D I U e) + 2 * loss D I U e ≤ perimeter U := by
  unfold DropletStoppedWord.stoppedStep loss
  split_ifs with h
  · exact GridPerimeterDynamics.modifiedStep_perimeter_loss_budget D U e
  · omega

theorem word_budget (D I U : Finset Site) (w : List DropletModifiedWord.Event) :
    perimeter (DropletStoppedWord.stoppedWord D I U w) + 2 * wordLoss D I U w ≤ perimeter U := by
  induction w generalizing U with
  | nil => simp [wordLoss]
  | cons e w ih =>
    rw [DropletStoppedWord.stoppedWord_cons,wordLoss]
    have hhead := step_budget D I U e
    have htail := ih (DropletStoppedWord.stoppedStep D I U e)
    omega

theorem wordLoss_append (D I U : Finset Site) (w u : List DropletModifiedWord.Event) :
    wordLoss D I U (w ++ u) = wordLoss D I U w +
      wordLoss D I (DropletStoppedWord.stoppedWord D I U w) u := by
  induction w generalizing U with
  | nil => simp [wordLoss]
  | cons e w ih => simp only [List.cons_append,wordLoss,
      DropletStoppedWord.stoppedWord_cons,ih, Nat.add_assoc]

/-- A deterministic ordered-word identity, including the first losing event. -/
theorem loss_sum_ordered {α : Type*} (time : α → Real)
    (mark : α → DropletModifiedWord.Event) (D I U : Finset Site)
    (w : List α) (hw : w.Pairwise (fun a b => time b < time a)) :
    wordLoss D I U (w.reverse.map mark) =
      (w.map (fun e => loss D I
        (DropletStoppedWord.stoppedWord D I U
          ((w.filter (fun f => decide (time f < time e))).reverse.map mark)) (mark e))).sum := by
  classical
  induction w with
  | nil => simp [wordLoss]
  | cons e w ih =>
    obtain ⟨he,hw⟩ := List.pairwise_cons.mp hw
    have hfilter : (e :: w).filter (fun f => decide (time f < time e)) = w := by
      simp only [List.filter_cons,lt_self_iff_false,decide_false,Bool.false_eq_true,↓reduceIte]
      exact List.filter_eq_self.mpr (fun f hf => decide_eq_true (he f hf))
    have htail : w.map (fun f => loss D I
        (DropletStoppedWord.stoppedWord D I U
          (((e :: w).filter (fun g => decide (time g < time f))).reverse.map mark)) (mark f)) =
      w.map (fun f => loss D I
        (DropletStoppedWord.stoppedWord D I U
          ((w.filter (fun g => decide (time g < time f))).reverse.map mark)) (mark f)) := by
      apply List.map_congr_left
      intro f hf
      have hnot : ¬ time e < time f := not_lt_of_gt (he f hf)
      simp only [List.filter_cons,decide_eq_false hnot,Bool.false_eq_true,↓reduceIte]
    rw [List.reverse_cons,List.map_append,List.map_singleton,wordLoss_append,
      wordLoss,wordLoss,List.map_cons,List.sum_cons,hfilter,htail, ← ih hw]
    omega

def score (L : Nat) (D I S : Finset Site) (v : Vertex L) (b : Bool)
    (p : NNReal × Sample L) : Real :=
  loss D I (ObservedPreState.beforeState L D I S p.1 p.2)
    (ClippedSquareCoordinates.recenter L v,b)

theorem score_measurable (L : Nat) (D I S : Finset Site) (v : Vertex L) (b : Bool) :
    Measurable[(RationalProtectedExit.nnHistory L).predictable] (score L D I S v b) :=
  ObservedPreState.observable_measurable L D I S (fun U : Finset Site =>
    (loss D I U (ClippedSquareCoordinates.recenter L v,b) : Real))

theorem loss_le_card {D I U : Finset Site} (hUD : U ⊆ D) (e : DropletModifiedWord.Event) :
    loss D I U e ≤ D.card := by
  unfold loss
  split_ifs
  · exact (Nat.sub_le _ _).trans (Finset.card_le_card
      (DropletModifiedWord.maskedRawStep_supported hUD e.1 e.2))
  · omega

theorem score_norm_le (L : Nat) {D I S : Finset Site} (hSD : S ⊆ D)
    (v : Vertex L) (b : Bool) (p : NNReal × Sample L) :
    ‖score L D I S v b p‖ ≤ (D.card : Real) := by
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  change (loss D I (ObservedPreState.beforeState L D I S p.1 p.2)
    (ClippedSquareCoordinates.recenter L v,b) : Real) ≤ (D.card : Real)
  exact_mod_cast loss_le_card (I := I) (ObservedPreState.state_supported L D I hSD p.1 p.2)
    (ClippedSquareCoordinates.recenter L v,b)

theorem score_eq_horizon_filter (L : Nat) (D I S : Finset Site)
    (z : Sample L) (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e)
    (T : Real) (e : Event L) (he : e ∈ ClockEventWord.word z.1 T) :
    score L D I S e.1 (z.2 e) ((ClockEventWord.eventTime z.1 e).toNNReal,z) =
      (loss D I
        (DropletStoppedWord.stoppedWord D I S
          (((ClockEventWord.word z.1 T).filter
            (fun f => decide (ClockEventWord.eventTime z.1 f < ClockEventWord.eventTime z.1 e))).reverse.map
              (fun f => (ClippedSquareCoordinates.recenter L f.1,z.2 f))))
        (ClippedSquareCoordinates.recenter L e.1,z.2 e) : Real) := by
  unfold score
  rw [ActualPreState.beforeState_eq_strictStateAt L D I S z hg hp,
    Real.coe_toNNReal _ (hp e).le]
  unfold ActualPreState.strictStateAt DropletClockLaw.markedEvents
  rw [ActualAreaTelescope.strictWord_eq_filter_horizon z.1
    ((ClockEventWord.word_mem_iff z.1 T (hg T) e).mp he) (hg T)]

theorem score_word_sum_eq_loss (L : Nat) (D I S : Finset Site) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) (T : NNReal) :
    ((ClockEventWord.word z.1 (T : Real)).map (fun e =>
      score L D I S e.1 (z.2 e) ((ClockEventWord.eventTime z.1 e).toNNReal,z))).sum =
    (wordLoss D I S (DropletClockLaw.markedEvents L
      (ClockEventWord.word z.1 (T : Real)) z.2) : Real) := by
  unfold DropletClockLaw.markedEvents
  rw [loss_sum_ordered (ClockEventWord.eventTime z.1)
    (fun e : Event L => (ClippedSquareCoordinates.recenter L e.1,z.2 e)) D I S
    (ClockEventWord.word z.1 (T : Real))
    (ClockEventWord.word_strictly_decreasing z.1 (T : Real)),Nat.cast_list_sum]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  exact score_eq_horizon_filter L D I S z hg hp (T : Real) e he

def eventScore (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (e : Event L) : Real :=
  if 0 < ClockEventWord.eventTime z.1 e ∧ ClockEventWord.eventTime z.1 e ≤ (T : Real) then
    score L D I S e.1 (z.2 e)
      ((ClockEventWord.eventTime z.1 e).toNNReal,z)
  else 0

/-- Precisely one Boolean-mark window matches the identity's actual mark. -/
theorem bool_sum_term (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (v : Vertex L) (k : Nat) :
    (∑ b : Bool, RealPredictableCompensation.term L v b T
      (score L D I S v b) k z) =
      eventScore L D I S T z (v,k) := by
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
    eventScore L D I S T z e = 0 := by
  have hnot : ¬ ClockEventWord.eventTime z.1 e ≤ (T : Real) := by
    intro ht
    exact he (List.mem_toFinset.mpr ((ClockEventWord.word_mem_iff z.1 (T : Real) hg e).mpr ht))
  simp [eventScore,hnot]

/-- The genuine finite horizon word proves signed summability pathwise. -/
theorem eventScore_summable (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real)) :
    Summable (eventScore L D I S T z) :=
  summable_of_ne_finset_zero (s := (ClockEventWord.word z.1 (T : Real)).toFinset)
    (eventScore_zero_outside_word L D I S T z hg)

/-- Each actual site/mark series is supported on the finite projection of the
true word. This proves the hypothesis needed before exchanging sum orders. -/
theorem term_summable (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real))
    (v : Vertex L) (b : Bool) :
    Summable (fun k : Nat => RealPredictableCompensation.term L v b T
      (score L D I S v b) k z) := by
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
      (score L D I S v b) z) =
      ∑' e : Event L, eventScore L D I S T z e := by
  classical
  rw [(eventScore_summable L D I S T z hg).tsum_prod,tsum_fintype]
  apply Finset.sum_congr rfl
  intro v _
  unfold RealPredictableCompensation.pathSum
  rw [← Summable.tsum_finsetSum (s := Finset.univ)
    (f := fun b : Bool => fun k : Nat => RealPredictableCompensation.term L v b T
      (score L D I S v b) k z)
    (fun b _ => term_summable L D I S T z hg v b)]
  apply tsum_congr
  intro k
  exact bool_sum_term L D I S T z v k

theorem tsum_eventScore_eq_word_sum (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real))
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) :
    (∑' e : Event L, eventScore L D I S T z e) =
    ∑ e ∈ (ClockEventWord.word z.1 (T : Real)).toFinset,
      score L D I S e.1 (z.2 e)
        ((ClockEventWord.eventTime z.1 e).toNNReal,z) := by
  classical
  rw [tsum_eq_sum (s := (ClockEventWord.word z.1 (T : Real)).toFinset)
    (eventScore_zero_outside_word L D I S T z hg)]
  apply Finset.sum_congr rfl
  intro e he
  have ht := (ClockEventWord.word_mem_iff z.1 (T : Real) hg e).mp (List.mem_toFinset.mp he)
  change ClockEventWord.eventTime z.1 e ≤ (T : Real) at ht
  simp only [eventScore,hp e,ht,and_self,↓reduceIte]

theorem sum_pathSums_eq_word_sum (L : Nat) (D I S : Finset Site) (T : NNReal)
    (z : Sample L) (hg : ClockEventWord.Good z.1 (T : Real))
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) :
    (∑ v : Vertex L, ∑ b : Bool, RealPredictableCompensation.pathSum L v b T
      (score L D I S v b) z) =
    ∑ e ∈ (ClockEventWord.word z.1 (T : Real)).toFinset,
      score L D I S e.1 (z.2 e)
        ((ClockEventWord.eventTime z.1 e).toNNReal,z) :=
  (sum_pathSums_eq_tsum_eventScore L D I S T z hg).trans
    (tsum_eventScore_eq_word_sum L D I S T z hg hp)


/-- The true pathwise cleanup sum, including the first losing event. -/
theorem pathSum_eq_loss (L : Nat) (D I S : Finset Site) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) (T : NNReal) :
    (∑ v : Vertex L, ∑ b : Bool, RealPredictableCompensation.pathSum L v b T
      (score L D I S v b) z) =
    (wordLoss D I S (DropletClockLaw.markedEvents L
      (ClockEventWord.word z.1 (T : Real)) z.2) : Real) := by
  rw [sum_pathSums_eq_word_sum L D I S T z (hg _) hp,
    ← ActualAreaTelescope.sum_map_eq_sum_toFinset _ (ClockEventWord.word_nodup z.1 (T : Real))]
  exact score_word_sum_eq_loss L D I S z hg hp T

theorem pathSum_le (L : Nat) (D I S : Finset Site) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hp : ∀ e : Event L, 0 < ClockEventWord.eventTime z.1 e) (T : NNReal) :
    (∑ v : Vertex L, ∑ b : Bool, RealPredictableCompensation.pathSum L v b T
      (score L D I S v b) z) ≤ (perimeter S : Real) / 2 := by
  rw [pathSum_eq_loss L D I S z hg hp T]
  have h := word_budget D I S (DropletClockLaw.markedEvents L
    (ClockEventWord.word z.1 (T : Real)) z.2)
  have h' : 2 * wordLoss D I S (DropletClockLaw.markedEvents L
      (ClockEventWord.word z.1 (T : Real)) z.2) ≤ perimeter S := by omega
  have hr : (2 : Real) * (wordLoss D I S (DropletClockLaw.markedEvents L
      (ClockEventWord.word z.1 (T : Real)) z.2) : Real) ≤ (perimeter S : Real) := by exact_mod_cast h'
  linarith

theorem marked_pathSum_integrable (L : Nat) {D I S : Finset Site} (hSD : S ⊆ D)
    (v : Vertex L) (b : Bool) (T : NNReal) :
    Integrable (RealPredictableCompensation.pathSum L v b T (score L D I S v b))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  RealPredictableCompensation.bounded_predictable_integrable L v b T
    (score L D I S v b) (score_measurable L D I S v b).stronglyMeasurable
    (D.card : Real) (score_norm_le L hSD v b)

theorem total_pathSum_integrable (L : Nat) {D I S : Finset Site} (hSD : S ⊆ D) (T : NNReal) :
    Integrable (fun z : Sample L => ∑ v : Vertex L, ∑ b : Bool,
      RealPredictableCompensation.pathSum L v b T (score L D I S v b) z)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  integrable_finsetSum _ fun v _ => integrable_finsetSum _ fun b _ =>
    marked_pathSum_integrable L hSD v b T

/-- A genuine original-law expectation bound, uniform in physical time. -/
theorem expected_cleanup_le (L : Nat) {D I S : Finset Site} (hSD : S ⊆ D) (T : NNReal) :
    (∫ z : Sample L, ∑ v : Vertex L, ∑ b : Bool,
      RealPredictableCompensation.pathSum L v b T (score L D I S v b) z
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) ≤ (perimeter S : Real) / 2 := by
  have h := integral_mono_ae (total_pathSum_integrable L hSD T)
    (integrable_const ((perimeter S : Real) / 2)) (by
      filter_upwards [ClockWordConsistency.marked_sample_good_ae L,
        ActualPreState.marked_all_events_positive_ae L] with z hg hp
      exact pathSum_le L D I S z hg hp T)
  simpa only [integral_const,probReal_univ,one_smul] using h

/-- The previously established compensation is instantiated with the actual
cleanup score rather than a core probability estimate supplied as an input. -/
theorem expected_cleanup_eq_compensator (L : Nat) {D I S : Finset Site} (hSD : S ⊆ D)
    (T : NNReal) :
    (∫ z : Sample L, ∑ v : Vertex L, ∑ b : Bool,
      RealPredictableCompensation.pathSum L v b T (score L D I S v b) z
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    ∑ v : Vertex L, ∑ b : Bool, (1 / 2 : Real) * ∫ u : Real in Set.Ioc 0 (T : Real),
      ∫ z : Sample L, score L D I S v b (u.toNNReal,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  rw [integral_finsetSum _ (fun v _ => integrable_finsetSum _
    (fun b _ => marked_pathSum_integrable L hSD v b T))]
  apply Finset.sum_congr rfl
  intro v _
  rw [integral_finsetSum _ (fun b _ => marked_pathSum_integrable L hSD v b T)]
  apply Finset.sum_congr rfl
  intro b _
  exact RealPredictableCompensation.bounded_predictable_integral_eq_time L v b T
    (score L D I S v b) (score_measurable L D I S v b).stronglyMeasurable
    (D.card : Real) (score_norm_le L hSD v b)

theorem cleanup_compensator_le (L : Nat) {D I S : Finset Site} (hSD : S ⊆ D) (T : NNReal) :
    (∑ v : Vertex L, ∑ b : Bool, (1 / 2 : Real) * ∫ u : Real in Set.Ioc 0 (T : Real),
      ∫ z : Sample L, score L D I S v b (u.toNNReal,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) ≤ (perimeter S : Real) / 2 := by
  rw [← expected_cleanup_eq_compensator L hSD T]
  exact expected_cleanup_le L hSD T

/-- The frozen D-site cleanup rate. -/
def rate (D I U : Finset Site) : Real :=
  if I ⊆ U then MaskedAreaGenerator.cleanupRate D U else 0

theorem finite_vertex_rate_eq (L : Nat) (D I U : Finset Site)
    (hD : D ⊆ ClippedSquareCoordinates.centeredSites L) :
    (1 / 2 : Real) * ∑ v : Vertex L, ∑ b : Bool,
      (loss D I U (ClippedSquareCoordinates.recenter L v,b) : Real) = rate D I U := by
  classical
  let g : Site → Real := fun x => ((loss D I U (x,false) : Real) +
    (loss D I U (x,true) : Real)) / 2
  have hzero (x : Site) (hx : x ∉ D) : g x = 0 := by
    simp [g,loss_of_not_mem D I U (x,false) hx,loss_of_not_mem D I U (x,true) hx]
  have hs : (∑ x ∈ D, g x) = ∑ x ∈ ClippedSquareCoordinates.centeredSites L, g x :=
    Finset.sum_subset hD (fun x _ hx => hzero x hx)
  calc
    _ = ∑ v : Vertex L, g (ClippedSquareCoordinates.recenter L v) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [Fintype.sum_bool]
      dsimp [g]
      ring
    _ = ∑ x ∈ ClippedSquareCoordinates.centeredSites L, g x := by
      rw [ClippedSquareCoordinates.centeredSites,
        Finset.sum_image (ClippedSquareCoordinates.recenter_injective L).injOn]
    _ = ∑ x ∈ D, g x := hs.symm
    _ = rate D I U := by
      unfold g loss rate
      split_ifs with h
      · rfl
      · simp

theorem time_mean_score_integrable (L : Nat) {D I S : Finset Site} (hSD : S ⊆ D)
    (v : Vertex L) (b : Bool) (T : NNReal) :
    Integrable (fun u : Real => ∫ z : Sample L, score L D I S v b (u.toNNReal,z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L))
      ((volume : Measure Real).restrict (Set.Ioc 0 (T : Real))) :=
  RealPredictableCompensation.time_mean_integrable L T (score L D I S v b)
    ((score_measurable L D I S v b).stronglyMeasurable.mono
      (PredictableClockSigma.predictable_le_ambient L))
    (D.card : Real) (score_norm_le L hSD v b)

theorem expected_rate_eq_score (L : Nat) {D I S : Finset Site} (hSD : S ⊆ D)
    (hD : D ⊆ ClippedSquareCoordinates.centeredSites L) (u : NNReal) :
    (1 / 2 : Real) * ∑ v : Vertex L, ∑ b : Bool,
      ∫ z : Sample L, score L D I S v b (u,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) =
    ∫ z : Sample L, rate D I (ObservedPreState.beforeState L D I S u z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  have hi (v : Vertex L) (b : Bool) := RealPredictableCompensation.sample_integrable L
    (score L D I S v b) ((score_measurable L D I S v b).stronglyMeasurable.mono
      (PredictableClockSigma.predictable_le_ambient L))
    (D.card : Real) (score_norm_le L hSD v b) u
  have hs : (∫ z : Sample L, ∑ v : Vertex L, ∑ b : Bool, score L D I S v b (u,z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      ∑ v : Vertex L, ∑ b : Bool, ∫ z : Sample L, score L D I S v b (u,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
    rw [integral_finsetSum _ (fun v _ => integrable_finsetSum _ (fun b _ => hi v b))]
    apply Finset.sum_congr rfl
    intro v _
    exact integral_finsetSum _ (fun b _ => hi v b)
  rw [← hs, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => finite_vertex_rate_eq L D I
    (ObservedPreState.beforeState L D I S u z) hD)


theorem rate_sample_integrable (L : Nat) {D I S : Finset Site} (hSD : S ⊆ D)
    (hD : D ⊆ ClippedSquareCoordinates.centeredSites L) (u : NNReal) :
    Integrable (fun z : Sample L => rate D I (ObservedPreState.beforeState L D I S u z))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  have hi := (integrable_finsetSum Finset.univ (fun v _ =>
    integrable_finsetSum Finset.univ (fun b _ =>
      RealPredictableCompensation.sample_integrable L (score L D I S v b)
        ((score_measurable L D I S v b).stronglyMeasurable.mono
          (PredictableClockSigma.predictable_le_ambient L))
        (D.card : Real) (score_norm_le L hSD v b) u))).const_mul (1 / 2 : Real)
  apply hi.congr
  exact Filter.Eventually.of_forall (fun z => finite_vertex_rate_eq L D I
    (ObservedPreState.beforeState L D I S u z) hD)

theorem time_mean_rate_integrable (L : Nat) {D I S : Finset Site} (hSD : S ⊆ D)
    (hD : D ⊆ ClippedSquareCoordinates.centeredSites L) (T : NNReal) :
    Integrable (fun u : Real => ∫ z : Sample L,
      rate D I (ObservedPreState.beforeState L D I S u.toNNReal z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L))
      ((volume : Measure Real).restrict (Set.Ioc 0 (T : Real))) := by
  have hi := (integrable_finsetSum Finset.univ (fun v _ =>
    integrable_finsetSum Finset.univ (fun b _ =>
      time_mean_score_integrable L (I := I) hSD v b T))).const_mul (1 / 2 : Real)
  apply hi.congr
  exact Filter.Eventually.of_forall (fun u => expected_rate_eq_score L hSD hD u.toNNReal)

/-- Cleanup's true cumulative predictable rate is paid by perimeter, uniformly
in the horizon. There is no assumed drift or compensation premise. -/
theorem time_integral_rate_le (L : Nat) {D I S : Finset Site} (hSD : S ⊆ D)
    (hD : D ⊆ ClippedSquareCoordinates.centeredSites L) (T : NNReal) :
    (∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L,
      rate D I (ObservedPreState.beforeState L D I S u.toNNReal z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) ≤ (perimeter S : Real) / 2 := by
  have hsum : (∫ u : Real in Set.Ioc 0 (T : Real), ∑ v : Vertex L, ∑ b : Bool,
      ∫ z : Sample L, score L D I S v b (u.toNNReal,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      ∑ v : Vertex L, ∑ b : Bool, ∫ u : Real in Set.Ioc 0 (T : Real),
        ∫ z : Sample L, score L D I S v b (u.toNNReal,z)
          ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
    rw [integral_finsetSum _ (fun v _ => integrable_finsetSum _
      (fun b _ => time_mean_score_integrable L (I := I) hSD v b T))]
    apply Finset.sum_congr rfl
    intro v _
    exact integral_finsetSum _ (fun b _ => time_mean_score_integrable L (I := I) hSD v b T)
  have heq : (∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L,
      rate D I (ObservedPreState.beforeState L D I S u.toNNReal z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      ∑ v : Vertex L, ∑ b : Bool, (1 / 2 : Real) * ∫ u : Real in Set.Ioc 0 (T : Real),
        ∫ z : Sample L, score L D I S v b (u.toNNReal,z)
          ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
    calc
      _ = ∫ u : Real in Set.Ioc 0 (T : Real), (1 / 2 : Real) * ∑ v : Vertex L, ∑ b : Bool,
          ∫ z : Sample L, score L D I S v b (u.toNNReal,z)
            ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun u => (expected_rate_eq_score L hSD hD u.toNNReal).symm)
      _ = _ := by rw [integral_const_mul,hsum]; simp only [Finset.mul_sum]
  rw [heq]
  exact cleanup_compensator_le L hSD T

/-- The concrete clipped droplet has physical perimeter 8L+4, hence its actual
cumulative cleanup contribution is at most 4L+2 for every physical horizon. -/
theorem actual_clipped_cleanup_rate_le (L : Nat) (hL : 1 ≤ L) (T : NNReal) :
    (∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L,
      rate (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
        (ObservedPreState.beforeState L (ClippedDiamondGeometry.clippedDomain L)
          (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L)
          u.toNNReal z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) ≤ (4 * L + 2 : Real) := by
  have h := time_integral_rate_le L (I := ClippedProtectedGeometry.protectedSites L)
    (S := ClippedDiamondGeometry.clippedDomain L) (Finset.Subset.refl _)
    (ClippedSquareCoordinates.clippedDomain_subset_centeredSites L hL) T
  rw [ClippedBoundaryPerimeter.physical_perimeter] at h
  push_cast at h
  linarith

end MathResearchAnalysis.CumulativeCleanupBudget
