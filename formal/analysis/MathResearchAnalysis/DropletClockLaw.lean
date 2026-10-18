module

public import MathResearchAnalysis.ClockExecutionLaw
public import MathResearchAnalysis.CenteredPeelingTransport
public import MathResearchAnalysis.DropletDomainComparison

set_option autoImplicit false

/-!
# Actual marked-clock endpoint law for raw and cleaned droplets

The clocks have rate one per vertex. Their identity word is newest first;
execution reverses it once. Both executors read the same identity-indexed
fair field. The law is derived from that actual product measure, including
its null-set fallback, rather than postulated as a process law.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace MathResearchAnalysis.DropletClockLaw

abbrev Vertex (L : ℕ) := SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)
abbrev Event (L : ℕ) := SquareSpin.Event (ClippedSquareCoordinates.parameter L)
abbrev Config (L : ℕ) := SquareSpin.Config (ClippedSquareCoordinates.parameter L)
abbrev Sample (L : ℕ) := ClockWordMarks.Sample (ClippedSquareCoordinates.parameter L)

/-- Chronological events, retaining the original event identity when reading marks. -/
def markedEvents (L : ℕ) (events : List (Event L)) (η : Event L → Bool) :
    List DropletModifiedWord.Event :=
  events.reverse.map (fun e => (ClippedSquareCoordinates.recenter L e.1, η e))

/-- A finite restriction of the actual masked set-valued execution. -/
def run (L : ℕ) (modified : Bool) (D S : Finset InfiniteGridModel.Site)
    (events : List (Event L)) (η : Event L → Bool) : Config L :=
  ClippedSquareCoordinates.clippedConfig L
    (if modified then DropletModifiedWord.modifiedWord D S (markedEvents L events η)
      else DropletModifiedWord.rawWord D S (markedEvents L events η))

def freshRun (L : ℕ) (modified : Bool) (D S : Finset InfiniteGridModel.Site)
    (events : List (Event L)) (ξ : Fin events.length → Bool) : Config L :=
  run L modified D S events (ClockExecutionLaw.freshMarks events ξ)

theorem markedEvents_fixedVector (L : ℕ) (events : List (Event L))
    (η : Event L → Bool) :
    markedEvents L events
      (ClockExecutionLaw.freshMarks events (ClockExecutionLaw.fixedVector events η)) =
      markedEvents L events η := by
  apply List.map_congr_left
  intro e he
  rw [ClockExecutionLaw.freshMarks_fixedVector events η e (List.mem_reverse.mp he)]

theorem freshRun_fixedVector (L : ℕ) (modified : Bool)
    (D S : Finset InfiniteGridModel.Site) (events : List (Event L))
    (η : Event L → Bool) :
    freshRun L modified D S events (ClockExecutionLaw.fixedVector events η) =
      run L modified D S events η := by
  simp only [freshRun, run, markedEvents_fixedVector]

theorem freshRun_measurable (L : ℕ) (modified : Bool)
    (D S : Finset InfiniteGridModel.Site) (events : List (Event L)) :
    Measurable (freshRun L modified D S events) := measurable_of_countable _

theorem fixedRun_measurable (L : ℕ) (modified : Bool)
    (D S : Finset InfiniteGridModel.Site) (events : List (Event L)) :
    Measurable (run L modified D S events) := by
  have h := (freshRun_measurable L modified D S events).comp
    (ClockExecutionLaw.fixedVector_measurable events)
  simpa only [Function.comp_def, freshRun_fixedVector] using h

/-- Actual physical time, with the same total word convention as the original process. -/
def endpoint (L : ℕ) (modified : Bool) (D S : Finset InfiniteGridModel.Site)
    (t : ℝ) (z : Sample L) : Config L :=
  run L modified D S (ClockEventWord.word z.1 t) z.2

theorem endpoint_measurable (L : ℕ) (modified : Bool)
    (D S : Finset InfiniteGridModel.Site) (t : ℝ) :
    Measurable (endpoint L modified D S t) := by
  have hrun : Measurable (fun z : List (Event L) × FairMarks.Sample (Event L) =>
      run L modified D S z.1 z.2) :=
    measurable_from_prod_countable_right fun events =>
      fixedRun_measurable L modified D S events
  exact hrun.comp (((ClockEventWord.word_measurable t).comp measurable_fst).prodMk
    measurable_snd)

theorem endpoint_eq_freshRun (L : ℕ) (modified : Bool)
    (D S : Finset InfiniteGridModel.Site) (t : ℝ) (events : List (Event L))
    (z : Sample L) (hword : ClockEventWord.word z.1 t = events) :
    endpoint L modified D S t z = freshRun L modified D S events
      (ClockWordMarks.prefixMarks (ClippedSquareCoordinates.parameter L) t events.length z) := by
  rw [ClockExecutionLaw.prefixMarks_eq_fixedVector _ t events z hword,
    freshRun_fixedVector]
  simp only [endpoint, hword]

def freshExecutionLaw (L : ℕ) (modified : Bool) (D S : Finset InfiniteGridModel.Site)
    (events : List (Event L)) : Measure (Config L) :=
  Measure.map (freshRun L modified D S events) (FairMarks.vectorMeasure events.length)

instance freshExecutionLaw_probability (L : ℕ) (modified : Bool)
    (D S : Finset InfiniteGridModel.Site) (events : List (Event L)) :
    IsProbabilityMeasure (freshExecutionLaw L modified D S events) := by
  unfold freshExecutionLaw
  infer_instance

theorem freshExecutionLaw_apply (L : ℕ) (modified : Bool)
    (D S : Finset InfiniteGridModel.Site) (events : List (Event L))
    (B : Set (Config L)) (hB : MeasurableSet B) :
    freshExecutionLaw L modified D S events B = FairMarks.vectorMeasure events.length
      {ξ | freshRun L modified D S events ξ ∈ B} :=
  Measure.map_apply (freshRun_measurable L modified D S events) hB

/-- Joint law on a genuine word fiber; no conditional law is an input. -/
theorem endpoint_joint_measure (L : ℕ) (modified : Bool)
    (D S : Finset InfiniteGridModel.Site) (t : ℝ) (events : List (Event L))
    (E : Set (ExponentialClocks.Sample (Vertex L))) (hE : MeasurableSet E)
    (B : Set (Config L)) (hB : MeasurableSet B) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | z.1 ∈ E ∩ ClockExecutionLaw.wordFiber _ t events ∧
        endpoint L modified D S t z ∈ B} =
      ExponentialClocks.clockMeasure (Vertex L)
        (E ∩ ClockExecutionLaw.wordFiber _ t events) *
          freshExecutionLaw L modified D S events B := by
  let n := ClippedSquareCoordinates.parameter L
  let F := E ∩ ClockExecutionLaw.wordFiber n t events
  have hF : MeasurableSet F := hE.inter (ClockExecutionLaw.wordFiber_measurable n t events)
  have henough : F ∩ ClockWordMarks.enough n t events.length = F :=
    Set.inter_eq_left.mpr fun _ h => ClockExecutionLaw.wordFiber_subset_enough n t events h.2
  have hset : {z : Sample L | z.1 ∈ E ∩ ClockExecutionLaw.wordFiber n t events ∧
      endpoint L modified D S t z ∈ B} =
      {z : Sample L | z.1 ∈ F ∩ ClockWordMarks.enough n t events.length ∧
        ClockWordMarks.prefixMarks n t events.length z ∈
          {ξ | freshRun L modified D S events ξ ∈ B}} := by
    ext z
    rw [henough]
    change (z.1 ∈ F ∧ endpoint L modified D S t z ∈ B) ↔
      (z.1 ∈ F ∧ freshRun L modified D S events
        (ClockWordMarks.prefixMarks n t events.length z) ∈ B)
    constructor
    · rintro ⟨hclock, hout⟩
      exact ⟨hclock, (endpoint_eq_freshRun L modified D S t events z hclock.2) ▸ hout⟩
    · rintro ⟨hclock, hout⟩
      exact ⟨hclock, (endpoint_eq_freshRun L modified D S t events z hclock.2).symm ▸ hout⟩
  rw [hset, henough, freshExecutionLaw_apply L modified D S events B hB]
  have h := ClockWordMarks.prefixMarks_joint_measure n t events.length F hF
    {ξ | freshRun L modified D S events ξ ∈ B}
    ((freshRun_measurable L modified D S events) hB)
  rw [henough] at h
  exact h

theorem endpoint_word_fiber_measure (L : ℕ) (modified : Bool)
    (D S : Finset InfiniteGridModel.Site) (t : ℝ) (events : List (Event L))
    (B : Set (Config L)) (hB : MeasurableSet B) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | z.1 ∈ ClockExecutionLaw.wordFiber _ t events ∧ endpoint L modified D S t z ∈ B} =
      ExponentialClocks.clockMeasure (Vertex L) (ClockExecutionLaw.wordFiber _ t events) *
        freshExecutionLaw L modified D S events B := by
  simpa only [Set.univ_inter] using endpoint_joint_measure L modified D S t events
    Set.univ MeasurableSet.univ B hB

/-- The unconditional endpoint law is the countable mixture over actual clock words. -/
theorem endpoint_measure_mixture (L : ℕ) (modified : Bool)
    (D S : Finset InfiniteGridModel.Site) (t : ℝ)
    (B : Set (Config L)) (hB : MeasurableSet B) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | endpoint L modified D S t z ∈ B} =
      ∑' events : List (Event L),
        ExponentialClocks.clockMeasure (Vertex L) (ClockExecutionLaw.wordFiber _ t events) *
          freshExecutionLaw L modified D S events B := by
  let A := fun events : List (Event L) => {z : Sample L |
    z.1 ∈ ClockExecutionLaw.wordFiber _ t events ∧ endpoint L modified D S t z ∈ B}
  have hA : ∀ events, MeasurableSet (A events) := fun events =>
    ((ClockExecutionLaw.wordFiber_measurable _ t events).preimage measurable_fst).inter
      ((endpoint_measurable L modified D S t) hB)
  have hdisj : Pairwise (fun e f => Disjoint (A e) (A f)) := by
    intro e f hef
    apply Set.disjoint_left.mpr
    intro z hz hez
    exact hef (hz.1.symm.trans hez.1)
  have hunion : (⋃ events, A events) = {z | endpoint L modified D S t z ∈ B} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨events, hevents⟩
      exact hevents.2
    · intro hz
      exact ⟨ClockEventWord.word z.1 t, rfl, hz⟩
  rw [← hunion, measure_iUnion hdisj hA]
  exact tsum_congr fun events => endpoint_word_fiber_measure L modified D S t events B hB

/-- Identification with actual finite heat-bath followed by actual finite cleanup. -/
theorem modified_run_finite_execution (L : ℕ) (hL : 1 ≤ L)
    (g : Config L) (events : List (Event L)) (η : Event L → Bool) :
    run L true (ClippedDiamondGeometry.clippedDomain L)
      (CenteredPeelingTransport.image L (CenteredPeelingTransport.occupied g)) events η =
      CenteredPeelingTransport.finiteModifiedWord L g
        (events.reverse.map (fun e => (e.1, η e))) := by
  have h := CenteredPeelingTransport.recenterConfig_finiteModifiedWord_config L hL g
    (events.reverse.map (fun e => (e.1, η e)))
  have hmap : ((events.reverse.map (fun e => (e.1, η e))).map
      (fun e => (ClippedSquareCoordinates.recenter L e.1, e.2))) =
        markedEvents L events η := by simp [markedEvents, List.map_map]
  rw [hmap] at h
  funext v
  have hv := congrFun h (ClippedSquareCoordinates.recenter L v)
  rw [ClippedSquareCoordinates.recenterConfig_at_vertex] at hv
  exact hv.symm

theorem modified_endpoint_finite_execution (L : ℕ) (hL : 1 ≤ L)
    (g : Config L) (t : ℝ) (z : Sample L) :
    endpoint L true (ClippedDiamondGeometry.clippedDomain L)
      (CenteredPeelingTransport.image L (CenteredPeelingTransport.occupied g)) t z =
      CenteredPeelingTransport.finiteModifiedWord L g
        ((ClockEventWord.word z.1 t).reverse.map (fun e => (e.1, z.2 e))) :=
  modified_run_finite_execution L hL g _ _

/-- Same physical clocks and marks, allowing genuinely different masks. -/
theorem endpoint_true_imp_raw_true (L : ℕ) {D E S T : Finset InfiniteGridModel.Site}
    (hDE : D ⊆ E) (hSD : S ⊆ D) (hST : S ⊆ T)
    (t : ℝ) (z : Sample L) (v : Vertex L)
    (hv : endpoint L true D S t z v = true) :
    endpoint L false E T t z v = true := by
  have hsub := DropletDomainComparison.modifiedWord_subset_rawWord_of_domains
    hDE hSD hST (markedEvents L (ClockEventWord.word z.1 t) z.2)
  change decide (ClippedSquareCoordinates.recenter L v ∈
    DropletModifiedWord.modifiedWord D S _) = true at hv
  change decide (ClippedSquareCoordinates.recenter L v ∈
    DropletModifiedWord.rawWord E T _) = true
  exact decide_eq_true (hsub (of_decide_eq_true hv))

/-- Extinction of the larger raw endpoint forces a missing protected vertex now.
This does not assert domination of the frozen process after its exit. -/
theorem protected_missing_of_raw_endpoint_zero (L : ℕ)
    {D E S T : Finset InfiniteGridModel.Site} (hDE : D ⊆ E)
    (hSD : S ⊆ D) (hST : S ⊆ T) (I : Finset (Vertex L)) (hI : I.Nonempty)
    (t : ℝ) (z : Sample L) (hz : endpoint L false E T t z = fun _ => false) :
    ¬ ∀ v ∈ I, endpoint L true D S t z v = true := by
  intro hpresent
  obtain ⟨v, hv⟩ := hI
  have h := endpoint_true_imp_raw_true L hDE hSD hST t z v (hpresent v hv)
  rw [hz] at h
  contradiction

/-- Failure-event inequality at physical time t, from an actual product coupling. -/
theorem raw_extinction_measure_le_protected_missing (L : ℕ)
    {D E S T : Finset InfiniteGridModel.Site} (hDE : D ⊆ E)
    (hSD : S ⊆ D) (hST : S ⊆ T) (I : Finset (Vertex L)) (hI : I.Nonempty)
    (t : ℝ) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | endpoint L false E T t z = fun _ => false} ≤
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | ¬ ∀ v ∈ I, endpoint L true D S t z v = true} := by
  apply measure_mono
  intro z hz
  exact protected_missing_of_raw_endpoint_zero L hDE hSD hST I hI t z hz

end MathResearchAnalysis.DropletClockLaw
