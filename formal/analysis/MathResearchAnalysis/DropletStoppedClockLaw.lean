module
public import MathResearchAnalysis.DropletClockLaw
public import MathResearchAnalysis.DropletStoppedWord
public import MathResearchAnalysis.ProtectedGeometricGood
public import MathResearchAnalysis.ProtectedDomainClockComparison
set_option autoImplicit false
/-! The true first-loss-frozen finite restriction at a fixed physical clock time.
The original rate-one clocks, identity-indexed fair marks and exceptional total-word fallback are retained. Word-fiber factorization and countable mixture are derived, not assumed. This is not a cross-time stopping, strong Markov or generator theorem. For arbitrary D,I,S the output Config is only the finite restriction, not an assertion that the sets lie within that finite window. -/
@[expose] public noncomputable section
open MeasureTheory Set
namespace MathResearchAnalysis.DropletStoppedClockLaw
open DropletClockLaw (Vertex Event Config Sample markedEvents markedEvents_fixedVector)

def run (L : ℕ) (D I S : Finset InfiniteGridModel.Site)
    (events : List (Event L)) (η : Event L → Bool) : Config L :=
  ClippedSquareCoordinates.clippedConfig L
    (DropletStoppedWord.stoppedWord D I S (markedEvents L events η))

def freshRun (L : ℕ) (D I S : Finset InfiniteGridModel.Site)
    (events : List (Event L)) (ξ : Fin events.length → Bool) : Config L :=
  run L D I S events (ClockExecutionLaw.freshMarks events ξ)

theorem freshRun_fixedVector (L : ℕ) 
    (D I S : Finset InfiniteGridModel.Site) (events : List (Event L))
    (η : Event L → Bool) :
    freshRun L D I S events (ClockExecutionLaw.fixedVector events η) =
      run L D I S events η := by
  simp only [freshRun, run, markedEvents_fixedVector]

theorem freshRun_measurable (L : ℕ) 
    (D I S : Finset InfiniteGridModel.Site) (events : List (Event L)) :
    Measurable (freshRun L D I S events) := measurable_of_countable _

theorem fixedRun_measurable (L : ℕ) 
    (D I S : Finset InfiniteGridModel.Site) (events : List (Event L)) :
    Measurable (run L D I S events) := by
  have h := (freshRun_measurable L D I S events).comp
    (ClockExecutionLaw.fixedVector_measurable events)
  simpa only [Function.comp_def, freshRun_fixedVector] using h

/-- Actual physical time, with the same total word convention as the original process. -/
def endpoint (L : ℕ) (D I S : Finset InfiniteGridModel.Site)
    (t : ℝ) (z : Sample L) : Config L :=
  run L D I S (ClockEventWord.word z.1 t) z.2

theorem endpoint_measurable (L : ℕ) 
    (D I S : Finset InfiniteGridModel.Site) (t : ℝ) :
    Measurable (endpoint L D I S t) := by
  have hrun : Measurable (fun z : List (Event L) × FairMarks.Sample (Event L) =>
      run L D I S z.1 z.2) :=
    measurable_from_prod_countable_right fun events =>
      fixedRun_measurable L D I S events
  exact hrun.comp (((ClockEventWord.word_measurable t).comp measurable_fst).prodMk
    measurable_snd)

theorem endpoint_eq_freshRun (L : ℕ) 
    (D I S : Finset InfiniteGridModel.Site) (t : ℝ) (events : List (Event L))
    (z : Sample L) (hword : ClockEventWord.word z.1 t = events) :
    endpoint L D I S t z = freshRun L D I S events
      (ClockWordMarks.prefixMarks (ClippedSquareCoordinates.parameter L) t events.length z) := by
  rw [ClockExecutionLaw.prefixMarks_eq_fixedVector _ t events z hword,
    freshRun_fixedVector]
  simp only [endpoint, hword]

def freshExecutionLaw (L : ℕ) (D I S : Finset InfiniteGridModel.Site)
    (events : List (Event L)) : Measure (Config L) :=
  Measure.map (freshRun L D I S events) (FairMarks.vectorMeasure events.length)

instance freshExecutionLaw_probability (L : ℕ) 
    (D I S : Finset InfiniteGridModel.Site) (events : List (Event L)) :
    IsProbabilityMeasure (freshExecutionLaw L D I S events) := by
  unfold freshExecutionLaw
  infer_instance

theorem freshExecutionLaw_apply (L : ℕ) 
    (D I S : Finset InfiniteGridModel.Site) (events : List (Event L))
    (B : Set (Config L)) (hB : MeasurableSet B) :
    freshExecutionLaw L D I S events B = FairMarks.vectorMeasure events.length
      {ξ | freshRun L D I S events ξ ∈ B} :=
  Measure.map_apply (freshRun_measurable L D I S events) hB

/-- Joint law on a genuine word fiber; no conditional law is an input. -/
theorem endpoint_joint_measure (L : ℕ) 
    (D I S : Finset InfiniteGridModel.Site) (t : ℝ) (events : List (Event L))
    (E : Set (ExponentialClocks.Sample (Vertex L))) (hE : MeasurableSet E)
    (B : Set (Config L)) (hB : MeasurableSet B) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | z.1 ∈ E ∩ ClockExecutionLaw.wordFiber _ t events ∧
        endpoint L D I S t z ∈ B} =
      ExponentialClocks.clockMeasure (Vertex L)
        (E ∩ ClockExecutionLaw.wordFiber _ t events) *
          freshExecutionLaw L D I S events B := by
  let n := ClippedSquareCoordinates.parameter L
  let F := E ∩ ClockExecutionLaw.wordFiber n t events
  have hF : MeasurableSet F := hE.inter (ClockExecutionLaw.wordFiber_measurable n t events)
  have henough : F ∩ ClockWordMarks.enough n t events.length = F :=
    Set.inter_eq_left.mpr fun _ h => ClockExecutionLaw.wordFiber_subset_enough n t events h.2
  have hset : {z : Sample L | z.1 ∈ E ∩ ClockExecutionLaw.wordFiber n t events ∧
      endpoint L D I S t z ∈ B} =
      {z : Sample L | z.1 ∈ F ∩ ClockWordMarks.enough n t events.length ∧
        ClockWordMarks.prefixMarks n t events.length z ∈
          {ξ | freshRun L D I S events ξ ∈ B}} := by
    ext z
    rw [henough]
    change (z.1 ∈ F ∧ endpoint L D I S t z ∈ B) ↔
      (z.1 ∈ F ∧ freshRun L D I S events
        (ClockWordMarks.prefixMarks n t events.length z) ∈ B)
    constructor
    · rintro ⟨hclock, hout⟩
      exact ⟨hclock, (endpoint_eq_freshRun L D I S t events z hclock.2) ▸ hout⟩
    · rintro ⟨hclock, hout⟩
      exact ⟨hclock, (endpoint_eq_freshRun L D I S t events z hclock.2).symm ▸ hout⟩
  rw [hset, henough, freshExecutionLaw_apply L D I S events B hB]
  have h := ClockWordMarks.prefixMarks_joint_measure n t events.length F hF
    {ξ | freshRun L D I S events ξ ∈ B}
    ((freshRun_measurable L D I S events) hB)
  rw [henough] at h
  exact h

theorem endpoint_word_fiber_measure (L : ℕ) 
    (D I S : Finset InfiniteGridModel.Site) (t : ℝ) (events : List (Event L))
    (B : Set (Config L)) (hB : MeasurableSet B) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | z.1 ∈ ClockExecutionLaw.wordFiber _ t events ∧ endpoint L D I S t z ∈ B} =
      ExponentialClocks.clockMeasure (Vertex L) (ClockExecutionLaw.wordFiber _ t events) *
        freshExecutionLaw L D I S events B := by
  simpa only [Set.univ_inter] using endpoint_joint_measure L D I S t events
    Set.univ MeasurableSet.univ B hB

/-- The unconditional endpoint law is the countable mixture over actual clock words. -/
theorem endpoint_measure_mixture (L : ℕ) 
    (D I S : Finset InfiniteGridModel.Site) (t : ℝ)
    (B : Set (Config L)) (hB : MeasurableSet B) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | endpoint L D I S t z ∈ B} =
      ∑' events : List (Event L),
        ExponentialClocks.clockMeasure (Vertex L) (ClockExecutionLaw.wordFiber _ t events) *
          freshExecutionLaw L D I S events B := by
  let A := fun events : List (Event L) => {z : Sample L |
    z.1 ∈ ClockExecutionLaw.wordFiber _ t events ∧ endpoint L D I S t z ∈ B}
  have hA : ∀ events, MeasurableSet (A events) := fun events =>
    ((ClockExecutionLaw.wordFiber_measurable _ t events).preimage measurable_fst).inter
      ((endpoint_measurable L D I S t) hB)
  have hdisj : Pairwise (fun e f => Disjoint (A e) (A f)) := by
    intro e f hef
    apply Set.disjoint_left.mpr
    intro z hz hez
    exact hef (hz.1.symm.trans hez.1)
  have hunion : (⋃ events, A events) = {z | endpoint L D I S t z ∈ B} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨events, hevents⟩
      exact hevents.2
    · intro hz
      exact ⟨ClockEventWord.word z.1 t, rfl, hz⟩
  rw [← hunion, measure_iUnion hdisj hA]
  exact tsum_congr fun events => endpoint_word_fiber_measure L D I S t events B hB


def stateAt (L : Nat) (D I S : Finset InfiniteGridModel.Site) (t : Real) (z : Sample L) :
    Finset InfiniteGridModel.Site :=
  DropletStoppedWord.stoppedWord D I S (markedEvents L (ClockEventWord.word z.1 t) z.2)

theorem endpoint_eq_clippedConfig (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (t : Real) (z : Sample L) : endpoint L D I S t z = ClippedSquareCoordinates.clippedConfig L (stateAt L D I S t z) := rfl

theorem stateAt_eq_stoppedTrajectory (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (t : Real) (z : Sample L) (fallback : DropletModifiedWord.Event) :
    stateAt L D I S t z = DropletDomainComparison.stoppedTrajectory D S I
      (fun n => (markedEvents L (ClockEventWord.word z.1 t) z.2).getD n fallback)
      (markedEvents L (ClockEventWord.word z.1 t) z.2).length :=
  DropletStoppedWord.stoppedWord_eq_stoppedTrajectory D I S _ fallback

theorem stateAt_protected_iff (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (t : Real) (z : Sample L) :
    I ⊆ stateAt L D I S t z ↔ ∀ k ≤ (markedEvents L (ClockEventWord.word z.1 t) z.2).length,
      I ⊆ DropletModifiedWord.modifiedWord D S ((markedEvents L (ClockEventWord.word z.1 t) z.2).take k) :=
  DropletStoppedWord.stoppedWord_protected_iff D I S _

theorem stateAt_missing_iff (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (t : Real) (z : Sample L) :
    (¬ I ⊆ stateAt L D I S t z) ↔ ∃ k ≤ (markedEvents L (ClockEventWord.word z.1 t) z.2).length,
      ¬ I ⊆ DropletModifiedWord.modifiedWord D S ((markedEvents L (ClockEventWord.word z.1 t) z.2).take k) :=
  DropletStoppedWord.stoppedWord_missing_iff D I S _

theorem stateAt_geometricGood_before_loss {L : Nat} (hL : 2 ≤ L)
    {S : Finset InfiniteGridModel.Site} (hS : ProtectedEvolution.Shape S)
    (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L) (t : Real) (z : Sample L)
    (hkeep : ClippedProtectedGeometry.protectedSites L ⊆ stateAt L
      (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L) S t z) :
    ClippedInitialContour.GeometricGood L (stateAt L (ClippedDiamondGeometry.clippedDomain L)
      (ClippedProtectedGeometry.protectedSites L) S t z) := by
  let fallback : DropletModifiedWord.Event := ((0,0),false)
  rw [stateAt_eq_stoppedTrajectory L _ _ S t z fallback] at hkeep ⊢
  have hn := (DropletStoppedWord.stoppedTrajectory_protected_iff _ _ _ _ _).mp hkeep
  exact ProtectedGeometricGood.stoppedTrajectory_geometricGood_before_exit hL hS hclip _ _ hn

theorem actual_protected_present_iff (L : Nat) (hL : 40 ≤ L) (S : Finset InfiniteGridModel.Site)
    (t : Real) (z : Sample L) :
    (∀ v ∈ ProtectedDomainClockComparison.protectedVertices L,
      endpoint L (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L) S t z v = true) ↔
    ClippedProtectedGeometry.protectedSites L ⊆ stateAt L (ClippedDiamondGeometry.clippedDomain L)
      (ClippedProtectedGeometry.protectedSites L) S t z :=
  ProtectedDomainClockComparison.protected_present_iff L hL _

theorem actual_protected_survival_measure_mixture (L : Nat) (hL : 40 ≤ L)
    (S : Finset InfiniteGridModel.Site) (t : Real) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | ClippedProtectedGeometry.protectedSites L ⊆ stateAt L (ClippedDiamondGeometry.clippedDomain L)
        (ClippedProtectedGeometry.protectedSites L) S t z} =
    ∑' events : List (Event L),
      ExponentialClocks.clockMeasure (Vertex L) (ClockExecutionLaw.wordFiber _ t events) *
        freshExecutionLaw L (ClippedDiamondGeometry.clippedDomain L)
          (ClippedProtectedGeometry.protectedSites L) S events
          {g | ∀ v ∈ ProtectedDomainClockComparison.protectedVertices L, g v = true} := by
  have hset : {z : Sample L | ClippedProtectedGeometry.protectedSites L ⊆
      stateAt L (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L) S t z} =
      {z | ∀ v ∈ ProtectedDomainClockComparison.protectedVertices L,
        endpoint L (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L) S t z v = true} := by
    ext z
    exact (actual_protected_present_iff L hL S t z).symm
  rw [hset]
  simpa only [Set.mem_ofPred_eq] using endpoint_measure_mixture L
    (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L) S t
    {g | ∀ v ∈ ProtectedDomainClockComparison.protectedVertices L, g v = true}
    (Set.to_countable _).measurableSet

theorem original_extinction_measure_le_frozen_protected_missing (L : Nat) (hL : 40 ≤ L) (t : Real) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L) t
        (fun _ => true) z = fun _ => false} ≤
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | ¬ ClippedProtectedGeometry.protectedSites L ⊆ stateAt L (ClippedDiamondGeometry.clippedDomain L)
        (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L) t z} := by
  apply le_trans (ProtectedDomainClockComparison.original_extinction_measure_le_actual_set_missing L hL t)
  apply measure_mono
  intro z hz
  change ¬ ClippedProtectedGeometry.protectedSites L ⊆ DropletStoppedWord.stoppedWord _ _ _
    (markedEvents L (ClockEventWord.word z.1 t) z.2)
  rw [DropletStoppedWord.stoppedWord_missing_iff]
  exact ⟨(markedEvents L (ClockEventWord.word z.1 t) z.2).length,le_rfl,by simpa only [List.take_length,Set.mem_ofPred_eq] using hz⟩

theorem measurableSet_actual_protected_survival (L : Nat) (hL : 40 ≤ L)
    (S : Finset InfiniteGridModel.Site) (t : Real) :
    MeasurableSet {z : Sample L | ClippedProtectedGeometry.protectedSites L ⊆
      stateAt L (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L) S t z} := by
  have hB : MeasurableSet {g : Config L | ∀ v ∈ ProtectedDomainClockComparison.protectedVertices L, g v = true} :=
    (Set.to_countable _).measurableSet
  have hm := (endpoint_measurable L (ClippedDiamondGeometry.clippedDomain L)
    (ClippedProtectedGeometry.protectedSites L) S t) hB
  convert hm using 1
  ext z
  exact (actual_protected_present_iff L hL S t z).symm

theorem measurableSet_actual_protected_missing (L : Nat) (hL : 40 ≤ L)
    (S : Finset InfiniteGridModel.Site) (t : Real) :
    MeasurableSet {z : Sample L | ¬ ClippedProtectedGeometry.protectedSites L ⊆
      stateAt L (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L) S t z} :=
  (measurableSet_actual_protected_survival L hL S t).compl
end MathResearchAnalysis.DropletStoppedClockLaw
