module
public import MathResearchAnalysis.LocalObservedHistory
public import MathResearchAnalysis.MarkedStoppedResidual
set_option autoImplicit false
/-! The actual physical protected exit, bounded by a deterministic horizon, is a genuine stopping time for the original joint history and has the proved residual law. No almost-sure finiteness of the unbounded exit is assumed. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.ProtectedExitResidual
open MeasureTheory ProbabilityTheory
open DropletClockLaw (Sample Vertex)
open InfiniteGridModel (Site)

def boundedExit (L : Nat) (D I S : Finset Site) (T : NNReal) (z : Sample L) : WithTop Real :=
  ((min (LocalObservedHistory.exit L D I S z) (T : ENNReal)).toReal : WithTop Real)

theorem capped_exit_ne_top (L : Nat) (D I S : Finset Site) (T : NNReal) (z : Sample L) :
    min (LocalObservedHistory.exit L D I S z) (T : ENNReal) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)

theorem boundedExit_nonnegative (L : Nat) (D I S : Finset Site) (T : NNReal) (z : Sample L) :
    0 ≤ boundedExit L D I S T z := by
  change (0 : WithTop Real) ≤ ((min (LocalObservedHistory.exit L D I S z) (T : ENNReal)).toReal : WithTop Real)
  exact WithTop.coe_le_coe.mpr ENNReal.toReal_nonneg

theorem boundedExit_ne_top (L : Nat) (D I S : Finset Site) (T : NNReal) (z : Sample L) :
    boundedExit L D I S T z ≠ ⊤ := WithTop.coe_ne_top

theorem boundedExit_le_horizon (L : Nat) (D I S : Finset Site) (T : NNReal) (z : Sample L) :
    boundedExit L D I S T z ≤ ((T : Real) : WithTop Real) := by
  apply WithTop.coe_le_coe.mpr
  simpa only [ENNReal.coe_toReal] using
    ENNReal.toReal_mono ENNReal.coe_ne_top (min_le_right (LocalObservedHistory.exit L D I S z) (T : ENNReal))

theorem boundedExit_isStoppingTime (L : Nat) (D I S : Finset Site) (T : NNReal) :
    IsStoppingTime (MarkedClockFiltration.history L) (boundedExit L D I S T) := by
  intro r
  let : MeasurableSpace (Sample L) := MarkedClockFiltration.history L r
  simp only [boundedExit,WithTop.coe_le_coe]
  by_cases hr : 0 ≤ r
  · have heq : {z : Sample L | (min (LocalObservedHistory.exit L D I S z) (T : ENNReal)).toReal ≤ r} =
        {z | LocalObservedHistory.exit L D I S z ≤ ENNReal.ofReal r ∨ (T : ENNReal) ≤ ENNReal.ofReal r} := by
      ext z
      simp only [Set.mem_ofPred_eq]
      calc
        _ ↔ (min (LocalObservedHistory.exit L D I S z) (T : ENNReal)).toReal ≤ (ENNReal.ofReal r).toReal := by
          rw [ENNReal.toReal_ofReal hr]
        _ ↔ min (LocalObservedHistory.exit L D I S z) (T : ENNReal) ≤ ENNReal.ofReal r :=
          ENNReal.toReal_le_toReal (capped_exit_ne_top L D I S T z) ENNReal.ofReal_ne_top
        _ ↔ _ := min_le_iff
    rw [heq]
    by_cases hT : (T : ENNReal) ≤ ENNReal.ofReal r
    · have he : {z : Sample L | LocalObservedHistory.exit L D I S z ≤ ENNReal.ofReal r ∨
          (T : ENNReal) ≤ ENNReal.ofReal r} = Set.univ := by ext z; simp only [Set.mem_ofPred_eq,hT,or_true,Set.mem_univ]
      rw [he]
      exact MeasurableSet.univ
    · have he : {z : Sample L | LocalObservedHistory.exit L D I S z ≤ ENNReal.ofReal r ∨
          (T : ENNReal) ≤ ENNReal.ofReal r} = LocalObservedHistory.absorbingLoss L D I S r := by
        ext z
        simp only [Set.mem_ofPred_eq,hT,or_false]
        exact LocalObservedHistory.exit_le_iff L D I S z hr
      rw [he]
      exact LocalObservedHistory.absorbingLoss_measurable L D I S r
  · have he : {z : Sample L | (min (LocalObservedHistory.exit L D I S z) (T : ENNReal)).toReal ≤ r} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      exact not_le.mpr ((lt_of_not_ge hr).trans_le ENNReal.toReal_nonneg)
    rw [he]
    exact MeasurableSet.empty

theorem boundedExit_eq_capped_physicalExit (L : Nat) (D I S : Finset Site) (T : NNReal) (z : Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t) : boundedExit L D I S T z =
      ((min (FrozenPhysicalExit.physicalExit L D I S z) (T : ENNReal)).toReal : WithTop Real) := by
  unfold boundedExit
  rw [LocalObservedHistory.exit_eq_physicalExit L D I S z hg]

theorem boundedExit_ae_eq_capped_physicalExit (L : Nat) (D I S : Finset Site) (T : NNReal) :
    boundedExit L D I S T =ᵐ[ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)]
      (fun z => ((min (FrozenPhysicalExit.physicalExit L D I S z) (T : ENNReal)).toReal : WithTop Real)) := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L] with z hz
  exact boundedExit_eq_capped_physicalExit L D I S T z hz

theorem boundedExit_wait_hasLaw (L : Nat) (D I S : Finset Site) (T : NNReal) (v : Vertex L) :
    HasLaw (MarkedStoppedResidual.waiting L v (boundedExit L D I S T)) (expMeasure 1)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  MarkedStoppedResidual.waiting_hasLaw L v (boundedExit L D I S T)
    (boundedExit_isStoppingTime L D I S T) (boundedExit_nonnegative L D I S T)
    (Filter.Eventually.of_forall (boundedExit_ne_top L D I S T))

theorem boundedExit_wait_independent_stopped_history (L : Nat) (D I S : Finset Site) (T : NNReal) (v : Vertex L) :
    Indep ((borel Real).comap (MarkedStoppedResidual.waiting L v (boundedExit L D I S T)))
      (boundedExit_isStoppingTime L D I S T).measurableSpace
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  MarkedStoppedResidual.waiting_independent_stopped_history L v (boundedExit L D I S T)
    (boundedExit_isStoppingTime L D I S T) (boundedExit_nonnegative L D I S T)
    (Filter.Eventually.of_forall (boundedExit_ne_top L D I S T))
end MathResearchAnalysis.ProtectedExitResidual
