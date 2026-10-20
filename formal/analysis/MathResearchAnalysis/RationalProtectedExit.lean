module
public import MathResearchAnalysis.MarkedHistoryWords
public import MathResearchAnalysis.FrozenPhysicalExit
set_option autoImplicit false
/-! A genuine stopping-time version of the extended physical protected exit. The filtration is explicitly the right continuation of the joint observed history, not an all-future constant filtration. The version is proved equal to the original physicalExit almost surely, retaining infinity. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.RationalProtectedExit
open MeasureTheory
open DropletClockLaw (Sample Event)

def nnHistory (L : Nat) : Filtration NNReal (inferInstance : MeasurableSpace (Sample L)) where
  seq t := MarkedClockFiltration.history L (t : Real)
  mono' s t hst := (MarkedClockFiltration.history L).mono (by exact_mod_cast hst)
  le' t := (MarkedClockFiltration.history L).le (t : Real)

def rightHistory (L : Nat) : Filtration NNReal (inferInstance : MeasurableSpace (Sample L)) :=
  (nnHistory L).rightCont

def rationalExit (L : Nat) (D I S : Finset InfiniteGridModel.Site) (z : Sample L) : ENNReal :=
  sInf {r | ∃ q : Rat, 0 ≤ (q : Real) ∧ z ∈ MarkedHistoryWords.observedLoss L D I S (q : Real) ∧
    r = ENNReal.ofReal (q : Real)}

theorem rationalExit_le_of_observed (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (z : Sample L) (q : Rat) (hq : 0 ≤ (q : Real))
    (hl : z ∈ MarkedHistoryWords.observedLoss L D I S (q : Real)) :
    rationalExit L D I S z ≤ ENNReal.ofReal (q : Real) := sInf_le ⟨q,hq,hl,rfl⟩

theorem rationalExit_lt_iff (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (z : Sample L) (t : NNReal) : rationalExit L D I S z < (t : ENNReal) ↔
    ∃ q : Rat, 0 ≤ (q : Real) ∧ z ∈ MarkedHistoryWords.observedLoss L D I S (q : Real) ∧
      ENNReal.ofReal (q : Real) < (t : ENNReal) := by
  rw [rationalExit,sInf_lt_iff]
  constructor
  · rintro ⟨r,⟨q,hq,hl,rfl⟩,hr⟩
    exact ⟨q,hq,hl,hr⟩
  · rintro ⟨q,hq,hl,hqt⟩
    exact ⟨ENNReal.ofReal (q : Real),⟨q,hq,hl,rfl⟩,hqt⟩

theorem rationalExit_strict_event_measurable (L : Nat) (D I S : Finset InfiniteGridModel.Site) (t : NNReal) :
    MeasurableSet[nnHistory L t] {z | rationalExit L D I S z < (t : ENNReal)} := by
  let : MeasurableSpace (Sample L) := nnHistory L t
  have heq : {z : Sample L | rationalExit L D I S z < (t : ENNReal)} =
      ⋃ q : Rat, ⋃ (hq : 0 ≤ (q : Real)), ⋃ (_ : ENNReal.ofReal (q : Real) < (t : ENNReal)),
        MarkedHistoryWords.observedLoss L D I S (q : Real) := by
    ext z
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,rationalExit_lt_iff]
    constructor
    · rintro ⟨q,hq,hl,hqt⟩
      exact ⟨q,hq,hqt,hl⟩
    · rintro ⟨q,hq,hqt,hl⟩
      exact ⟨q,hq,hl,hqt⟩
  rw [heq]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => MeasurableSet.iUnion fun hqt =>
    (MarkedClockFiltration.history L).mono ((ENNReal.ofReal_lt_coe_iff hq).mp hqt).le _
      (MarkedHistoryWords.observedLoss_measurable L D I S (q : Real))

theorem rationalExit_isStoppingTime (L : Nat) (D I S : Finset InfiniteGridModel.Site) :
    IsStoppingTime (rightHistory L) (rationalExit L D I S) := by
  change IsStoppingTime ((nnHistory L).rightCont) _
  apply isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  intro t
  exact (nnHistory L).le_rightCont t _ (rationalExit_strict_event_measurable L D I S t)

theorem rationalExit_measurable (L : Nat) (D I S : Finset InfiniteGridModel.Site) :
    Measurable (rationalExit L D I S) := (rationalExit_isStoppingTime L D I S).measurable'

theorem rationalExit_eq_physicalExit (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (z : Sample L) (hg : ∀ t : Real, ClockEventWord.Good z.1 t) :
    rationalExit L D I S z = FrozenPhysicalExit.physicalExit L D I S z := by
  have hlower : FrozenPhysicalExit.physicalExit L D I S z ≤ rationalExit L D I S z := by
    apply le_sInf
    rintro r ⟨q,hq,hl,rfl⟩
    exact (FrozenPhysicalExit.physicalExit_le_iff L D I S z hg hq).mpr
      ((MarkedHistoryWords.observedLoss_iff L D I S (q : Real) z (hg (q : Real))).mp hl)
  apply le_antisymm ?_ hlower
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  by_cases hbtop : b = ⊤
  · rw [hbtop]
    exact le_top
  · have hfin : FrozenPhysicalExit.physicalExit L D I S z ≠ ⊤ := ne_top_of_lt hb
    have hreal : (FrozenPhysicalExit.physicalExit L D I S z).toReal < b.toReal :=
      (ENNReal.toReal_lt_toReal hfin hbtop).mpr hb
    obtain ⟨q,hq1,hq2⟩ := exists_rat_btwn hreal
    have hq : 0 ≤ (q : Real) := ENNReal.toReal_nonneg.trans hq1.le
    have hlt : FrozenPhysicalExit.physicalExit L D I S z < ENNReal.ofReal (q : Real) := by
      rw [← ENNReal.ofReal_toReal hfin]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mpr hq1
    have hloss := (FrozenPhysicalExit.physicalExit_le_iff L D I S z hg hq).mp hlt.le
    have hobs := (MarkedHistoryWords.observedLoss_iff L D I S (q : Real) z (hg (q : Real))).mpr hloss
    have hbq : ENNReal.ofReal (q : Real) ≤ b := by
      rw [← ENNReal.ofReal_toReal hbtop]
      exact ENNReal.ofReal_le_ofReal hq2.le
    exact (rationalExit_le_of_observed L D I S z q hq hobs).trans hbq

theorem rationalExit_ae_eq_physicalExit (L : Nat) (D I S : Finset InfiniteGridModel.Site) :
    rationalExit L D I S =ᵐ[ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)]
      FrozenPhysicalExit.physicalExit L D I S := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L] with z hz
  exact rationalExit_eq_physicalExit L D I S z hz

theorem physicalExit_aemeasurable (L : Nat) (D I S : Finset InfiniteGridModel.Site) :
    AEMeasurable (FrozenPhysicalExit.physicalExit L D I S)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  (rationalExit_measurable L D I S).aemeasurable.congr (rationalExit_ae_eq_physicalExit L D I S)

theorem exit_law_equal (L : Nat) (D I S : Finset InfiniteGridModel.Site) :
    Measure.map (rationalExit L D I S) (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      Measure.map (FrozenPhysicalExit.physicalExit L D I S)
        (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  Measure.map_congr (rationalExit_ae_eq_physicalExit L D I S)

theorem extended_exit_mean_equal (L : Nat) (D I S : Finset InfiniteGridModel.Site) :
    ∫⁻ z, rationalExit L D I S z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) =
      ∫⁻ z, FrozenPhysicalExit.physicalExit L D I S z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) :=
  lintegral_congr_ae (rationalExit_ae_eq_physicalExit L D I S)

theorem original_extinction_measure_le_stopping_exit (L : Nat) (hL : 40 ≤ L) (t : Real) (ht : 0 ≤ t) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L) t
        (fun _ => true) z = fun _ => false} ≤
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | rationalExit L (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
        (ClippedDiamondGeometry.clippedDomain L) z ≤ ENNReal.ofReal t} := by
  have heq :
      {z | rationalExit L (ClippedDiamondGeometry.clippedDomain L)
        (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L) z ≤ ENNReal.ofReal t} =ᵐ[
          ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)]
      {z | FrozenPhysicalExit.physicalExit L (ClippedDiamondGeometry.clippedDomain L)
        (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L) z ≤ ENNReal.ofReal t} := by
    filter_upwards [rationalExit_ae_eq_physicalExit L (ClippedDiamondGeometry.clippedDomain L)
      (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L)] with z hz
    exact congrArg (fun r : ENNReal => r ≤ ENNReal.ofReal t) hz
  calc
    _ ≤ ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
        {z | FrozenPhysicalExit.physicalExit L (ClippedDiamondGeometry.clippedDomain L)
          (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L) z ≤ ENNReal.ofReal t} :=
      FrozenPhysicalExit.original_extinction_measure_le_physical_exit L hL t ht
    _ = _ := (measure_congr heq).symm
end MathResearchAnalysis.RationalProtectedExit
