module
public import MathResearchAnalysis.ClockWordConsistency
public import MathResearchAnalysis.ProtectedExitArea
set_option autoImplicit false
/-! Extended physical first-loss times and their exact one-time threshold law.
No filtration stopping-time or generator theorem is asserted. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.FrozenPhysicalExit
open MeasureTheory

def firstLossTime (loss : Real → Prop) : ENNReal :=
  sInf {r | ∃ t : Real, 0 ≤ t ∧ loss t ∧ r = ENNReal.ofReal t}

theorem firstLossTime_le_of_loss {loss : Real → Prop} {t : Real} (ht : 0 ≤ t) (hl : loss t) :
    firstLossTime loss ≤ ENNReal.ofReal t := sInf_le ⟨t,ht,hl,rfl⟩

theorem firstLossTime_le_iff (loss : Real → Prop)
    (hmono : ∀ s t : Real, 0 ≤ s → s ≤ t → loss s → loss t)
    (hright : ∀ t : Real, 0 ≤ t → ¬ loss t → ∃ b : Real, t < b ∧ ∀ u, t ≤ u → u < b → ¬ loss u)
    {t : Real} (ht : 0 ≤ t) : firstLossTime loss ≤ ENNReal.ofReal t ↔ loss t := by
  constructor
  · intro htime
    by_contra hnot
    obtain ⟨b,htb,hkeep⟩ := hright t ht hnot
    have hblower : ENNReal.ofReal b ≤ firstLossTime loss := by
      apply le_sInf
      rintro r ⟨u,hu,hl,rfl⟩
      apply ENNReal.ofReal_le_ofReal
      by_contra hbu
      have hub : u < b := lt_of_not_ge hbu
      by_cases hut : u ≤ t
      · exact hnot (hmono u t hu hut hl)
      · exact hkeep u (lt_of_not_ge hut).le hub hl
    have hbt : ENNReal.ofReal t < ENNReal.ofReal b :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).mpr htb
    exact (not_le_of_gt hbt) (hblower.trans htime)
  · exact firstLossTime_le_of_loss ht

theorem firstLossTime_eq_top_iff (loss : Real → Prop) :
    firstLossTime loss = ⊤ ↔ ∀ t : Real, 0 ≤ t → ¬ loss t := by
  constructor
  · intro htop t ht hl
    have hle := firstLossTime_le_of_loss ht hl
    rw [htop] at hle
    simp only [top_le_iff,ENNReal.ofReal_ne_top] at hle
  · intro hnone
    apply top_unique
    apply le_sInf
    rintro r ⟨t,ht,hl,_⟩
    exact False.elim (hnone t ht hl)

def physicalExit (L : Nat) (D I S : Finset InfiniteGridModel.Site) (z : DropletClockLaw.Sample L) : ENNReal :=
  firstLossTime (fun t => ¬ I ⊆ DropletStoppedClockLaw.stateAt L D I S t z)

theorem physicalExit_le_iff (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (z : DropletClockLaw.Sample L) (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    {t : Real} (ht : 0 ≤ t) : physicalExit L D I S z ≤ ENNReal.ofReal t ↔
      ¬ I ⊆ DropletStoppedClockLaw.stateAt L D I S t z := by
  apply firstLossTime_le_iff _ ?_ ?_ ht
  · intro s u _ hsu hl
    rw [ClockWordConsistency.frozen_loss_persistent L D I S z hsu (hg u) hl]
    exact hl
  · intro u _ hnot
    obtain ⟨b,hub,hkeep⟩ := ClockWordConsistency.stateAt_right_locally_constant L D I S z u (hg (u+1))
    refine ⟨b,hub,?_⟩
    intro v huv hvb
    simpa only [hkeep v huv hvb] using hnot

theorem physicalExit_le_iff_ae (L : Nat) (D I S : Finset InfiniteGridModel.Site) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L), ∀ t : Real, 0 ≤ t →
      (physicalExit L D I S z ≤ ENNReal.ofReal t ↔ ¬ I ⊆ DropletStoppedClockLaw.stateAt L D I S t z) := by
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L] with z hz
  exact fun _ ht => physicalExit_le_iff L D I S z hz ht

theorem physicalExit_eq_top_iff (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (z : DropletClockLaw.Sample L) : physicalExit L D I S z = ⊤ ↔
      ∀ t : Real, 0 ≤ t → I ⊆ DropletStoppedClockLaw.stateAt L D I S t z := by
  simpa only [physicalExit,not_not] using firstLossTime_eq_top_iff
    (fun t => ¬ I ⊆ DropletStoppedClockLaw.stateAt L D I S t z)

theorem actual_exit_event_ae (L : Nat) (t : Real) (ht : 0 ≤ t) :
    {z | physicalExit L (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
      (ClippedDiamondGeometry.clippedDomain L) z ≤ ENNReal.ofReal t} =ᵐ[
      ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)]
    {z | ¬ ClippedProtectedGeometry.protectedSites L ⊆ DropletStoppedClockLaw.stateAt L
      (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
      (ClippedDiamondGeometry.clippedDomain L) t z} := by
  filter_upwards [physicalExit_le_iff_ae L (ClippedDiamondGeometry.clippedDomain L)
    (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L)] with z hz
  exact propext (hz t ht)

theorem actual_exit_event_nullMeasurable (L : Nat) (hL : 40 ≤ L) (t : Real) (ht : 0 ≤ t) :
    NullMeasurableSet {z | physicalExit L (ClippedDiamondGeometry.clippedDomain L)
      (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L) z ≤ ENNReal.ofReal t}
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  (DropletStoppedClockLaw.measurableSet_actual_protected_missing L hL
    (ClippedDiamondGeometry.clippedDomain L) t).nullMeasurableSet.congr (actual_exit_event_ae L t ht).symm

theorem original_extinction_measure_le_physical_exit (L : Nat) (hL : 40 ≤ L) (t : Real) (ht : 0 ≤ t) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L) t
        (fun _ => true) z = fun _ => false} ≤
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | physicalExit L (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
        (ClippedDiamondGeometry.clippedDomain L) z ≤ ENNReal.ofReal t} := by
  rw [measure_congr (actual_exit_event_ae L t ht)]
  exact DropletStoppedClockLaw.original_extinction_measure_le_frozen_protected_missing L hL t

theorem quadratic_area_of_physical_exit_le (L : Nat) (hL : 40 ≤ L)
    (z : DropletClockLaw.Sample L) (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (t : Real) (ht : 0 ≤ t)
    (hexit : physicalExit L (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
      (ClippedDiamondGeometry.clippedDomain L) z ≤ ENNReal.ofReal t) :
    (L : Real)^2/1600 ≤ ((ClippedDiamondGeometry.clippedDomain L \
      DropletStoppedClockLaw.stateAt L (ClippedDiamondGeometry.clippedDomain L)
        (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L) t z).card : Real) := by
  have hm := (physicalExit_le_iff L _ _ _ z hg ht).mp hexit
  let fallback : DropletModifiedWord.Event := ((0,0),false)
  rw [DropletStoppedClockLaw.stateAt_eq_stoppedTrajectory L _ _ _ t z fallback] at hm ⊢
  have hn : DropletDomainComparison.exitTime _ _ _ _ ≤
      ((DropletClockLaw.markedEvents L (ClockEventWord.word z.1 t) z.2).length : ℕ∞) :=
    le_of_not_gt (fun h => hm ((DropletStoppedWord.stoppedTrajectory_protected_iff _ _ _ _ _).mpr h))
  exact ProtectedExitArea.actual_stopped_area_after_exit hL _ _ hn

theorem physicalExit_attained (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (z : DropletClockLaw.Sample L) (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hfin : physicalExit L D I S z ≠ ⊤) :
    ¬ I ⊆ DropletStoppedClockLaw.stateAt L D I S (physicalExit L D I S z).toReal z := by
  apply (physicalExit_le_iff L D I S z hg ENNReal.toReal_nonneg).mp
  rw [ENNReal.ofReal_toReal hfin]

theorem frozen_at_physical_exit (L : Nat) (D I S : Finset InfiniteGridModel.Site)
    (z : DropletClockLaw.Sample L) (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (hfin : physicalExit L D I S z ≠ ⊤) (t : Real) (ht : (physicalExit L D I S z).toReal ≤ t) :
    DropletStoppedClockLaw.stateAt L D I S t z =
      DropletStoppedClockLaw.stateAt L D I S (physicalExit L D I S z).toReal z :=
  ClockWordConsistency.frozen_loss_persistent L D I S z ht (hg t) (physicalExit_attained L D I S z hg hfin)

theorem geometricGood_before_physical_exit {L : Nat} (hL : 2 ≤ L)
    {S : Finset InfiniteGridModel.Site} (hS : ProtectedEvolution.Shape S)
    (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L) (z : DropletClockLaw.Sample L)
    (hg : ∀ t : Real, ClockEventWord.Good z.1 t) (t : Real) (ht : 0 ≤ t)
    (hbefore : ENNReal.ofReal t < physicalExit L (ClippedDiamondGeometry.clippedDomain L)
      (ClippedProtectedGeometry.protectedSites L) S z) :
    ClippedInitialContour.GeometricGood L (DropletStoppedClockLaw.stateAt L
      (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L) S t z) := by
  apply DropletStoppedClockLaw.stateAt_geometricGood_before_loss hL hS hclip t z
  by_contra hm
  exact (not_le_of_gt hbefore) ((physicalExit_le_iff L _ _ S z hg ht).mpr hm)

theorem actual_physicalExit_pos_ae (L : Nat) (hL : 40 ≤ L) :
    ∀ᵐ z ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L),
      0 < physicalExit L (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
        (ClippedDiamondGeometry.clippedDomain L) z := by
  filter_upwards [physicalExit_le_iff_ae L (ClippedDiamondGeometry.clippedDomain L)
    (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L),
    ClockWordConsistency.stateAt_zero_ae L (ClippedDiamondGeometry.clippedDomain L)
      (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L)] with z hz hzero
  apply lt_of_not_ge
  intro h
  have hm := (hz 0 le_rfl).mp (by simpa only [ENNReal.ofReal_zero] using h)
  rw [hzero] at hm
  exact hm (ClippedProtectedGeometry.protectedSites_subset_clippedDomain hL)

theorem physical_exit_measure_le_quadratic_area (L : Nat) (hL : 40 ≤ L) (t : Real) (ht : 0 ≤ t) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | physicalExit L (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
        (ClippedDiamondGeometry.clippedDomain L) z ≤ ENNReal.ofReal t} ≤
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | (L : Real)^2/1600 ≤ ((ClippedDiamondGeometry.clippedDomain L \
        DropletStoppedClockLaw.stateAt L (ClippedDiamondGeometry.clippedDomain L)
          (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L) t z).card : Real)} := by
  apply measure_mono_ae
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L] with z hz
  exact fun he => quadratic_area_of_physical_exit_le L hL z hz t ht he
end MathResearchAnalysis.FrozenPhysicalExit
