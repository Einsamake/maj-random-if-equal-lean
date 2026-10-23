module
public import MathResearchAnalysis.ActualAreaDynkin
public import MathResearchAnalysis.ClippedProtectedGeometry
set_option autoImplicit false
/-! The actual finite clock vertex rate equals the D-site frozen generator
when the mask is represented in the finite clock square. The concrete clipped
mask supplies this coverage from existing geometry, rather than a probability
or compensation premise. Every real-time mean is integrable before it is used.
No geometric drift estimate or quadratic recovery bound is asserted. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.PhysicalAreaGenerator
open MeasureTheory
open DropletClockLaw (Sample Vertex)
open InfiniteGridModel (Site)

theorem stoppedStep_of_not_mem (D I U : Finset Site) (x : Site) (b : Bool)
    (hx : x ∉ D) : DropletStoppedWord.stoppedStep D I U (x,b) = U := by
  unfold DropletStoppedWord.stoppedStep
  split_ifs
  · exact DropletModifiedWord.modifiedStep_of_not_mem D U x b hx
  · rfl

theorem finite_vertex_generator_eq (L : Nat) (D I U : Finset Site)
    (f : Finset Site → Real) (hD : D ⊆ ClippedSquareCoordinates.centeredSites L) :
    (1 / 2 : Real) * ∑ v : Vertex L, ∑ b : Bool,
      (f (DropletStoppedWord.stoppedStep D I U (ClippedSquareCoordinates.recenter L v,b)) - f U) =
      MaskedAreaGenerator.frozenGenerator D I U f := by
  classical
  let g : Site → Real := fun x =>
    (f (DropletStoppedWord.stoppedStep D I U (x,false)) +
      f (DropletStoppedWord.stoppedStep D I U (x,true))) / 2 - f U
  have hzero (x : Site) (hx : x ∉ D) : g x = 0 := by
    dsimp [g]
    rw [stoppedStep_of_not_mem D I U x false hx,
      stoppedStep_of_not_mem D I U x true hx]
    ring
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
    _ = _ := rfl

theorem area_rate_eq_generator (L : Nat) (D I S : Finset Site)
    (hD : D ⊆ ClippedSquareCoordinates.centeredSites L) (p : NNReal × Sample L) :
    (1 / 2 : Real) * ∑ v : Vertex L, ∑ b : Bool,
      PredictableAreaContribution.increment L D I S v b p =
    MaskedAreaGenerator.frozenGenerator D I
      (ObservedPreState.beforeState L D I S p.1 p.2)
      (fun U => ((D \ U).card : Real)) := by
  simpa only [PredictableAreaContribution.increment] using
    finite_vertex_generator_eq L D I
      (ObservedPreState.beforeState L D I S p.1 p.2)
      (fun U : Finset Site => ((D \ U).card : Real)) hD

theorem clipped_area_rate_eq_generator (L : Nat) (hL : 1 ≤ L) (p : NNReal × Sample L) :
    (1 / 2 : Real) * ∑ v : Vertex L, ∑ b : Bool,
      PredictableAreaContribution.increment L (ClippedDiamondGeometry.clippedDomain L)
        (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L) v b p =
    MaskedAreaGenerator.frozenGenerator (ClippedDiamondGeometry.clippedDomain L)
      (ClippedProtectedGeometry.protectedSites L)
      (ObservedPreState.beforeState L (ClippedDiamondGeometry.clippedDomain L)
        (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L) p.1 p.2)
      (fun U => (((ClippedDiamondGeometry.clippedDomain L) \ U).card : Real)) :=
  area_rate_eq_generator L _ _ _
    (ClippedSquareCoordinates.clippedDomain_subset_centeredSites L hL) p

theorem generator_sample_integrable (L : Nat) (D I S : Finset Site)
    (hD : D ⊆ ClippedSquareCoordinates.centeredSites L) (u : NNReal) :
    Integrable (fun z : Sample L => MaskedAreaGenerator.frozenGenerator D I
      (ObservedPreState.beforeState L D I S u z) (fun U => ((D \ U).card : Real)))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  have hi (v : Vertex L) (b : Bool) : Integrable (fun z : Sample L =>
      PredictableAreaContribution.increment L D I S v b (u,z))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
    RealPredictableCompensation.sample_integrable L _
      ((PredictableAreaContribution.increment_stronglyMeasurable L D I S v b).mono
        (PredictableClockSigma.predictable_le_ambient L))
      (D.card : Real) (PredictableAreaContribution.increment_norm_le L D I S v b) u
  have hs := integrable_finsetSum Finset.univ (fun v _ =>
    integrable_finsetSum Finset.univ (fun b _ => hi v b))
  apply (hs.const_mul (1 / 2 : Real)).congr
  exact Filter.Eventually.of_forall (fun z => area_rate_eq_generator L D I S hD (u,z))

theorem expected_rate_eq_generator (L : Nat) (D I S : Finset Site)
    (hD : D ⊆ ClippedSquareCoordinates.centeredSites L) (u : NNReal) :
    (1 / 2 : Real) * ∑ v : Vertex L, ∑ b : Bool,
      ∫ z : Sample L, PredictableAreaContribution.increment L D I S v b (u,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) =
    ∫ z : Sample L, MaskedAreaGenerator.frozenGenerator D I
      (ObservedPreState.beforeState L D I S u z) (fun U => ((D \ U).card : Real))
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  have hi (v : Vertex L) (b : Bool) : Integrable (fun z : Sample L =>
      PredictableAreaContribution.increment L D I S v b (u,z))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
    RealPredictableCompensation.sample_integrable L _
      ((PredictableAreaContribution.increment_stronglyMeasurable L D I S v b).mono
        (PredictableClockSigma.predictable_le_ambient L))
      (D.card : Real) (PredictableAreaContribution.increment_norm_le L D I S v b) u
  have hs : (∫ z : Sample L, ∑ v : Vertex L, ∑ b : Bool,
      PredictableAreaContribution.increment L D I S v b (u,z)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      ∑ v : Vertex L, ∑ b : Bool, ∫ z : Sample L,
        PredictableAreaContribution.increment L D I S v b (u,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
    rw [integral_finsetSum _ (fun v _ => integrable_finsetSum _ (fun b _ => hi v b))]
    apply Finset.sum_congr rfl
    intro v _
    exact integral_finsetSum _ (fun b _ => hi v b)
  rw [← hs, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (fun z => area_rate_eq_generator L D I S hD (u,z)))

theorem generator_time_mean_integrable (L : Nat) (D I S : Finset Site)
    (hD : D ⊆ ClippedSquareCoordinates.centeredSites L) (T : NNReal) :
    Integrable (fun u : Real => ∫ z : Sample L, MaskedAreaGenerator.frozenGenerator D I
      (ObservedPreState.beforeState L D I S u.toNNReal z) (fun U => ((D \ U).card : Real))
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L))
      ((volume : Measure Real).restrict (Set.Ioc 0 (T : Real))) := by
  have hs := integrable_finsetSum Finset.univ (fun v _ =>
    integrable_finsetSum Finset.univ (fun b _ =>
      ActualAreaDynkin.time_mean_increment_integrable L D I S v b T))
  apply (hs.const_mul (1 / 2 : Real)).congr
  exact Filter.Eventually.of_forall
    (fun u => expected_rate_eq_generator L D I S hD u.toNNReal)

theorem area_change_dynkin_generator (L : Nat) (D I S : Finset Site)
    (hD : D ⊆ ClippedSquareCoordinates.centeredSites L) (T : NNReal) :
    (∫ z : Sample L,
      ((D \ DropletStoppedClockLaw.stateAt L D I S (T : Real) z).card : Real) -
        ((D \ S).card : Real)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    ∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L,
      MaskedAreaGenerator.frozenGenerator D I
        (ObservedPreState.beforeState L D I S u.toNNReal z)
        (fun U => ((D \ U).card : Real))
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  rw [ActualAreaDynkin.area_change_dynkin_single_integral, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (fun u => expected_rate_eq_generator L D I S hD u.toNNReal))

theorem actual_clipped_area_dynkin (L : Nat) (hL : 1 ≤ L) (T : NNReal) :
    (∫ z : Sample L, (((ClippedDiamondGeometry.clippedDomain L) \
      DropletStoppedClockLaw.stateAt L (ClippedDiamondGeometry.clippedDomain L)
        (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L)
        (T : Real) z).card : Real)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    ∫ u : Real in Set.Ioc 0 (T : Real), ∫ z : Sample L,
      MaskedAreaGenerator.frozenGenerator (ClippedDiamondGeometry.clippedDomain L)
        (ClippedProtectedGeometry.protectedSites L)
        (ObservedPreState.beforeState L (ClippedDiamondGeometry.clippedDomain L)
          (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L)
          u.toNNReal z)
        (fun U => (((ClippedDiamondGeometry.clippedDomain L) \ U).card : Real))
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  simpa only [Finset.sdiff_self,Finset.card_empty,Nat.cast_zero,sub_zero] using
    area_change_dynkin_generator L (ClippedDiamondGeometry.clippedDomain L)
      (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L)
      (ClippedSquareCoordinates.clippedDomain_subset_centeredSites L hL) T

theorem actual_clipped_generator_raw_cleanup (L : Nat) (p : NNReal × Sample L) :
    MaskedAreaGenerator.frozenGenerator (ClippedDiamondGeometry.clippedDomain L)
      (ClippedProtectedGeometry.protectedSites L)
      (ObservedPreState.beforeState L (ClippedDiamondGeometry.clippedDomain L)
        (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L) p.1 p.2)
      (fun U => (((ClippedDiamondGeometry.clippedDomain L) \ U).card : Real)) =
    if ClippedProtectedGeometry.protectedSites L ⊆ ObservedPreState.beforeState L
      (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L)
      (ClippedDiamondGeometry.clippedDomain L) p.1 p.2
    then MaskedAreaGenerator.rawAreaRate (ClippedDiamondGeometry.clippedDomain L)
      (ObservedPreState.beforeState L (ClippedDiamondGeometry.clippedDomain L)
        (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L) p.1 p.2) +
      MaskedAreaGenerator.cleanupRate (ClippedDiamondGeometry.clippedDomain L)
      (ObservedPreState.beforeState L (ClippedDiamondGeometry.clippedDomain L)
        (ClippedProtectedGeometry.protectedSites L) (ClippedDiamondGeometry.clippedDomain L) p.1 p.2)
    else 0 :=
  ProtectedAreaPotential.missing_area_generator
    (ObservedPreState.state_supported L (ClippedDiamondGeometry.clippedDomain L)
      (ClippedProtectedGeometry.protectedSites L) (Finset.Subset.refl _) p.1 p.2)

end MathResearchAnalysis.PhysicalAreaGenerator
