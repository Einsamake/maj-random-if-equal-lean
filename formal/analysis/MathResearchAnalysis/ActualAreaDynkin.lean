module
public import MathResearchAnalysis.MarkedAreaSum
set_option autoImplicit false
/-! A genuine finite-horizon area Dynkin formula under the original joint law.
The physical area is integrable and its signed finite-site compensator is
identified from actual event words. No geometric drift or recovery bound is
an input. The finite vertex sum is not yet identified with a D-site generator. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.ActualAreaDynkin
open MeasureTheory
open DropletClockLaw (Sample Vertex)
open InfiniteGridModel (Site)

theorem marked_pathSum_integrable (L : Nat) (D I S : Finset Site)
    (v : Vertex L) (b : Bool) (T : NNReal) :
    Integrable (RealPredictableCompensation.pathSum L v b T
      (PredictableAreaContribution.increment L D I S v b))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) :=
  RealPredictableCompensation.bounded_predictable_integrable L v b T
    (PredictableAreaContribution.increment L D I S v b)
    (PredictableAreaContribution.increment_stronglyMeasurable L D I S v b)
    (D.card : Real) (PredictableAreaContribution.increment_norm_le L D I S v b)

theorem total_pathSum_integrable (L : Nat) (D I S : Finset Site) (T : NNReal) :
    Integrable (fun z : Sample L => ∑ v : Vertex L, ∑ b : Bool,
      RealPredictableCompensation.pathSum L v b T
        (PredictableAreaContribution.increment L D I S v b) z)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  exact integrable_finsetSum _ fun v _ => integrable_finsetSum _ fun b _ =>
    marked_pathSum_integrable L D I S v b T

theorem area_change_integrable (L : Nat) (D I S : Finset Site) (T : NNReal) :
    Integrable (fun z : Sample L =>
      ((D \ DropletStoppedClockLaw.stateAt L D I S (T : Real) z).card : Real) -
        ((D \ S).card : Real))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  apply (total_pathSum_integrable L D I S T).congr
  filter_upwards [MarkedAreaSum.area_eq_pathSums_all_times_ae L D I S] with z hz
  exact (hz T).symm

theorem area_integrable (L : Nat) (D I S : Finset Site) (T : NNReal) :
    Integrable (fun z : Sample L =>
      ((D \ DropletStoppedClockLaw.stateAt L D I S (T : Real) z).card : Real))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  convert (area_change_integrable L D I S T).add
    (integrable_const (((D \ S).card : Real))) using 1
  ext z
  simp only [Pi.add_apply]
  ring

/-- Exact physical signed compensation, with integrability established first.
Each half rate belongs to one specified fair mark at one original site. -/
theorem area_change_dynkin (L : Nat) (D I S : Finset Site) (T : NNReal) :
    (∫ z : Sample L,
      ((D \ DropletStoppedClockLaw.stateAt L D I S (T : Real) z).card : Real) -
        ((D \ S).card : Real)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    ∑ v : Vertex L, ∑ b : Bool, (1 / 2 : Real) * ∫ u : Real in Set.Ioc 0 (T : Real),
      ∫ z : Sample L, PredictableAreaContribution.increment L D I S v b (u.toNNReal,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  calc
    _ = ∫ z : Sample L, ∑ v : Vertex L, ∑ b : Bool,
        RealPredictableCompensation.pathSum L v b T
          (PredictableAreaContribution.increment L D I S v b) z
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
      apply integral_congr_ae
      filter_upwards [MarkedAreaSum.area_eq_pathSums_all_times_ae L D I S] with z hz
      exact hz T
    _ = _ := by
      rw [integral_finsetSum _ (fun v _ =>
        integrable_finsetSum _ (fun b _ => marked_pathSum_integrable L D I S v b T))]
      apply Finset.sum_congr rfl
      intro v _
      rw [integral_finsetSum _ (fun b _ => marked_pathSum_integrable L D I S v b T)]
      apply Finset.sum_congr rfl
      intro b _
      exact RealPredictableCompensation.bounded_predictable_integral_eq_time L v b T
        (PredictableAreaContribution.increment L D I S v b)
        (PredictableAreaContribution.increment_stronglyMeasurable L D I S v b)
        (D.card : Real) (PredictableAreaContribution.increment_norm_le L D I S v b)

theorem time_mean_increment_integrable (L : Nat) (D I S : Finset Site)
    (v : Vertex L) (b : Bool) (T : NNReal) :
    Integrable (fun u : Real => ∫ z : Sample L,
      PredictableAreaContribution.increment L D I S v b (u.toNNReal,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L))
      ((volume : Measure Real).restrict (Set.Ioc 0 (T : Real))) :=
  RealPredictableCompensation.time_mean_integrable L T
    (PredictableAreaContribution.increment L D I S v b)
    ((PredictableAreaContribution.increment_stronglyMeasurable L D I S v b).mono
      (PredictableClockSigma.predictable_le_ambient L))
    (D.card : Real) (PredictableAreaContribution.increment_norm_le L D I S v b)

theorem area_change_dynkin_single_integral (L : Nat) (D I S : Finset Site) (T : NNReal) :
    (∫ z : Sample L,
      ((D \ DropletStoppedClockLaw.stateAt L D I S (T : Real) z).card : Real) -
        ((D \ S).card : Real)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    (1 / 2 : Real) * ∫ u : Real in Set.Ioc 0 (T : Real), ∑ v : Vertex L, ∑ b : Bool,
      ∫ z : Sample L, PredictableAreaContribution.increment L D I S v b (u.toNNReal,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  rw [area_change_dynkin]
  have hsum : (∫ u : Real in Set.Ioc 0 (T : Real), ∑ v : Vertex L, ∑ b : Bool,
      ∫ z : Sample L, PredictableAreaContribution.increment L D I S v b (u.toNNReal,z)
        ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
      ∑ v : Vertex L, ∑ b : Bool, ∫ u : Real in Set.Ioc 0 (T : Real),
        ∫ z : Sample L, PredictableAreaContribution.increment L D I S v b (u.toNNReal,z)
          ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
    rw [integral_finsetSum _ (fun v _ => integrable_finsetSum _
      (fun b _ => time_mean_increment_integrable L D I S v b T))]
    apply Finset.sum_congr rfl
    intro v _
    exact integral_finsetSum _ (fun b _ => time_mean_increment_integrable L D I S v b T)
  rw [hsum]
  simp only [Finset.mul_sum]

theorem expected_area_dynkin (L : Nat) (D I S : Finset Site) (T : NNReal) :
    (∫ z : Sample L, ((D \ DropletStoppedClockLaw.stateAt L D I S (T : Real) z).card : Real)
      ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    ((D \ S).card : Real) +
      ∑ v : Vertex L, ∑ b : Bool, (1 / 2 : Real) * ∫ u : Real in Set.Ioc 0 (T : Real),
        ∫ z : Sample L, PredictableAreaContribution.increment L D I S v b (u.toNNReal,z)
          ∂ClockWordMarks.measure (ClippedSquareCoordinates.parameter L) := by
  have h := area_change_dynkin L D I S T
  rw [integral_sub (area_integrable L D I S T) (integrable_const _)] at h
  simpa only [integral_const,probReal_univ,one_smul] using (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
end MathResearchAnalysis.ActualAreaDynkin
