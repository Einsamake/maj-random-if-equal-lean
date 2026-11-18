module
public import FullBlockThreshold
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchLower
open MathResearchAnalysis MeasureTheory
open InfiniteGridModel (Site)
open WeightedRawContour
open ClippedDiamondGeometry (clippedDomain)
open ClippedProtectedGeometry (innerDiamond protectedSites)
open OrthogonalGridConvexity
open GridCellBoundary (HalfEdge)
open ForbiddenBirthControl (weight rawWeightedRate)

/-- Each paid edge is the unique west-facing edge of an occupied row. -/
theorem paired_rises_le_rows {S : Finset Site} (hr : RowConvex S)
    (hc : ColumnConvex S) (hconn : FourConnected S) :
    (∑ v ∈ northwestPairs S, (westSegment (previousTop S v) v).card) ≤
      (S.image Prod.snd).card := by
  classical
  let tag : Site → HalfEdge := fun u => (u, 3)
  have hs : (northwestPairs S).biUnion (fun v => westSegment (previousTop S v) v) ⊆
      (OrthogonalPerimeter.westCells S).image tag := by
    intro e he
    obtain ⟨v,hv,he⟩ := Finset.mem_biUnion.mp he
    have h := pair_spec hv
    have hb := rising_tops_westSegment_subset hc hconn h.2.1
      (northwestCorner_north h.1) (by omega) (pair_rises hc hconn hv) he
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_image.mpr ⟨(v.1,j), Finset.mem_filter.mpr
      ((GridCellBoundary.mem_boundary_west S _).mp hb), rfl⟩
  rw [← Finset.card_biUnion (paired_segments_disjoint hc)]
  exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans
    (OrthogonalPerimeter.westCells_card hr).le)

theorem charge_le_rows {L : Nat} (hL : 1 ≤ L) {S : Finset Site}
    (hr : RowConvex S) (hc : ColumnConvex S) (hconn : FourConnected S)
    (hSD : S ⊆ clippedDomain L) :
    northwestCharge L (ClippedSquareCoordinates.centeredSites L) S ≤
      (L : ℝ) + 2 + ((S.image Prod.snd).card : ℝ) := by
  have hseg := Finset.sum_le_sum (s := northwestPairs S) (fun v hv =>
    rising_tops_weight_le_segment L (by have hx := (pair_spec hv).2.2; omega : v.1 = (previousTop S v).1 + 1)
      (pair_rises hc hconn hv))
  have hrows : (∑ v ∈ northwestPairs S, ((westSegment (previousTop S v) v).card : ℝ))
      ≤ ((S.image Prod.snd).card : ℝ) := by exact_mod_cast paired_rises_le_rows hr hc hconn
  change (∑ v ∈ northwestPairs S, (weight L v - weight L (pairedValley S v))) ≤ _ at hseg
  have hp : northwestPairs S ⊆ northwestCorners S := Finset.filter_subset _ _
  have heq := Finset.sum_sdiff (f := weight L) hp
  have hval := paired_valley_weight_sum_le L hL hc hconn hSD
  have hor := northwest_unpaired_weight_le L hc hconn
  rw [Finset.sum_sub_distrib] at hseg
  unfold northwestCharge
  linarith

theorem raw_drift_le_six {L : Nat} (hL : 2 ≤ L) {S : Finset Site}
    (hs : ProtectedEvolution.Shape S) (hi : innerDiamond L ⊆ S)
    (hSD : S ⊆ clippedDomain L) :
    rawWeightedRate (weight L) (ClippedSquareCoordinates.centeredSites L) S ≤ 6*(L : ℝ)+6 := by
  have hcharge (a b : Bool) :
      northwestCharge L (ClippedSquareCoordinates.centeredSites L)
        (ProtectedCornerGeometry.mirror a b S) ≤ 3*(L : ℝ)+3 := by
    have hs' := WeightedReflection.shape_mirror a b hs
    have hd := WeightedReflection.mirror_subset_clippedDomain L a b hSD
    have hy : (ProtectedCornerGeometry.mirror a b S).image Prod.snd ⊆
        Finset.Icc (-(L : ℤ)) (L : ℤ) := by
      intro y hy
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_Icc.mpr (abs_le.mp (((ClippedDiamondGeometry.mem_clippedDomain L u).mp (hd hu)).2.1))
    have hcard := Finset.card_le_card hy
    rw [Int.card_Icc] at hcard
    have hb : ((ProtectedCornerGeometry.mirror a b S).image Prod.snd).card ≤ 2*L+1 := by omega
    have hb' : (((ProtectedCornerGeometry.mirror a b S).image Prod.snd).card : ℝ) ≤ 2*(L : ℝ)+1 := by exact_mod_cast hb
    linarith [charge_le_rows (by omega : 1 ≤ L) hs'.1 hs'.2.1 hs'.2.2.1 hd]
  have he := WeightedRawRate.actual_raw_four_charges hL hs hi hSD
  simp only [Fintype.sum_bool] at he
  linarith [hcharge false false,hcharge true false,hcharge false true,hcharge true true]

theorem clock_extinction_bound (L : Nat) (hL : 80 ≤ L) (T : NNReal) :
    (PhysicalAreaTail.law L).real {z | ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L)
      (T : ℝ) (fun _ => true) z = fun _ => false} ≤
      ((6*(L : ℝ)+6)*(T : ℝ)+((L : ℝ)+2)*(4*L+2))/((L : ℝ)^3/12500) := by
  have hp (t : NNReal) : (∫ z, WeightedAreaTail.rawContribution L (t,z) ∂PhysicalAreaTail.law L)
      ≤ 6*(L : ℝ)+6 := by
    have hpoint : ∀ᵐ z ∂PhysicalAreaTail.law L, WeightedAreaTail.rawContribution L (t,z) ≤ 6*(L : ℝ)+6 := by
      filter_upwards [PhysicalWeightedDrift.beforeState_shape_all_times_ae L (by omega)] with z hz
      unfold WeightedAreaTail.rawContribution
      split
      · rename_i h
        exact raw_drift_le_six (by omega) (hz t)
          ((ClippedProtectedGeometry.innerDiamond_subset_protectedSites L).trans h)
          (ObservedPreState.state_supported L _ _ (Finset.Subset.refl _) t z)
      · positivity
    simpa using integral_mono_ae (WeightedAreaTail.rawContribution_sample_integrable L (by omega) t)
      (integrable_const (6*(L : ℝ)+6)) hpoint
  have hc : Integrable (fun _ : ℝ => 6*(L : ℝ)+6) ((volume : Measure ℝ).restrict (Set.Ioc 0 (T : ℝ))) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have htime := integral_mono_ae (WeightedAreaTail.rawContribution_time_mean_integrable L (by omega) T)
    hc (Filter.Eventually.of_forall (fun t : ℝ => hp t.toNNReal))
  rw [PhysicalWeightedDrift.integral_time_const] at htime
  have hmean := WeightedAreaTail.meanArea_le_raw_integral_add_budget L (by omega) T
  have hprob := MathResearchExploration.FullBlockThreshold.exit_probability_mul_le_mean L hL T
  apply le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (FrozenPhysicalExit.original_extinction_measure_le_physical_exit L (by omega) T T.coe_nonneg)) _
  apply (le_div_iff₀ (MathResearchExploration.FullBlockThreshold.threshold_pos L hL)).mpr
  change (PhysicalAreaTail.law L).real (PhysicalAreaTail.exitEvent L T) * _ ≤ _
  rw [mul_comm ((PhysicalAreaTail.law L).real _), mul_comm (6*(L : ℝ)+6)]
  exact hprob.trans (hmean.trans (add_le_add htime le_rfl))

end MathResearchLower
