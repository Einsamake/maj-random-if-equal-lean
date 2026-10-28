module

public import MathResearchAnalysis.WeightedExitArea
public import MathResearchAnalysis.PhysicalWeightedDrift

set_option autoImplicit false

/- Exploratory extension. This file does not alter the sealed source tree.
   Validation status is recorded separately; no result is asserted merely by
   the presence of this source file. -/

@[expose] public noncomputable section

namespace MathResearchExploration.FullBlockThreshold

open MathResearchAnalysis
open MeasureTheory
open InfiniteGridModel (Site)
open ClippedDiamondGeometry (clippedDomain directedBlock)
open ClippedProtectedGeometry (protectedSites norm1)
open OrthogonalGridConvexity
open ForbiddenBirthControl (weight mass)
open WeightedExitArea (missingWeight)
open DropletDomainComparison (exitTime stoppedTrajectory)
open scoped BigOperators

def directedPoint (x : Site) (horizontal vertical : Bool) {m : Nat}
    (p : Fin m × Fin m) : Site :=
  (x.1 + (if horizontal then -((p.1.val : Int)+1) else (p.1.val : Int)+1),
   x.2 + (if vertical then -((p.2.val : Int)+1) else (p.2.val : Int)+1))

theorem directedPoint_injective (x : Site) (horizontal vertical : Bool) (m : Nat) :
    Function.Injective (directedPoint x horizontal vertical (m := m)) := by
  intro p q h
  have ha := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  apply Prod.ext <;> apply Fin.ext
  · cases horizontal <;> dsimp [directedPoint] at ha <;> omega
  · cases vertical <;> dsimp [directedPoint] at hb <;> omega

theorem directedBlock_eq_image (L : Nat) (x : Site) (horizontal vertical : Bool) :
    directedBlock L x horizontal vertical =
      Finset.univ.image (directedPoint x horizontal vertical (m := L/20)) := by
  ext u
  rw [ClippedDiamondGeometry.mem_directedBlock]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨p,hp.symm⟩
  · rintro ⟨p,hp⟩
    exact ⟨p,hp.symm⟩

theorem sum_positive_offsets (m : Nat) :
    (∑ i : Fin m, ((i.val : Real)+1)) = (m : Real)*((m : Real)+1)/2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

theorem sum_affine_block (m : Nat) (a : Real) :
    (∑ p : Fin m × Fin m,
      (a + 1 - ((p.1.val : Real)+1) - ((p.2.val : Real)+1))) =
        (m : Real)^2*(a-(m : Real)) := by
  simp only [Fintype.sum_prod_type, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  rw [sum_positive_offsets]
  rw [← Finset.mul_sum, sum_positive_offsets]
  push_cast
  ring

theorem directedPoint_weight_lower {L : Nat} {x : Site}
    (hx : x ∈ protectedSites L) (horizontal vertical : Bool)
    (p : Fin (L/20) × Fin (L/20)) :
    (L : Real)/10+1-((p.1.val : Real)+1)-((p.2.val : Real)+1) ≤
      weight L (directedPoint x horizontal vertical p) := by
  have hxBand := (ClippedProtectedGeometry.mem_protectedSites_iff_band L x).mp hx
  change 10 * norm1 x ≤ 9 * (L : Int)+10 at hxBand
  have ha := abs_add_le x.1
    (if horizontal then -((p.1.val : Int)+1) else (p.1.val : Int)+1)
  have hb := abs_add_le x.2
    (if vertical then -((p.2.val : Int)+1) else (p.2.val : Int)+1)
  rw [WeightedExitArea.abs_signed_offset] at ha hb
  have hi : 10 * norm1 (directedPoint x horizontal vertical p) ≤
      9*(L : Int)+10+10*((p.1.val : Int)+1)+10*((p.2.val : Int)+1) := by
    dsimp only [norm1, directedPoint] at hxBand ⊢
    omega
  have hr : 10 * (norm1 (directedPoint x horizontal vertical p) : Real) ≤
      9*(L : Real)+10+10*((p.1.val : Real)+1)+10*((p.2.val : Real)+1) := by
    exact_mod_cast hi
  change _ ≤ (L : Real)+2-(norm1 (directedPoint x horizontal vertical p) : Real)
  linarith

theorem fullBlock_exact_lower_bound {L : Nat} {x : Site}
    (hx : x ∈ protectedSites L) (horizontal vertical : Bool) :
    (L/20 : Nat)^2 * ((L : Real)/10-(L/20 : Nat)) ≤
      mass (weight L) (directedBlock L x horizontal vertical) := by
  rw [directedBlock_eq_image]
  unfold mass
  rw [Finset.sum_image]
  · calc
      _ = ∑ p : Fin (L/20) × Fin (L/20),
          ((L : Real)/10 + 1 - ((p.1.val : Real)+1) - ((p.2.val : Real)+1)) :=
        (sum_affine_block (L/20) ((L : Real)/10)).symm
      _ ≤ _ := Finset.sum_le_sum (fun p _ => directedPoint_weight_lower hx horizontal vertical p)
  · exact fun p _ q _ h => directedPoint_injective x horizontal vertical _ h

theorem side_le_twentyfive_mul_div_twenty {L : Nat} (hL : 80 ≤ L) :
    L ≤ 25*(L/20) := by
  have hr := Nat.mod_lt L (by omega : 0 < 20)
  have hd := Nat.mod_add_div L 20
  omega

theorem fullBlock_cubic_weight {L : Nat} (hL : 80 ≤ L) {x : Site}
    (hx : x ∈ protectedSites L) (horizontal vertical : Bool) :
    (L : Real)^3/12500 ≤ mass (weight L) (directedBlock L x horizontal vertical) := by
  have hm : (L : Real) ≤ 25*(L/20 : Nat) := by
    exact_mod_cast side_le_twentyfive_mul_div_twenty hL
  have hu : 20*((L/20 : Nat) : Real) ≤ (L : Real) := by
    exact_mod_cast Nat.mul_div_le L 20
  have hm0 : (0 : Real) ≤ (L/20 : Nat) := Nat.cast_nonneg _
  have hL0 : (0 : Real) ≤ L := Nat.cast_nonneg _
  have hsq := mul_self_le_mul_self hL0 hm
  have hfactor : (L : Real)/20 ≤ (L : Real)/10-(L/20 : Nat) := by linarith
  have hmul := mul_le_mul_of_nonneg_right hsq (by positivity : (0 : Real) ≤ (L : Real)/20)
  have hmul2 := mul_le_mul_of_nonneg_left hfactor (sq_nonneg ((L/20 : Nat) : Real))
  have hsum := fullBlock_exact_lower_bound hx horizontal vertical
  nlinarith

theorem cubic_weight_of_protected_missing {L : Nat} (hL : 80 ≤ L)
    {S : Finset Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hconn : FourConnected S) (hmissing : ¬ protectedSites L ⊆ S) :
    (L : Real)^3/12500 ≤ missingWeight L S := by
  have hex : ∃ x ∈ protectedSites L, x ∉ S := by
    by_contra hh
    apply hmissing
    intro x hx
    by_contra hxs
    exact hh ⟨x,hx,hxs⟩
  obtain ⟨x,hx,hxs⟩ := hex
  obtain ⟨horizontal,vertical,hblock⟩ := ProtectedExitArea.exists_vacant_directedBlock
    (by omega : 40 ≤ L) hr hc hconn hx hxs
  exact (fullBlock_cubic_weight hL hx horizontal vertical).trans
    (WeightedExitArea.mass_le_missingWeight hblock)

theorem actual_stopped_weight_after_exit {L : Nat} (hL : 80 ≤ L)
    (events : Nat → DropletModifiedWord.Event) (n : Nat)
    (hn : exitTime (clippedDomain L) (clippedDomain L) (protectedSites L) events ≤ (n : ℕ∞)) :
    (L : Real)^3/12500 ≤
      missingWeight L (stoppedTrajectory (clippedDomain L) (clippedDomain L) (protectedSites L) events n) := by
  have hs := (ProtectedEvolution.initial_stoppedTrajectory_shape (by omega : 2 ≤ L) events n).1
  apply cubic_weight_of_protected_missing hL hs.1 hs.2.1 hs.2.2.1
  intro hh
  have hlt := (DropletStoppedWord.stoppedTrajectory_protected_iff _ _ _ _ _).mp hh
  exact (not_le_of_gt hlt) hn

theorem cubic_weight_of_physical_exit_le (L : Nat) (hL : 80 ≤ L)
    (z : DropletClockLaw.Sample L) (hg : ∀ t : Real, ClockEventWord.Good z.1 t)
    (t : Real) (ht : 0 ≤ t)
    (hexit : FrozenPhysicalExit.physicalExit L (clippedDomain L) (protectedSites L)
      (clippedDomain L) z ≤ ENNReal.ofReal t) :
    (L : Real)^3/12500 ≤ missingWeight L
      (DropletStoppedClockLaw.stateAt L (clippedDomain L) (protectedSites L) (clippedDomain L) t z) := by
  have hm := (FrozenPhysicalExit.physicalExit_le_iff L _ _ _ z hg ht).mp hexit
  let fallback : DropletModifiedWord.Event := ((0,0),false)
  rw [DropletStoppedClockLaw.stateAt_eq_stoppedTrajectory L _ _ _ t z fallback] at hm ⊢
  have hn : exitTime _ _ _ _ ≤
      ((DropletClockLaw.markedEvents L (ClockEventWord.word z.1 t) z.2).length : ℕ∞) :=
    le_of_not_gt (fun h => hm ((DropletStoppedWord.stoppedTrajectory_protected_iff _ _ _ _ _).mpr h))
  exact actual_stopped_weight_after_exit hL _ _ hn

theorem physical_exit_measure_le_cubic_weight (L : Nat) (hL : 80 ≤ L) (t : Real) (ht : 0 ≤ t) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | FrozenPhysicalExit.physicalExit L (clippedDomain L) (protectedSites L) (clippedDomain L) z ≤ ENNReal.ofReal t} ≤
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | (L : Real)^3/12500 ≤ missingWeight L
        (DropletStoppedClockLaw.stateAt L (clippedDomain L) (protectedSites L) (clippedDomain L) t z)} := by
  apply measure_mono_ae
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L] with z hz
  exact fun he => cubic_weight_of_physical_exit_le L hL z hz t ht he

theorem original_extinction_measure_le_cubic_weight (L : Nat) (hL : 80 ≤ L) (t : Real) (ht : 0 ≤ t) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L) t (fun _ => true) z = fun _ => false} ≤
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | (L : Real)^3/12500 ≤ missingWeight L
        (DropletStoppedClockLaw.stateAt L (clippedDomain L) (protectedSites L) (clippedDomain L) t z)} :=
  (FrozenPhysicalExit.original_extinction_measure_le_physical_exit L (by omega : 40 ≤ L) t ht).trans
    (physical_exit_measure_le_cubic_weight L hL t ht)

theorem threshold_pos (L : Nat) (hL : 80 ≤ L) : 0 < (L : Real)^3/12500 := by
  have hp : 0 < (L : Real) := by exact_mod_cast (show 0 < L by omega)
  positivity

theorem exit_probability_mul_le_mean (L : Nat) (hL : 80 ≤ L) (T : NNReal) :
    ((L : Real)^3/12500) * (PhysicalAreaTail.law L).real (PhysicalAreaTail.exitEvent L T) ≤
      ∫ z : DropletClockLaw.Sample L, WeightedAreaTail.missingArea L T z ∂PhysicalAreaTail.law L := by
  have hm : (PhysicalAreaTail.law L).real (PhysicalAreaTail.exitEvent L T) ≤
      (PhysicalAreaTail.law L).real {z | (L : Real)^3/12500 ≤ WeightedAreaTail.missingArea L T z} := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact physical_exit_measure_le_cubic_weight L hL T T.coe_nonneg
  exact (mul_le_mul_of_nonneg_left hm (threshold_pos L hL).le).trans
    (mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall (WeightedAreaTail.missingArea_nonnegative L T))
      (WeightedAreaTail.missingArea_integrable L T) _)

theorem actual_exit_probability_le_linear_time (L : Nat) (hL : 80 ≤ L) (T : NNReal) :
    (PhysicalAreaTail.law L).real (PhysicalAreaTail.exitEvent L T) ≤
      ((18*L+12 : Real)*(T : Real)+((L : Real)+2)*(4*L+2)) / ((L : Real)^3/12500) := by
  apply (le_div_iff₀ (threshold_pos L hL)).mpr
  have he := exit_probability_mul_le_mean L hL T
  have hm := PhysicalWeightedDrift.actual_mean_weighted_area_le L (by omega : 2 ≤ L) T
  simpa only [mul_comm] using he.trans hm

theorem original_clock_extinction_le_linear_time (L : Nat) (hL : 80 ≤ L) (T : NNReal) :
    (PhysicalAreaTail.law L).real {z | ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L)
      (T : Real) (fun _ => true) z = fun _ => false} ≤
      ((18*L+12 : Real)*(T : Real)+((L : Real)+2)*(4*L+2)) / ((L : Real)^3/12500) := by
  apply le_trans _ (actual_exit_probability_le_linear_time L hL T)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact FrozenPhysicalExit.original_extinction_measure_le_physical_exit L (by omega) T T.coe_nonneg

def quadraticHorizon (L : Nat) : NNReal :=
  ⟨(L : Real)^2/1000000, by positivity⟩

theorem quadratic_mean_bound (L : Nat) (hL : 250000 ≤ L) :
    (18*L+12 : Real)*(quadraticHorizon L : Real)+((L : Real)+2)*(4*L+2) ≤
      39*(L : Real)^3/1000000 := by
  have hlarge : (250000 : Real) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : Real) ≤ L := Nat.cast_nonneg L
  have hcoef : (18*L+12 : Real) ≤ 19*(L : Real) := by linarith
  have hquad := mul_le_mul_of_nonneg_right (show (11 : Real) ≤ L by linarith) hL0
  have hclean : ((L : Real)+2)*(4*L+2) ≤ 5*(L : Real)^2 := by nlinarith
  have hraw := mul_le_mul_of_nonneg_right hcoef
    (show (0 : Real) ≤ (L : Real)^2/1000000 by positivity)
  have hcubic := mul_le_mul_of_nonneg_right hlarge (sq_nonneg (L : Real))
  change (18*L+12 : Real)*((L : Real)^2/1000000)+((L : Real)+2)*(4*L+2) ≤ _
  nlinarith

theorem quadratic_bound_le_half_threshold (L : Nat) (hL : 250000 ≤ L) :
    (18*L+12 : Real)*(quadraticHorizon L : Real)+((L : Real)+2)*(4*L+2) ≤
      ((L : Real)^3/12500)/2 := by
  have hm := quadratic_mean_bound L hL
  have hp : (0 : Real) ≤ (L : Real)^3 := by positivity
  nlinarith

theorem actual_exit_at_quadraticHorizon_le_half (L : Nat) (hL : 250000 ≤ L) :
    (PhysicalAreaTail.law L).real (PhysicalAreaTail.exitEvent L (quadraticHorizon L)) ≤ (1/2 : Real) := by
  apply (actual_exit_probability_le_linear_time L (by omega) (quadraticHorizon L)).trans
  apply (div_le_iff₀ (threshold_pos L (by omega))).mpr
  have hm := quadratic_bound_le_half_threshold L hL
  nlinarith

theorem original_clock_extinction_at_quadraticHorizon_le_half (L : Nat) (hL : 250000 ≤ L) :
    (PhysicalAreaTail.law L).real {z | ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L)
      (quadraticHorizon L : Real) (fun _ => true) z = fun _ => false} ≤ (1/2 : Real) := by
  apply le_trans _ (actual_exit_at_quadraticHorizon_le_half L hL)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact FrozenPhysicalExit.original_extinction_measure_le_physical_exit L (by omega)
    (quadraticHorizon L) (quadraticHorizon L).coe_nonneg

#print axioms directedPoint
#print axioms directedPoint_injective
#print axioms directedBlock_eq_image
#print axioms sum_positive_offsets
#print axioms sum_affine_block
#print axioms directedPoint_weight_lower
#print axioms fullBlock_exact_lower_bound
#print axioms side_le_twentyfive_mul_div_twenty
#print axioms fullBlock_cubic_weight
#print axioms cubic_weight_of_protected_missing
#print axioms actual_stopped_weight_after_exit
#print axioms cubic_weight_of_physical_exit_le
#print axioms physical_exit_measure_le_cubic_weight
#print axioms original_extinction_measure_le_cubic_weight
#print axioms threshold_pos
#print axioms exit_probability_mul_le_mean
#print axioms actual_exit_probability_le_linear_time
#print axioms original_clock_extinction_le_linear_time
#print axioms quadraticHorizon
#print axioms quadratic_mean_bound
#print axioms quadratic_bound_le_half_threshold
#print axioms actual_exit_at_quadraticHorizon_le_half
#print axioms original_clock_extinction_at_quadraticHorizon_le_half

end MathResearchExploration.FullBlockThreshold
