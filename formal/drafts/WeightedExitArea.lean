module

public import MathResearchAnalysis.ForbiddenBirthControl
public import MathResearchAnalysis.FrozenPhysicalExit

set_option autoImplicit false

/-!
# A cubic weighted-area threshold for genuine protected loss

The weight is the actual linear diamond weight. A half-sized subblock of the
previously proved vacant quadrant has order L^2 sites, each of weight at least
L/20. The resulting L^3/128000 threshold is connected to the actual frozen
physical exit event and the original endpoint law. No drift or tail bound is
assumed or concluded.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.WeightedExitArea

open MeasureTheory
open InfiniteGridModel (Site)
open ClippedDiamondGeometry (clippedDomain directedBlock)
open ClippedProtectedGeometry (protectedSites norm1)
open OrthogonalGridConvexity
open DropletDomainComparison (exitTime stoppedTrajectory)
open ForbiddenBirthControl (weight mass)
open scoped BigOperators

def smallBlock (L : Nat) (x : Site) (horizontal vertical : Bool) : Finset Site :=
  directedBlock (L / 2) x horizontal vertical

def missingWeight (L : Nat) (S : Finset Site) : Real :=
  mass (weight L) (clippedDomain L \ S)

theorem half_twentieth (L : Nat) : L / 2 / 20 = L / 40 := by
  exact Nat.div_div_eq_div_mul L 2 20

theorem smallBlock_subset_directedBlock (L : Nat) (x : Site) (horizontal vertical : Bool) :
    smallBlock L x horizontal vertical ⊆ directedBlock L x horizontal vertical := by
  intro u hu
  obtain ⟨p,hp⟩ := (ClippedDiamondGeometry.mem_directedBlock (L/2) x u horizontal vertical).mp hu
  have hm : L / 2 / 20 ≤ L / 20 := Nat.div_le_div_right (Nat.div_le_self L 2)
  let q : Fin (L / 20) × Fin (L / 20) :=
    (⟨p.1.val,lt_of_lt_of_le p.1.isLt hm⟩,⟨p.2.val,lt_of_lt_of_le p.2.isLt hm⟩)
  exact (ClippedDiamondGeometry.mem_directedBlock L x u horizontal vertical).mpr ⟨q,hp⟩

theorem smallBlock_card (L : Nat) (x : Site) (horizontal vertical : Bool) :
    (smallBlock L x horizontal vertical).card = (L / 40) ^ 2 := by
  rw [smallBlock,ClippedDiamondGeometry.directedBlock_card,half_twentieth]

theorem side_le_eighty_mul_div_forty {L : Nat} (hL : 80 ≤ L) : L ≤ 80 * (L / 40) := by
  have hm := Nat.mod_lt L (by omega : 0 < 40)
  have hd := Nat.mod_add_div L 40
  omega

theorem smallBlock_quadratic_card {L : Nat} (hL : 80 ≤ L) (x : Site)
    (horizontal vertical : Bool) :
    (L : Real)^2 / 6400 ≤ ((smallBlock L x horizontal vertical).card : Real) := by
  rw [smallBlock_card]
  have hbound : (L : Real) ≤ 80 * (L / 40 : Nat) := by
    exact_mod_cast side_le_eighty_mul_div_forty hL
  have hsq := mul_self_le_mul_self (Nat.cast_nonneg L : (0 : Real) ≤ L) hbound
  push_cast
  nlinarith

theorem abs_signed_offset (b : Bool) (n : Nat) :
    |if b then -((n : Int)+1) else (n : Int)+1| = (n : Int)+1 := by
  have hn : 0 ≤ (n : Int)+1 := by omega
  cases b with
  | false => exact abs_of_nonneg hn
  | true =>
    change |-((n : Int)+1)| = (n : Int)+1
    rw [abs_neg,abs_of_nonneg hn]

theorem smallBlock_norm_bound {L : Nat} {x : Site} (hx : x ∈ protectedSites L)
    (horizontal vertical : Bool) {u : Site} (hu : u ∈ smallBlock L x horizontal vertical) :
    20 * norm1 u ≤ 19 * (L : Int) + 20 := by
  have hxBand := (ClippedProtectedGeometry.mem_protectedSites_iff_band L x).mp hx
  change 10 * norm1 x ≤ 9 * (L : Int) + 10 at hxBand
  obtain ⟨p,rfl⟩ := (ClippedDiamondGeometry.mem_directedBlock (L/2) x u horizontal vertical).mp hu
  have hp : (p.1.val : Int)+1 ≤ (L / 40 : Nat) := by
    have h := p.1.isLt
    have heq := half_twentieth L
    have hs : p.1.val+1 ≤ L/40 := by omega
    exact_mod_cast hs
  have hq : (p.2.val : Int)+1 ≤ (L / 40 : Nat) := by
    have h := p.2.isLt
    have heq := half_twentieth L
    have hs : p.2.val+1 ≤ L/40 := by omega
    exact_mod_cast hs
  have hm : 40 * (L / 40 : Int) ≤ (L : Int) := by exact_mod_cast Nat.mul_div_le L 40
  have ha := abs_add_le x.1 (if horizontal then -((p.1.val : Int)+1) else (p.1.val : Int)+1)
  have hb := abs_add_le x.2 (if vertical then -((p.2.val : Int)+1) else (p.2.val : Int)+1)
  rw [abs_signed_offset] at ha hb
  dsimp only [norm1] at hxBand ⊢
  omega

theorem smallBlock_weight_lower_bound {L : Nat} {x : Site} (hx : x ∈ protectedSites L)
    (horizontal vertical : Bool) {u : Site} (hu : u ∈ smallBlock L x horizontal vertical) :
    (L : Real)/20 ≤ weight L u := by
  have h := smallBlock_norm_bound hx horizontal vertical hu
  have hr : 20 * (norm1 u : Real) ≤ 19 * (L : Real) + 20 := by exact_mod_cast h
  change (L : Real)/20 ≤ (L : Real)+2-(norm1 u : Real)
  linarith

theorem smallBlock_cubic_weight {L : Nat} (hL : 80 ≤ L) {x : Site}
    (hx : x ∈ protectedSites L) (horizontal vertical : Bool) :
    (L : Real)^3 / 128000 ≤ mass (weight L) (smallBlock L x horizontal vertical) := by
  have hcard := smallBlock_quadratic_card hL x horizontal vertical
  have hsum : ((smallBlock L x horizontal vertical).card : Real) * ((L : Real)/20) ≤
      mass (weight L) (smallBlock L x horizontal vertical) := by
    calc
      _ = ∑ u ∈ smallBlock L x horizontal vertical, (L : Real)/20 := by
        simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun u hu => smallBlock_weight_lower_bound hx horizontal vertical hu)
  calc
    (L : Real)^3 / 128000 = ((L : Real)^2/6400) * ((L : Real)/20) := by ring
    _ ≤ ((smallBlock L x horizontal vertical).card : Real) * ((L : Real)/20) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ _ := hsum

theorem missingWeight_nonnegative (L : Nat) (S : Finset Site) : 0 ≤ missingWeight L S := by
  apply Finset.sum_nonneg
  intro u hu
  exact le_trans (by norm_num : (0 : Real) ≤ 1)
    (ForbiddenBirthControl.weight_nonnegative_on_domain L u (Finset.mem_sdiff.mp hu).1)

theorem mass_le_missingWeight {L : Nat} {S B : Finset Site}
    (hB : B ⊆ clippedDomain L \ S) : mass (weight L) B ≤ missingWeight L S := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hB
  intro u hu _
  exact le_trans (by norm_num : (0 : Real) ≤ 1)
    (ForbiddenBirthControl.weight_nonnegative_on_domain L u (Finset.mem_sdiff.mp hu).1)

theorem cubic_weight_of_protected_missing {L : Nat} (hL : 80 ≤ L)
    {S : Finset Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hconn : FourConnected S) (hmissing : ¬ protectedSites L ⊆ S) :
    (L : Real)^3 / 128000 ≤ missingWeight L S := by
  have hex : ∃ x ∈ protectedSites L, x ∉ S := by
    by_contra hh
    apply hmissing
    intro x hx
    by_contra hxs
    exact hh ⟨x,hx,hxs⟩
  obtain ⟨x,hx,hxs⟩ := hex
  obtain ⟨horizontal,vertical,hblock⟩ := ProtectedExitArea.exists_vacant_directedBlock
    (by omega : 40 ≤ L) hr hc hconn hx hxs
  exact (smallBlock_cubic_weight hL hx horizontal vertical).trans
    (mass_le_missingWeight ((smallBlock_subset_directedBlock L x horizontal vertical).trans hblock))

theorem actual_stopped_weight_after_exit {L : Nat} (hL : 80 ≤ L)
    (events : Nat → DropletModifiedWord.Event) (n : Nat)
    (hn : exitTime (clippedDomain L) (clippedDomain L) (protectedSites L) events ≤ (n : ℕ∞)) :
    (L : Real)^3 / 128000 ≤
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
    (L : Real)^3 / 128000 ≤ missingWeight L
      (DropletStoppedClockLaw.stateAt L (clippedDomain L) (protectedSites L) (clippedDomain L) t z) := by
  have hm := (FrozenPhysicalExit.physicalExit_le_iff L _ _ _ z hg ht).mp hexit
  let fallback : DropletModifiedWord.Event := ((0,0),false)
  rw [DropletStoppedClockLaw.stateAt_eq_stoppedTrajectory L _ _ _ t z fallback] at hm ⊢
  have hn : DropletDomainComparison.exitTime _ _ _ _ ≤
      ((DropletClockLaw.markedEvents L (ClockEventWord.word z.1 t) z.2).length : ℕ∞) :=
    le_of_not_gt (fun h => hm ((DropletStoppedWord.stoppedTrajectory_protected_iff _ _ _ _ _).mpr h))
  exact actual_stopped_weight_after_exit hL _ _ hn

theorem physical_exit_measure_le_cubic_weight (L : Nat) (hL : 80 ≤ L) (t : Real) (ht : 0 ≤ t) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | FrozenPhysicalExit.physicalExit L (clippedDomain L) (protectedSites L) (clippedDomain L) z ≤ ENNReal.ofReal t} ≤
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | (L : Real)^3/128000 ≤ missingWeight L
        (DropletStoppedClockLaw.stateAt L (clippedDomain L) (protectedSites L) (clippedDomain L) t z)} := by
  apply measure_mono_ae
  filter_upwards [ClockWordConsistency.marked_sample_good_ae L] with z hz
  exact fun he => cubic_weight_of_physical_exit_le L hL z hz t ht he

theorem original_extinction_measure_le_cubic_weight (L : Nat) (hL : 80 ≤ L) (t : Real) (ht : 0 ≤ t) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L) t (fun _ => true) z = fun _ => false} ≤
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | (L : Real)^3/128000 ≤ missingWeight L
        (DropletStoppedClockLaw.stateAt L (clippedDomain L) (protectedSites L) (clippedDomain L) t z)} :=
  (FrozenPhysicalExit.original_extinction_measure_le_physical_exit L (by omega : 40 ≤ L) t ht).trans
    (physical_exit_measure_le_cubic_weight L hL t ht)

end MathResearchAnalysis.WeightedExitArea
