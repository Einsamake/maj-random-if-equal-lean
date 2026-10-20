module
public import MathResearchAnalysis.MaskedAreaGenerator
set_option autoImplicit false
/-! The actual mask-relative missing area is a bounded observable, and its finite update-rate equals the negative-cardinality rate only after proving mask support. No arbitrary initial-set potential or physical-time compensation identity is substituted. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.ProtectedAreaPotential
open MeasureTheory
open InfiniteGridModel (Site)
open DropletStoppedWord (stoppedStep stoppedWord)
open MaskedAreaGenerator (frozenGenerator)

theorem stoppedStep_supported {D I S : Finset Site} (hSD : S ⊆ D) (e : DropletModifiedWord.Event) :
    stoppedStep D I S e ⊆ D := by
  unfold stoppedStep
  split_ifs
  · exact DropletModifiedWord.modifiedStep_supported hSD e.1 e.2
  · exact hSD

theorem stoppedWord_supported {D I S : Finset Site} (hSD : S ⊆ D) (w : List DropletModifiedWord.Event) :
    stoppedWord D I S w ⊆ D := by
  induction w generalizing S with
  | nil => exact hSD
  | cons e w ih => exact ih (stoppedStep_supported hSD e)

theorem observed_state_supported (L : Nat) {D I S : Finset Site} (hSD : S ⊆ D)
    (t : Real) (z : DropletClockLaw.Sample L) : ObservedFrozenProcess.state L D I S t z ⊆ D := by
  classical
  by_cases hex : ∃ T, z ∈ ObservedFrozenProcess.graph L D I S t T
  · obtain ⟨T,hT⟩ := hex
    rw [ObservedFrozenProcess.state_eq_of_graph L D I S t z T hT]
    obtain ⟨l,ξ,_,he⟩ := hT
    rw [← he]
    exact stoppedWord_supported hSD _
  · simpa only [ObservedFrozenProcess.state,dite_eq_right hex] using hSD

theorem missing_area_eq_negative_card {D S : Finset Site} (hSD : S ⊆ D) :
    ((D \ S).card : Real) = (D.card : Real) - S.card := by
  have hc : ((D \ S).card : Real) + S.card = D.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hSD
  linarith

theorem observed_area_eq_negative_card (L : Nat) {D I S : Finset Site} (hSD : S ⊆ D)
    (t : Real) (z : DropletClockLaw.Sample L) :
    ((D \ ObservedFrozenProcess.state L D I S t z).card : Real) =
      (D.card : Real) - (ObservedFrozenProcess.state L D I S t z).card :=
  missing_area_eq_negative_card (observed_state_supported L hSD t z)

theorem frozenGenerator_congr (D I S : Finset Site) (f g : Finset Site → Real)
    (h0 : f S = g S) (hstep : ∀ v ∈ D, ∀ b : Bool, f (stoppedStep D I S (v,b)) = g (stoppedStep D I S (v,b))) :
    frozenGenerator D I S f = frozenGenerator D I S g := by
  unfold frozenGenerator
  apply Finset.sum_congr rfl
  intro v hv
  rw [h0,hstep v hv false,hstep v hv true]

theorem frozenGenerator_add_constant (D I S : Finset Site) (f : Finset Site → Real) (c : Real) :
    frozenGenerator D I S (fun T => c + f T) = frozenGenerator D I S f := by
  unfold frozenGenerator
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem missing_area_generator {D I S : Finset Site} (hSD : S ⊆ D) :
    frozenGenerator D I S (fun T => ((D \ T).card : Real)) =
      if I ⊆ S then MaskedAreaGenerator.rawAreaRate D S + MaskedAreaGenerator.cleanupRate D S else 0 := by
  calc
    _ = frozenGenerator D I S (fun T => (D.card : Real) + -(T.card : Real)) := by
      apply frozenGenerator_congr
      · simpa only [sub_eq_add_neg] using missing_area_eq_negative_card hSD
      · intro v _ b
        simpa only [sub_eq_add_neg] using missing_area_eq_negative_card (stoppedStep_supported hSD (v,b))
    _ = frozenGenerator D I S (fun T => -(T.card : Real)) := frozenGenerator_add_constant D I S _ _
    _ = _ := MaskedAreaGenerator.frozen_area_generator_exact D I S

theorem observed_area_measurable (L : Nat) (D I S : Finset Site) (t : Real) :
    Measurable (fun z : DropletClockLaw.Sample L => ((D \ ObservedFrozenProcess.state L D I S t z).card : Real)) :=
  (ObservedFrozenProcess.observable_measurable L D I S t (fun T => ((D \ T).card : Real))).mono
    ((MarkedClockFiltration.history L).le t) le_rfl

theorem observed_area_bounds (L : Nat) (D I S : Finset Site) (t : Real) (z : DropletClockLaw.Sample L) :
    0 ≤ ((D \ ObservedFrozenProcess.state L D I S t z).card : Real) ∧
      ((D \ ObservedFrozenProcess.state L D I S t z).card : Real) ≤ D.card := by
  exact ⟨Nat.cast_nonneg _,by exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := D))⟩

theorem observed_area_integrable (L : Nat) (D I S : Finset Site) (t : Real) :
    Integrable (fun z : DropletClockLaw.Sample L => ((D \ ObservedFrozenProcess.state L D I S t z).card : Real))
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  apply Integrable.of_bound (observed_area_measurable L D I S t).aestronglyMeasurable (D.card : Real)
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (observed_area_bounds L D I S t z).1]
    exact (observed_area_bounds L D I S t z).2
end MathResearchAnalysis.ProtectedAreaPotential
