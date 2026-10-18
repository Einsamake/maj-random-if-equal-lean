module

public import MathResearchAnalysis.DropletClockLaw

set_option autoImplicit false

/-!
# Whole-square centered execution and the original clock endpoint

Every finite vertex lies in the whole centered-square mask. Its masked raw
word therefore performs exactly the original finite zero-boundary cell updates.
The newest-first clock word is reversed once, identically on both sides.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.WholeSquareClockTransport

open InfiniteGridModel

theorem clippedConfig_image (L : Nat)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L))) :
    ClippedSquareCoordinates.clippedConfig L (CenteredPeelingTransport.image L S) =
      GridMajorityPeeling.finiteState S := by
  funext v
  simp only [ClippedSquareCoordinates.clippedConfig, GridMajorityPeeling.state,
    GridMajorityPeeling.finiteState, CenteredPeelingTransport.mem_image_recenter]

theorem maskedRawStep_image_wholeSquare (L : Nat) (hL : 1 ≤ L)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)))
    (v : SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)) (tie : Bool) :
    DropletModifiedWord.maskedRawStep (ClippedSquareCoordinates.centeredSites L)
        (CenteredPeelingTransport.image L S) (ClippedSquareCoordinates.recenter L v) tie =
      CenteredPeelingTransport.image L (CenteredPeelingTransport.finiteRawStep S v tie) := by
  have hv : ClippedSquareCoordinates.recenter L v ∈ ClippedSquareCoordinates.centeredSites L :=
    Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
  simp only [DropletModifiedWord.maskedRawStep, hv, ite_true]
  exact CenteredPeelingTransport.rawStep_image_recenter L hL S v tie

theorem rawWord_image_execute (L : Nat) (hL : 1 ≤ L)
    (S : Finset (SquareTasks.Vertex (ClippedSquareCoordinates.parameter L)))
    (events : List (SquareSpin.Event (ClippedSquareCoordinates.parameter L)))
    (η : SquareSpin.Event (ClippedSquareCoordinates.parameter L) → Bool) :
    DropletModifiedWord.rawWord (ClippedSquareCoordinates.centeredSites L)
        (CenteredPeelingTransport.image L S)
        (events.map (fun e => (ClippedSquareCoordinates.recenter L e.1, η e))) =
      CenteredPeelingTransport.image L (CenteredPeelingTransport.occupied
        (MarkedEventTrace.execute η events (GridMajorityPeeling.finiteState S))) := by
  induction events generalizing S with
  | nil =>
    simp only [List.map_nil, DropletModifiedWord.rawWord_nil, MarkedEventTrace.execute,
      EventTrace.execute_nil, CenteredPeelingTransport.occupied_finiteState]
  | cons e events ih =>
    change DropletModifiedWord.rawWord _
      (DropletModifiedWord.maskedRawStep _ (CenteredPeelingTransport.image L S)
        (ClippedSquareCoordinates.recenter L e.1) (η e)) _ = _
    rw [maskedRawStep_image_wholeSquare L hL S e.1 (η e), ih,
      CenteredPeelingTransport.finiteState_finiteRawStep]
    rfl

theorem rawWord_clippedConfig_execute (L : Nat) (hL : 1 ≤ L)
    (g : SquareSpin.Config (ClippedSquareCoordinates.parameter L))
    (events : List (SquareSpin.Event (ClippedSquareCoordinates.parameter L)))
    (η : SquareSpin.Event (ClippedSquareCoordinates.parameter L) → Bool) :
    ClippedSquareCoordinates.clippedConfig L
        (DropletModifiedWord.rawWord (ClippedSquareCoordinates.centeredSites L)
          (CenteredPeelingTransport.image L (CenteredPeelingTransport.occupied g))
          (events.map (fun e => (ClippedSquareCoordinates.recenter L e.1, η e)))) =
      MarkedEventTrace.execute η events g := by
  rw [rawWord_image_execute L hL, clippedConfig_image,
    CenteredPeelingTransport.finiteState_occupied, CenteredPeelingTransport.finiteState_occupied]

theorem raw_run_wholeSquare_execute (L : Nat) (hL : 1 ≤ L)
    (g : DropletClockLaw.Config L) (events : List (DropletClockLaw.Event L))
    (η : DropletClockLaw.Event L → Bool) :
    DropletClockLaw.run L false (ClippedSquareCoordinates.centeredSites L)
      (CenteredPeelingTransport.image L (CenteredPeelingTransport.occupied g)) events η =
      MarkedEventTrace.execute η events.reverse g := by
  exact rawWord_clippedConfig_execute L hL g events.reverse η

theorem raw_endpoint_wholeSquare (L : Nat) (hL : 1 ≤ L)
    (g : DropletClockLaw.Config L) (t : Real) (z : DropletClockLaw.Sample L) :
    DropletClockLaw.endpoint L false (ClippedSquareCoordinates.centeredSites L)
      (CenteredPeelingTransport.image L (CenteredPeelingTransport.occupied g)) t z =
      ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L) t g z := by
  exact raw_run_wholeSquare_execute L hL g (ClockEventWord.word z.1 t) z.2

theorem raw_endpoint_wholeSquare_law (L : Nat) (hL : 1 ≤ L)
    (g : DropletClockLaw.Config L) (t : Real) :
    MeasureTheory.Measure.map
      (DropletClockLaw.endpoint L false (ClippedSquareCoordinates.centeredSites L)
        (CenteredPeelingTransport.image L (CenteredPeelingTransport.occupied g)) t)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) =
    MeasureTheory.Measure.map
      (ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L) t g)
      (ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)) := by
  congr 1
  exact funext (raw_endpoint_wholeSquare L hL g t)

/-- The larger process is the original actual clock endpoint, on its true law.
The smaller process uses the genuine clipped mask and actual cleanup. -/
theorem original_extinction_measure_le_clipped_protected_missing
    (L : Nat) (hL : 1 ≤ L)
    (S : Finset InfiniteGridModel.Site) (hSD : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    (g : DropletClockLaw.Config L)
    (hST : S ⊆ CenteredPeelingTransport.image L (CenteredPeelingTransport.occupied g))
    (I : Finset (DropletClockLaw.Vertex L)) (hI : I.Nonempty) (t : Real) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L) t g z = fun _ => false} ≤
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | ¬ ∀ v ∈ I, DropletClockLaw.endpoint L true
        (ClippedDiamondGeometry.clippedDomain L) S t z v = true} := by
  simpa only [raw_endpoint_wholeSquare L hL g t] using
    DropletClockLaw.raw_extinction_measure_le_protected_missing L
      (ClippedSquareCoordinates.clippedDomain_subset_centeredSites L hL) hSD hST I hI t
end MathResearchAnalysis.WholeSquareClockTransport

