module

public import MathResearchAnalysis.GridPerimeterDynamics
public import MathResearchAnalysis.ClippedBoundaryPerimeter
public import MathResearchAnalysis.DropletClockLaw

set_option autoImplicit false

/-!
# Concrete clipped-word and actual physical-clock perimeter budgets

The word is the actual clock event word and retains its original fair mark
identities. The occupied set below represents the previously defined genuine
endpoint exactly. The bound holds pointwise at every physical endpoint; it
is not a generator, stopped-process law or recovery-time estimate.
-/

@[expose] public noncomputable section
namespace MathResearchAnalysis.ClippedPerimeterBudget

open GridCellBoundary (Site perimeter)
open ClippedDiamondGeometry (clippedDomain)
open DropletModifiedWord GridPerimeterDynamics

theorem modifiedWord_budget (L : Nat) (D : Finset Site) (w : List Event) :
    perimeter (modifiedWord D (clippedDomain L) w) + 2 * wordLoss D (clippedDomain L) w ≤
      8 * L + 4 := by
  simpa only [ClippedBoundaryPerimeter.physical_perimeter] using
    modifiedWord_perimeter_loss_budget D (clippedDomain L) w

theorem wordLoss_le (L : Nat) (D : Finset Site) (w : List Event) :
    wordLoss D (clippedDomain L) w ≤ 4 * L + 2 := by
  have h := modifiedWord_budget L D w
  omega

def clockOccupied (L : Nat) (D S : Finset Site) (t : Real) (z : DropletClockLaw.Sample L) :
    Finset Site := modifiedWord D S
      (DropletClockLaw.markedEvents L (ClockEventWord.word z.1 t) z.2)

def clockCleanupLoss (L : Nat) (D : Finset Site) (t : Real) (z : DropletClockLaw.Sample L) : Nat :=
  wordLoss D (clippedDomain L)
    (DropletClockLaw.markedEvents L (ClockEventWord.word z.1 t) z.2)

theorem clockOccupied_exact_endpoint (L : Nat) (D S : Finset Site) (t : Real)
    (z : DropletClockLaw.Sample L) :
    ClippedSquareCoordinates.clippedConfig L (clockOccupied L D S t z) =
      DropletClockLaw.endpoint L true D S t z := rfl

theorem actual_clock_budget (L : Nat) (D : Finset Site) (t : Real)
    (z : DropletClockLaw.Sample L) :
    perimeter (clockOccupied L D (clippedDomain L) t z) + 2 * clockCleanupLoss L D t z ≤
      8 * L + 4 :=
  modifiedWord_budget L D (DropletClockLaw.markedEvents L (ClockEventWord.word z.1 t) z.2)

theorem actual_clock_cleanup_loss_le (L : Nat) (D : Finset Site) (t : Real)
    (z : DropletClockLaw.Sample L) : clockCleanupLoss L D t z ≤ 4 * L + 2 :=
  wordLoss_le L D (DropletClockLaw.markedEvents L (ClockEventWord.word z.1 t) z.2)

end MathResearchAnalysis.ClippedPerimeterBudget
