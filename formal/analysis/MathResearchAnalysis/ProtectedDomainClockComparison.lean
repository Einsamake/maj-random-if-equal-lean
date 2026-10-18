module

public import MathResearchAnalysis.ClippedProtectedGeometry
public import MathResearchAnalysis.WholeSquareClockTransport

set_option autoImplicit false

/-!
# The actual CMST protected domain in the finite clock model

The protected set is the inner diamond together with its external four-neighbour
boundary. It is not replaced by the inner diamond alone. All physical-time
probabilities below use the original clock/fair-mark product measure. First-loss
indices remain extended natural event indices, not physical clock times.
-/

@[expose] public noncomputable section

namespace MathResearchAnalysis.ProtectedDomainClockComparison

open InfiniteGridModel MeasureTheory

abbrev Vertex (L : Nat) := DropletClockLaw.Vertex L

/-- The exact finite vertices representing D union its external boundary. -/
def protectedVertices (L : Nat) : Finset (Vertex L) :=
  Finset.univ.filter (fun v =>
    ClippedSquareCoordinates.recenter L v ∈ ClippedProtectedGeometry.protectedSites L)

theorem mem_protectedVertices (L : Nat) (v : Vertex L) :
    v ∈ protectedVertices L ↔
      ClippedSquareCoordinates.recenter L v ∈ ClippedProtectedGeometry.protectedSites L := by
  simp [protectedVertices]

theorem image_protectedVertices (L : Nat) (hL : 40 ≤ L) :
    (protectedVertices L).image (ClippedSquareCoordinates.recenter L) =
      ClippedProtectedGeometry.protectedSites L := by
  ext z
  constructor
  · rintro hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact (mem_protectedVertices L v).mp hv
  · intro hz
    have hc := ClippedProtectedGeometry.protectedSites_subset_clippedDomain hL hz
    have hs := (ClippedDiamondGeometry.mem_clippedDomain L z).mp hc
    obtain ⟨v, rfl⟩ := (ClippedSquareCoordinates.exists_recenter_iff L (by omega) z).mpr
      ⟨hs.1, hs.2.1⟩
    exact Finset.mem_image.mpr ⟨v, (mem_protectedVertices L v).mpr hz, rfl⟩

theorem protectedVertices_nonempty (L : Nat) (hL : 40 ≤ L) :
    (protectedVertices L).Nonempty := by
  obtain ⟨z, hz⟩ := ClippedProtectedGeometry.protectedSites_nonempty L
  rw [← image_protectedVertices L hL] at hz
  obtain ⟨v, hv, _⟩ := Finset.mem_image.mp hz
  exact ⟨v, hv⟩

theorem protectedVertices_subset_clippedVertices (L : Nat) (hL : 40 ≤ L) :
    protectedVertices L ⊆ ClippedSquareCoordinates.clippedVertices L := by
  intro v hv
  exact (ClippedSquareCoordinates.mem_clippedVertices L v).mpr
    (ClippedProtectedGeometry.protectedSites_subset_clippedDomain hL
      ((mem_protectedVertices L v).mp hv))

/-- Presence of every finite protected spin is exactly presence of D union boundary. -/
theorem protected_present_iff (L : Nat) (hL : 40 ≤ L) (S : Finset Site) :
    (∀ v ∈ protectedVertices L, ClippedSquareCoordinates.clippedConfig L S v = true) ↔
      ClippedProtectedGeometry.protectedSites L ⊆ S := by
  constructor
  · intro h z hz
    rw [← image_protectedVertices L hL] at hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact of_decide_eq_true (h v hv)
  · intro h v hv
    exact decide_eq_true (h ((mem_protectedVertices L v).mp hv))

theorem protected_initially_present (L : Nat) (hL : 40 ≤ L) :
    ∀ v ∈ protectedVertices L, ClippedSquareCoordinates.clippedConfig L
      (ClippedDiamondGeometry.clippedDomain L) v = true :=
  (protected_present_iff L hL _).mpr
    (ClippedProtectedGeometry.protectedSites_subset_clippedDomain hL)

theorem image_occupied_true (L : Nat) :
    CenteredPeelingTransport.image L (CenteredPeelingTransport.occupied
      (fun _ : Vertex L => true)) = ClippedSquareCoordinates.centeredSites L := by
  simp [CenteredPeelingTransport.image, CenteredPeelingTransport.occupied,
    ClippedSquareCoordinates.centeredSites]

/-- No arbitrary protected-set premise remains in this physical-time comparison. -/
theorem original_extinction_measure_le_actual_protected_missing
    (L : Nat) (hL : 40 ≤ L) (t : Real) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L) t
        (fun _ => true) z = fun _ => false} ≤
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | ¬ ∀ v ∈ protectedVertices L, DropletClockLaw.endpoint L true
        (ClippedDiamondGeometry.clippedDomain L) (ClippedDiamondGeometry.clippedDomain L)
        t z v = true} := by
  apply WholeSquareClockTransport.original_extinction_measure_le_clipped_protected_missing
    L (by omega) _ (Finset.Subset.refl _) (fun _ => true) _
    (protectedVertices L) (protectedVertices_nonempty L hL) t
  rw [image_occupied_true]
  exact ClippedSquareCoordinates.clippedDomain_subset_centeredSites L (by omega)

/-- The same bound stated on the actual centered set, including its external boundary. -/
theorem original_extinction_measure_le_actual_set_missing
    (L : Nat) (hL : 40 ≤ L) (t : Real) :
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | ClockExecutionLaw.endpoint (ClippedSquareCoordinates.parameter L) t
        (fun _ => true) z = fun _ => false} ≤
    ClockWordMarks.measure (ClippedSquareCoordinates.parameter L)
      {z | ¬ ClippedProtectedGeometry.protectedSites L ⊆
        DropletModifiedWord.modifiedWord (ClippedDiamondGeometry.clippedDomain L)
          (ClippedDiamondGeometry.clippedDomain L)
          (DropletClockLaw.markedEvents L (ClockEventWord.word z.1 t) z.2)} := by
  have hset : {z : DropletClockLaw.Sample L | ¬ ∀ v ∈ protectedVertices L,
      DropletClockLaw.endpoint L true (ClippedDiamondGeometry.clippedDomain L)
        (ClippedDiamondGeometry.clippedDomain L) t z v = true} =
      {z | ¬ ClippedProtectedGeometry.protectedSites L ⊆
        DropletModifiedWord.modifiedWord (ClippedDiamondGeometry.clippedDomain L)
          (ClippedDiamondGeometry.clippedDomain L)
          (DropletClockLaw.markedEvents L (ClockEventWord.word z.1 t) z.2)} := by
    ext z
    exact not_congr (protected_present_iff L hL _)
  rw [← hset]
  exact original_extinction_measure_le_actual_protected_missing L hL t

/-- First event index of loss of this concrete CMST protected set; infinity is retained. -/
def protectedExitIndex (L : Nat) (events : Nat → DropletModifiedWord.Event) : ℕ∞ :=
  DropletDomainComparison.exitTime (ClippedDiamondGeometry.clippedDomain L)
    (ClippedDiamondGeometry.clippedDomain L) (ClippedProtectedGeometry.protectedSites L) events

theorem protectedExitIndex_le_rawRecoveryIndex (L : Nat) (hL : 40 ≤ L)
    (events : Nat → DropletModifiedWord.Event) :
    protectedExitIndex L events ≤ DropletDomainComparison.rawRecoveryIndex
      (ClippedSquareCoordinates.centeredSites L) (ClippedSquareCoordinates.centeredSites L)
      events := by
  have hs := ClippedSquareCoordinates.clippedDomain_subset_centeredSites L (by omega)
  exact DropletDomainComparison.exitTime_le_rawRecoveryIndex hs (Finset.Subset.refl _) hs
    (ClippedProtectedGeometry.protectedSites_nonempty L) events

theorem protectedExitIndex_pos (L : Nat) (hL : 40 ≤ L)
    (events : Nat → DropletModifiedWord.Event) : 0 < protectedExitIndex L events := by
  apply lt_of_not_ge
  intro hzero
  obtain ⟨j, hj, hmissing⟩ :=
    (DropletDomainComparison.exitTime_le_nat_iff _ _ _ events 0).mp hzero
  have hj0 : j = 0 := by omega
  subst j
  exact hmissing (ClippedProtectedGeometry.protectedSites_subset_clippedDomain hL)

end MathResearchAnalysis.ProtectedDomainClockComparison
