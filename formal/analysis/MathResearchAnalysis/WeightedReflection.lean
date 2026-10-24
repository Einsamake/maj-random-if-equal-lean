module
public import MathResearchAnalysis.ForbiddenBirthControl
public import MathResearchAnalysis.ProtectedEvolution
public import MathResearchAnalysis.OrthogonalPerimeter
set_option autoImplicit false
/-! Actual sign-reflection transport for grid degrees, boundary length and
weighted raw rates. No corner-charge or quantitative drift bound is assumed. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.WeightedReflection
open InfiniteGridModel (Site north east south west)
open ClippedDiamondGeometry (reflect clippedDomain)
open ProtectedCornerGeometry (mirror mem_mirror)
open GridMajorityPeeling (degree4)
open GridCellBoundary (perimeter)
open ForbiddenBirthControl (weight mass rawWeightedRate)

theorem degree4_mirror (horizontal vertical : Bool) (S : Finset Site) (u : Site) :
    degree4 (mirror horizontal vertical S) u = degree4 S (reflect horizontal vertical u) := by
  unfold degree4
  refine Finset.card_bij (fun v _ => reflect horizontal vertical v) ?_ ?_ ?_
  · intro v hv
    exact Finset.mem_inter.mpr
      ⟨OrthogonalVacantQuadrant.neighbors_reflect horizontal vertical (Finset.mem_inter.mp hv).1,
        (mem_mirror horizontal vertical S v).mp (Finset.mem_inter.mp hv).2⟩
  · intro a _ b _ hab
    exact ClippedDiamondGeometry.reflect_injective horizontal vertical hab
  · intro v hv
    have hn := OrthogonalVacantQuadrant.neighbors_reflect horizontal vertical
      (Finset.mem_inter.mp hv).1
    rw [ClippedDiamondGeometry.reflect_involutive horizontal vertical u] at hn
    have hm : reflect horizontal vertical v ∈ mirror horizontal vertical S := by
      apply (mem_mirror horizontal vertical S _).mpr
      simpa only [ClippedDiamondGeometry.reflect_involutive horizontal vertical v] using
        (Finset.mem_inter.mp hv).2
    exact ⟨reflect horizontal vertical v,Finset.mem_inter.mpr ⟨hn,hm⟩,
      ClippedDiamondGeometry.reflect_involutive horizontal vertical v⟩

theorem degree4_at_reflect (horizontal vertical : Bool) (S : Finset Site) (u : Site) :
    degree4 (mirror horizontal vertical S) (reflect horizontal vertical u) = degree4 S u := by
  rw [degree4_mirror,ClippedDiamondGeometry.reflect_involutive horizontal vertical u]

theorem stable_mirror (horizontal vertical : Bool) {S : Finset Site}
    (hs : DropletModifiedWord.Stable S) : DropletModifiedWord.Stable (mirror horizontal vertical S) := by
  apply (FiniteMajorityPeeling.stable_iff GridMajorityPeeling.neighbors4 _).mpr
  intro u hu
  change 2 ≤ degree4 (mirror horizontal vertical S) u
  rw [degree4_mirror]
  exact (FiniteMajorityPeeling.stable_iff GridMajorityPeeling.neighbors4 _).mp hs
    (reflect horizontal vertical u) ((mem_mirror _ _ _ _).mp hu)

theorem card_mirror (horizontal vertical : Bool) (S : Finset Site) :
    (mirror horizontal vertical S).card = S.card := by
  exact Finset.card_image_of_injective _ (ClippedDiamondGeometry.reflect_injective _ _)

theorem perimeter_mirror (horizontal vertical : Bool) (S : Finset Site) :
    perimeter (mirror horizontal vertical S) = perimeter S := by
  have h0 := GridPerimeterUpdate.perimeter_plus_total_degree S
  have h1 := GridPerimeterUpdate.perimeter_plus_total_degree (mirror horizontal vertical S)
  have hd : (∑ u ∈ mirror horizontal vertical S, degree4 (mirror horizontal vertical S) u) =
      ∑ u ∈ S, degree4 S u := by
    unfold mirror
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro u _
      exact degree4_at_reflect horizontal vertical S u
    · intro a _ b _ hab
      exact ClippedDiamondGeometry.reflect_injective horizontal vertical hab
  rw [hd,card_mirror] at h1
  exact Nat.add_right_cancel (h1.trans h0.symm)

theorem shape_mirror (horizontal vertical : Bool) {S : Finset Site}
    (hs : ProtectedEvolution.Shape S) : ProtectedEvolution.Shape (mirror horizontal vertical S) :=
  ⟨ProtectedCornerGeometry.rowConvex_mirror horizontal vertical hs.1,
    ProtectedCornerGeometry.columnConvex_mirror horizontal vertical hs.2.1,
    OrthogonalVacantQuadrant.fourConnected_mirror horizontal vertical hs.2.2.1,
    stable_mirror horizontal vertical hs.2.2.2⟩

theorem weight_reflect (L : Nat) (horizontal vertical : Bool) (u : Site) :
    weight L (reflect horizontal vertical u) = weight L u := by
  cases horizontal <;> cases vertical <;> simp [weight,reflect]

theorem clippedDomain_mirror (L : Nat) (horizontal vertical : Bool) :
    mirror horizontal vertical (clippedDomain L) = clippedDomain L := by
  ext u
  rw [mem_mirror,ClippedDiamondGeometry.mem_clippedDomain,
    ClippedDiamondGeometry.clipped_reflect_iff,ClippedDiamondGeometry.mem_clippedDomain]

theorem centeredSites_mirror (L : Nat) (hL : 1 ≤ L) (horizontal vertical : Bool) :
    mirror horizontal vertical (ClippedSquareCoordinates.centeredSites L) =
      ClippedSquareCoordinates.centeredSites L := by
  ext u
  rw [mem_mirror,ClippedSquareCoordinates.mem_centeredSites L hL,
    ClippedSquareCoordinates.mem_centeredSites L hL]
  cases horizontal <;> cases vertical <;>
    simp [ClippedSquareCoordinates.centeredSquare,reflect]

theorem protectedSites_reflect_iff (L : Nat) (horizontal vertical : Bool) (u : Site) :
    reflect horizontal vertical u ∈ ClippedProtectedGeometry.protectedSites L ↔
      u ∈ ClippedProtectedGeometry.protectedSites L := by
  rw [ClippedProtectedGeometry.mem_protectedSites_iff_band,
    ClippedProtectedGeometry.mem_protectedSites_iff_band,
    ClippedDiamondGeometry.boundaryBand_reflect_iff]

theorem protectedSites_subset_mirror (L : Nat) (horizontal vertical : Bool) {S : Finset Site}
    (hI : ClippedProtectedGeometry.protectedSites L ⊆ S) :
    ClippedProtectedGeometry.protectedSites L ⊆ mirror horizontal vertical S := by
  intro u hu
  exact (mem_mirror _ _ _ _).mpr (hI ((protectedSites_reflect_iff _ _ _ _).mpr hu))

theorem innerDiamond_subset_mirror (L : Nat) (horizontal vertical : Bool) {S : Finset Site}
    (hI : ClippedProtectedGeometry.innerDiamond L ⊆ S) :
    ClippedProtectedGeometry.innerDiamond L ⊆ mirror horizontal vertical S := by
  intro u hu
  exact (mem_mirror _ _ _ _).mpr
    (hI ((ProtectedCornerGeometry.innerDiamond_reflect_iff _ _ _ _).mpr hu))

theorem mirror_subset_clippedDomain (L : Nat) (horizontal vertical : Bool) {S : Finset Site}
    (hSD : S ⊆ clippedDomain L) : mirror horizontal vertical S ⊆ clippedDomain L := by
  intro u hu
  have h := hSD ((mem_mirror _ _ _ _).mp hu)
  rw [ClippedDiamondGeometry.mem_clippedDomain,
    ClippedDiamondGeometry.clipped_reflect_iff] at h
  exact (ClippedDiamondGeometry.mem_clippedDomain _ _).mpr h

theorem rawWeightedRate_mirror (L : Nat) (horizontal vertical : Bool) (E S : Finset Site) :
    rawWeightedRate (weight L) (mirror horizontal vertical E) (mirror horizontal vertical S) =
      rawWeightedRate (weight L) E S := by
  unfold rawWeightedRate
  change (∑ u ∈ E.image (reflect horizontal vertical), _) = _
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro u _
    rw [ForbiddenBirthControl.rawWeightedRate_local,ForbiddenBirthControl.rawWeightedRate_local,
      weight_reflect,MaskedAreaGenerator.raw_local_rate,MaskedAreaGenerator.raw_local_rate,
      degree4_at_reflect]
    simp only [mem_mirror,ClippedDiamondGeometry.reflect_involutive horizontal vertical u]
  · intro a _ b _ hab
    exact ClippedDiamondGeometry.reflect_injective horizontal vertical hab

theorem actual_rawWeightedRate_mirror (L : Nat) (hL : 1 ≤ L) (horizontal vertical : Bool) (S : Finset Site) :
    rawWeightedRate (weight L) (ClippedSquareCoordinates.centeredSites L) (mirror horizontal vertical S) =
      rawWeightedRate (weight L) (ClippedSquareCoordinates.centeredSites L) S := by
  simpa only [centeredSites_mirror L hL] using
    rawWeightedRate_mirror L horizontal vertical (ClippedSquareCoordinates.centeredSites L) S

end MathResearchAnalysis.WeightedReflection
