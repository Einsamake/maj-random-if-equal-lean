module

public import MathResearchAnalysis.ClippedBoundaryBox
public import MathResearchAnalysis.GridBoundaryIncidence

set_option autoImplicit false

/-!
# Actual initial clipped boundaries have no alternating corner pattern

Box constraints propagate to the two remaining cells of a 2x2 square. The sum
of the opposite L1 norms is the same for both diagonals, so the remaining two
cells cannot both violate the same diamond bound. This derives, rather than
assumes, local one-in/one-out incidence of the actual initial boundary.
-/

@[expose] public section

namespace MathResearchAnalysis.ClippedBoundaryIncidence

open InfiniteGridModel

abbrev Site := InfiniteGridModel.Site

theorem occupied_ne_diagonal_forces_cross (L : Nat) (a : Site)
    (ha : a ∈ ClippedDiamondGeometry.clippedDomain L)
    (hne : north (east a) ∈ ClippedDiamondGeometry.clippedDomain L) :
    east a ∈ ClippedDiamondGeometry.clippedDomain L ∨
      north a ∈ ClippedDiamondGeometry.clippedDomain L := by
  have hA := (ClippedDiamondGeometry.mem_clippedDomain L a).mp ha
  have hNE := (ClippedDiamondGeometry.mem_clippedDomain L (north (east a))).mp hne
  dsimp [ClippedDiamondGeometry.clipped, north, east] at hA hNE
  by_cases he : east a ∈ ClippedDiamondGeometry.clippedDomain L
  · exact Or.inl he
  · apply Or.inr
    have hnE : ¬ |a.1 + 1| + |a.2| ≤ (L : Int) + 1 := by
      intro h
      exact he ((ClippedDiamondGeometry.mem_clippedDomain L (east a)).mpr
        ⟨hNE.1, hA.2.1, h⟩)
    apply (ClippedDiamondGeometry.mem_clippedDomain L (north a)).mpr
    refine ⟨hA.1, hNE.2.1, ?_⟩
    dsimp [north]
    omega

theorem occupied_cross_forces_ne_diagonal (L : Nat) (a : Site)
    (he : east a ∈ ClippedDiamondGeometry.clippedDomain L)
    (hn : north a ∈ ClippedDiamondGeometry.clippedDomain L) :
    a ∈ ClippedDiamondGeometry.clippedDomain L ∨
      north (east a) ∈ ClippedDiamondGeometry.clippedDomain L := by
  have hE := (ClippedDiamondGeometry.mem_clippedDomain L (east a)).mp he
  have hN := (ClippedDiamondGeometry.mem_clippedDomain L (north a)).mp hn
  dsimp [ClippedDiamondGeometry.clipped, north, east] at hE hN
  by_cases ha : a ∈ ClippedDiamondGeometry.clippedDomain L
  · exact Or.inl ha
  · apply Or.inr
    have hnA : ¬ |a.1| + |a.2| ≤ (L : Int) + 1 := by
      intro h
      exact ha ((ClippedDiamondGeometry.mem_clippedDomain L a).mpr ⟨hN.1, hE.2.1, h⟩)
    apply (ClippedDiamondGeometry.mem_clippedDomain L (north (east a))).mpr
    refine ⟨hE.1, hN.2.1, ?_⟩
    dsimp [north, east]
    omega

theorem no_checkerboard (L : Nat) :
    GridBoundaryIncidence.NoCheckerboard (ClippedDiamondGeometry.clippedDomain L) := by
  intro a
  constructor
  · rintro ⟨ha, hne, he, hn⟩
    rcases occupied_ne_diagonal_forces_cross L a ha hne with h | h
    · exact he h
    · exact hn h
  · rintro ⟨ha, hne, he, hn⟩
    rcases occupied_cross_forces_ne_diagonal L a he hn with h | h
    · exact ha h
    · exact hne h

theorem vertices_eq (L : Nat) :
    GridBoundaryIncidence.vertices (ClippedDiamondGeometry.clippedDomain L) =
      ClippedBoundaryBox.vertices L := rfl

theorem vertex_incidence_one (L : Nat) (p : Site)
    (hp : p ∈ ClippedBoundaryBox.vertices L) :
    (GridBoundaryIncidence.outgoing (ClippedDiamondGeometry.clippedDomain L) p).card = 1 ∧
      (GridBoundaryIncidence.incoming (ClippedDiamondGeometry.clippedDomain L) p).card = 1 :=
  GridBoundaryIncidence.vertex_incidence_one _ (no_checkerboard L) p hp

theorem source_injective_on_boundary (L : Nat) :
    Set.InjOn GridCellBoundary.source
      (ClippedDiamondGeometry.clippedDomain L |> GridCellBoundary.boundary :
        Set GridCellBoundary.HalfEdge) := by
  intro e he f hf hef
  have hp := ClippedBoundaryBox.source_mem_vertices L he
  have hc := (vertex_incidence_one L (GridCellBoundary.source e) hp).1
  have he' := (GridBoundaryIncidence.mem_outgoing _ _ e).mpr ⟨he, rfl⟩
  have hf' := (GridBoundaryIncidence.mem_outgoing _ _ f).mpr ⟨hf, hef.symm⟩
  exact (Finset.card_le_one.mp (Nat.le_of_eq hc)) e he' f hf'

theorem target_injective_on_boundary (L : Nat) :
    Set.InjOn GridCellBoundary.target
      (ClippedDiamondGeometry.clippedDomain L |> GridCellBoundary.boundary :
        Set GridCellBoundary.HalfEdge) := by
  intro e he f hf hef
  have hp := ClippedBoundaryBox.target_mem_vertices L he
  have hc := (vertex_incidence_one L (GridCellBoundary.target e) hp).2
  have he' := (GridBoundaryIncidence.mem_incoming _ _ e).mpr ⟨he, rfl⟩
  have hf' := (GridBoundaryIncidence.mem_incoming _ _ f).mpr ⟨hf, hef.symm⟩
  exact (Finset.card_le_one.mp (Nat.le_of_eq hc)) e he' f hf'

end MathResearchAnalysis.ClippedBoundaryIncidence
