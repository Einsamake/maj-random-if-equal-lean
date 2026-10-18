module

public import MathResearchAnalysis.ClippedBoundaryPerimeter
public import Mathlib.Logic.Relation

set_option autoImplicit false

/-!
# Connectivity of the actual exposed clipped-droplet facets

Touch is sharing one of the actual doubled-coordinate endpoints. BoundaryStep
requires both facets to belong to the existing exposed-cell boundary. Path is
the finite reflexive transitive closure of this relation. The proof follows
adjacent column tops and transports those paths by a proved quarter-turn.
This is a connectivity statement, not a Jordan or simple-cycle theorem.
-/

@[expose] public section

namespace MathResearchAnalysis.ClippedBoundaryConnectivity

open GridCellBoundary ClippedBoundaryPerimeter ClippedOrthogonalSections
open ClippedDiamondGeometry (clippedDomain)

def Touch (e f : HalfEdge) : Prop :=
  source e = source f ∨ source e = target f ∨
    target e = source f ∨ target e = target f

def BoundaryStep (L : Nat) (e f : HalfEdge) : Prop :=
  e ∈ boundary (clippedDomain L) ∧ f ∈ boundary (clippedDomain L) ∧ Touch e f

abbrev Path (L : Nat) : HalfEdge → HalfEdge → Prop :=
  Relation.ReflTransGen (BoundaryStep L)

theorem touch_symm {e f : HalfEdge} (h : Touch e f) : Touch f e := by
  rcases h with h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (Or.inr h.symm))

theorem boundaryStep_symm {L : Nat} {e f : HalfEdge} (h : BoundaryStep L e f) :
    BoundaryStep L f e := ⟨h.2.1, h.1, touch_symm h.2.2⟩

theorem path_reverse {L : Nat} {e f : HalfEdge} (h : Path L e f) : Path L f e := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
      exact (Relation.ReflTransGen.single (boundaryStep_symm hs)).trans ih

theorem path_of_source_eq_target {L : Nat} {e f : HalfEdge}
    (he : e ∈ boundary (clippedDomain L)) (hf : f ∈ boundary (clippedDomain L))
    (h : source e = target f) : Path L e f :=
  Relation.ReflTransGen.single ⟨he, hf, Or.inr (Or.inl h)⟩

theorem facet_mem (L : Nat) (d : Direction) (a : Int) (ha : |a| ≤ (L : Int)) :
    facet L (d, a) ∈ boundary (clippedDomain L) :=
  facet_mem_boundary L (d, a) ((mem_facetIndices L (d, a)).mpr ha)

theorem sectionRadius_succ_bounds (L : Nat) (a : Int) :
    sectionRadius L a - 1 ≤ sectionRadius L (a + 1) ∧
      sectionRadius L (a + 1) ≤ sectionRadius L a + 1 := by
  have h1 : |a + 1| ≤ |a| + 1 := by
    simpa only [abs_one] using abs_add_le a (1 : Int)
  have h2 : |a| ≤ |a + 1| + 1 := by
    calc
      |a| = |(a + 1) + (-1)| := by congr 1; omega
      _ ≤ |a + 1| + |(-1 : Int)| := abs_add_le (a + 1) (-1)
      _ = |a + 1| + 1 := by norm_num
  simp only [sectionRadius, min_def]
  split_ifs <;> omega

theorem sectionRadius_succ_cases (L : Nat) (a : Int) :
    sectionRadius L (a + 1) = sectionRadius L a ∨
      sectionRadius L (a + 1) = sectionRadius L a + 1 ∨
      sectionRadius L (a + 1) = sectionRadius L a - 1 := by
  have h := sectionRadius_succ_bounds L a
  omega

theorem north_adjacent_path (L : Nat) (a : Int)
    (ha : |a| ≤ (L : Int)) (ha1 : |a + 1| ≤ (L : Int)) :
    Path L (facet L (0, a)) (facet L (0, a + 1)) := by
  have h0 := facet_mem L 0 a ha
  have h1 := facet_mem L 0 (a + 1) ha1
  rcases sectionRadius_succ_cases L a with hr | hr | hr
  · apply path_of_source_eq_target h0 h1
    apply Prod.ext
    · change 2 * a + 1 = 2 * (a + 1) - 1
      omega
    · change 2 * sectionRadius L a + 1 = 2 * sectionRadius L (a + 1) + 1
      omega
  · let bridge : HalfEdge := ((a + 1, sectionRadius L (a + 1)), 3)
    have hbridge : bridge ∈ boundary (clippedDomain L) := by
      apply (mem_boundary _ _).mpr
      constructor
      · simpa only [bridge, facet, ite_true] using boundary_owner_mem h1
      · have hn := boundary_neighbor_not_mem h0
        simpa [bridge, facet, neighbor, InfiniteGridModel.north,
          InfiniteGridModel.west, hr] using hn
    have hp0 : Path L (facet L (0, a)) bridge := by
      apply path_of_source_eq_target h0 hbridge
      apply Prod.ext
      · change 2 * a + 1 = 2 * (a + 1) - 1
        omega
      · change 2 * sectionRadius L a + 1 = 2 * sectionRadius L (a + 1) - 1
        omega
    have hp1 : Path L bridge (facet L (0, a + 1)) := by
      apply path_of_source_eq_target hbridge h1
      rfl
    exact hp0.trans hp1
  · let bridge : HalfEdge := ((a, sectionRadius L a), 1)
    have hbridge : bridge ∈ boundary (clippedDomain L) := by
      apply (mem_boundary _ _).mpr
      constructor
      · simpa only [bridge, facet, ite_true] using boundary_owner_mem h0
      · have hn := boundary_neighbor_not_mem h1
        simpa [bridge, facet, neighbor, InfiniteGridModel.north,
          InfiniteGridModel.east, hr] using hn
    have hp0 : Path L (facet L (0, a)) bridge := by
      apply path_of_source_eq_target h0 hbridge
      rfl
    have hp1 : Path L bridge (facet L (0, a + 1)) := by
      apply path_of_source_eq_target hbridge h1
      apply Prod.ext
      · change 2 * a + 1 = 2 * (a + 1) - 1
        omega
      · change 2 * sectionRadius L a - 1 = 2 * sectionRadius L (a + 1) + 1
        omega
    exact hp0.trans hp1

theorem north_path_of_le (L : Nat) (a b : Int)
    (ha : |a| ≤ (L : Int)) (hb : |b| ≤ (L : Int)) (hab : a ≤ b) :
    Path L (facet L (0, a)) (facet L (0, b)) := by
  have haux : ∀ n : Nat, a + (n : Int) ≤ b →
      Path L (facet L (0, a)) (facet L (0, a + (n : Int))) := by
    intro n
    induction n with
    | zero =>
        intro _
        simpa only [Nat.cast_zero, add_zero] using
          (Relation.ReflTransGen.refl : Path L (facet L (0, a)) (facet L (0, a)))
    | succ n ih =>
        intro hn
        have hprev : a + (n : Int) ≤ b := by omega
        have hc : |a + (n : Int)| ≤ (L : Int) := by
          have hA := abs_le.mp ha
          have hB := abs_le.mp hb
          exact abs_le.mpr ⟨by omega, by omega⟩
        have hc1 : |a + (n : Int) + 1| ≤ (L : Int) := by
          have hA := abs_le.mp ha
          have hB := abs_le.mp hb
          exact abs_le.mpr ⟨by omega, by omega⟩
        have hp := (ih hprev).trans (north_adjacent_path L (a + (n : Int)) hc hc1)
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hp
  have hn : a + ((b - a).toNat : Int) = b := by omega
  simpa only [hn] using haux (b - a).toNat (by omega)

theorem north_path (L : Nat) (a b : Int)
    (ha : |a| ≤ (L : Int)) (hb : |b| ≤ (L : Int)) :
    Path L (facet L (0, a)) (facet L (0, b)) := by
  by_cases hab : a ≤ b
  · exact north_path_of_le L a b ha hb hab
  · exact path_reverse (north_path_of_le L b a hb ha (by omega))

def turnSite (z : GridCellBoundary.Site) : GridCellBoundary.Site := (-z.2, z.1)

def turnDirection (d : Direction) : Direction :=
  ⟨(d.val + 3) % 4, Nat.mod_lt _ (by decide)⟩

def turnEdge (e : HalfEdge) : HalfEdge := (turnSite e.1, turnDirection e.2)

theorem turn_mem_iff (L : Nat) (z : GridCellBoundary.Site) :
    turnSite z ∈ clippedDomain L ↔ z ∈ clippedDomain L := by
  simp only [ClippedDiamondGeometry.mem_clippedDomain,
    ClippedDiamondGeometry.clipped, turnSite, abs_neg]
  omega

theorem neighbor_turn (z : GridCellBoundary.Site) (d : Direction) :
    neighbor (turnSite z) (turnDirection d) = turnSite (neighbor z d) := by
  fin_cases d <;> apply Prod.ext <;>
    norm_num [turnSite, turnDirection, neighbor, InfiniteGridModel.north,
      InfiniteGridModel.east, InfiniteGridModel.south, InfiniteGridModel.west] <;> omega

theorem source_turn (e : HalfEdge) : source (turnEdge e) = turnSite (source e) := by
  rcases e with ⟨z, d⟩
  fin_cases d <;> apply Prod.ext <;>
    norm_num [turnEdge, turnSite, turnDirection, source] <;> omega

theorem target_turn (e : HalfEdge) : target (turnEdge e) = turnSite (target e) := by
  rcases e with ⟨z, d⟩
  fin_cases d <;> apply Prod.ext <;>
    norm_num [turnEdge, turnSite, turnDirection, target] <;> omega

theorem turn_boundary_mem {L : Nat} {e : HalfEdge}
    (he : e ∈ boundary (clippedDomain L)) :
    turnEdge e ∈ boundary (clippedDomain L) := by
  have h := (mem_boundary _ _).mp he
  apply (mem_boundary _ _).mpr
  constructor
  · exact (turn_mem_iff L e.1).mpr h.1
  · intro hn
    have hn' : turnSite (neighbor e.1 e.2) ∈ clippedDomain L := by
      rw [← neighbor_turn]
      exact hn
    exact h.2 ((turn_mem_iff L _).mp hn')

theorem touch_turn {e f : HalfEdge} (h : Touch e f) :
    Touch (turnEdge e) (turnEdge f) := by
  simp only [Touch, source_turn, target_turn]
  rcases h with h | h | h | h
  · exact Or.inl (congrArg turnSite h)
  · exact Or.inr (Or.inl (congrArg turnSite h))
  · exact Or.inr (Or.inr (Or.inl (congrArg turnSite h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg turnSite h)))

theorem path_turn {L : Nat} {e f : HalfEdge} (h : Path L e f) :
    Path L (turnEdge e) (turnEdge f) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
      exact ih.tail ⟨turn_boundary_mem hs.1, turn_boundary_mem hs.2.1, touch_turn hs.2.2⟩

theorem turn_facet_north (L : Nat) (a : Int) :
    turnEdge (facet L (0, a)) = facet L (3, a) := by
  simp [turnEdge, turnSite, turnDirection, facet]

theorem turn_facet_east (L : Nat) (a : Int) :
    turnEdge (facet L (1, a)) = facet L (0, -a) := by
  simp [turnEdge, turnSite, turnDirection, facet, sectionRadius_neg]

theorem turn_facet_south (L : Nat) (a : Int) :
    turnEdge (facet L (2, a)) = facet L (1, a) := by
  simp [turnEdge, turnSite, turnDirection, facet]

theorem turn_facet_west (L : Nat) (a : Int) :
    turnEdge (facet L (3, a)) = facet L (2, -a) := by
  simp [turnEdge, turnSite, turnDirection, facet, sectionRadius_neg]

theorem west_path (L : Nat) (a b : Int)
    (ha : |a| ≤ (L : Int)) (hb : |b| ≤ (L : Int)) :
    Path L (facet L (3, a)) (facet L (3, b)) := by
  simpa only [turn_facet_north] using path_turn (north_path L a b ha hb)

theorem south_path (L : Nat) (a b : Int)
    (ha : |a| ≤ (L : Int)) (hb : |b| ≤ (L : Int)) :
    Path L (facet L (2, a)) (facet L (2, b)) := by
  have h := west_path L (-a) (-b) (by simpa only [abs_neg] using ha)
    (by simpa only [abs_neg] using hb)
  simpa only [turn_facet_west, neg_neg] using path_turn h

theorem east_path (L : Nat) (a b : Int)
    (ha : |a| ≤ (L : Int)) (hb : |b| ≤ (L : Int)) :
    Path L (facet L (1, a)) (facet L (1, b)) := by
  simpa only [turn_facet_south] using path_turn (south_path L a b ha hb)

theorem sectionRadius_one (L : Nat) : sectionRadius L 1 = (L : Int) := by
  simp [sectionRadius]

theorem sectionRadius_extreme (L : Nat) (hL : 1 ≤ L) :
    sectionRadius L (L : Int) = 1 := by
  unfold sectionRadius
  rw [abs_of_nonneg (Int.natCast_nonneg L)]
  have hsub : (L : Int) + 1 - (L : Int) = 1 := by omega
  rw [hsub]
  exact min_eq_right (by exact_mod_cast hL)

theorem north_zero_to_east_zero (L : Nat) (hL : 1 ≤ L) :
    Path L (facet L (0, 0)) (facet L (1, 0)) := by
  have h0 : |(0 : Int)| ≤ (L : Int) := by simp
  have h1 : |(1 : Int)| ≤ (L : Int) := by simpa only [abs_one] using
    (show (1 : Int) ≤ (L : Int) by exact_mod_cast hL)
  have hR : |(L : Int)| ≤ (L : Int) := by simp
  have hcorner : Path L (facet L (0, (L : Int))) (facet L (1, 1)) := by
    apply path_of_source_eq_target (facet_mem L 0 L hR) (facet_mem L 1 1 h1)
    simp [facet, source, target, sectionRadius_one, sectionRadius_extreme L hL]
  exact (north_path L 0 L h0 hR).trans (hcorner.trans (east_path L 1 0 h1 h0))

theorem facet_path_to_north_zero (L : Nat) (hL : 1 ≤ L) (d : Direction) (a : Int)
    (ha : |a| ≤ (L : Int)) : Path L (facet L (d, a)) (facet L (0, 0)) := by
  have h0 : |(0 : Int)| ≤ (L : Int) := by simp
  have hNE := north_zero_to_east_zero L hL
  have hWN : Path L (facet L (3, 0)) (facet L (0, 0)) := by
    simpa only [turn_facet_north, turn_facet_east, neg_zero] using path_turn hNE
  have hSW : Path L (facet L (2, 0)) (facet L (3, 0)) := by
    simpa only [turn_facet_west, turn_facet_north, neg_zero] using path_turn hWN
  fin_cases d
  · exact north_path L a 0 ha h0
  · exact (east_path L a 0 ha h0).trans (path_reverse hNE)
  · exact (south_path L a 0 ha h0).trans (hSW.trans hWN)
  · exact (west_path L a 0 ha h0).trans hWN

theorem path_to_north_zero (L : Nat) (hL : 1 ≤ L) (e : HalfEdge)
    (he : e ∈ boundary (clippedDomain L)) : Path L e (facet L (0, 0)) := by
  have hp := facetIndex_mem_of_boundary L e he
  have ha := (mem_facetIndices L (facetIndex e)).mp hp
  have h : Path L (facet L (facetIndex e)) (facet L (0, 0)) :=
    facet_path_to_north_zero L hL (facetIndex e).1 (facetIndex e).2 ha
  rw [facet_facetIndex_of_boundary L e he] at h
  exact h

theorem boundary_path_between (L : Nat) (hL : 1 ≤ L) (e f : HalfEdge)
    (he : e ∈ boundary (clippedDomain L)) (hf : f ∈ boundary (clippedDomain L)) :
    Path L e f :=
  (path_to_north_zero L hL e he).trans (path_reverse (path_to_north_zero L hL f hf))

end MathResearchAnalysis.ClippedBoundaryConnectivity
