module

public import MathResearchAnalysis.GridCellBoundary

set_option autoImplicit false

/-!
# Local incidence of the actual exposed cell boundary

An odd corner is the northeast corner of its southwest cell a. The only
possible incoming and outgoing edges are read from its actual four surrounding
cells. The checkerboard condition excludes exactly the two alternating
occupancy patterns; no contour property is stored as a structure field.
The resulting one-in/one-out statement is local and does not assert one cycle.
-/

@[expose] public section

namespace MathResearchAnalysis.GridBoundaryIncidence

open InfiniteGridModel (north east south west)
open GridCellBoundary

def corner (a : Site) : Site := (2 * a.1 + 1, 2 * a.2 + 1)

def outgoingCandidates (a : Site) : Finset HalfEdge :=
  {(a, 0), (north a, 1), (north (east a), 2), (east a, 3)}

def incomingCandidates (a : Site) : Finset HalfEdge :=
  {(a, 1), (east a, 0), (north (east a), 3), (north a, 2)}

def outgoing (S : Finset Site) (p : Site) : Finset HalfEdge :=
  (boundary S).filter (fun e => source e = p)

def incoming (S : Finset Site) (p : Site) : Finset HalfEdge :=
  (boundary S).filter (fun e => target e = p)

def vertices (S : Finset Site) : Finset Site :=
  (boundary S).image source ∪ (boundary S).image target

/-- Excludes precisely the two diagonal occupied/empty patterns of the real 2x2 cells. -/
def NoCheckerboardAt (S : Finset Site) (a : Site) : Prop :=
  ¬ (a ∈ S ∧ north (east a) ∈ S ∧ east a ∉ S ∧ north a ∉ S) ∧
    ¬ (a ∉ S ∧ north (east a) ∉ S ∧ east a ∈ S ∧ north a ∈ S)

def NoCheckerboard (S : Finset Site) : Prop := ∀ a, NoCheckerboardAt S a

theorem corner_odd_coordinates (a : Site) :
    (corner a).1 % 2 = 1 ∧ (corner a).2 % 2 = 1 := by
  constructor <;> dsimp [corner] <;> omega

theorem exists_corner_of_odd_coordinates (p : Site)
    (hp : p.1 % 2 = 1 ∧ p.2 % 2 = 1) : ∃ a, corner a = p := by
  refine ⟨(p.1 / 2, p.2 / 2), ?_⟩
  apply Prod.ext <;> dsimp [corner] <;> omega

theorem source_eq_corner_iff (e : HalfEdge) (a : Site) :
    source e = corner a ↔ e ∈ outgoingCandidates a := by
  rcases e with ⟨v, d⟩
  fin_cases d <;>
    simp only [source, corner, outgoingCandidates, Finset.mem_insert, Finset.mem_singleton,
      Prod.ext_iff, Fin.ext_iff, north, east]
  all_goals norm_num
  all_goals omega

theorem target_eq_corner_iff (e : HalfEdge) (a : Site) :
    target e = corner a ↔ e ∈ incomingCandidates a := by
  rcases e with ⟨v, d⟩
  fin_cases d <;>
    simp only [target, corner, incomingCandidates, Finset.mem_insert, Finset.mem_singleton,
      Prod.ext_iff, Fin.ext_iff, north, east]
  all_goals norm_num
  all_goals omega

theorem mem_outgoing (S : Finset Site) (p : Site) (e : HalfEdge) :
    e ∈ outgoing S p ↔ e ∈ boundary S ∧ source e = p := Finset.mem_filter

theorem mem_incoming (S : Finset Site) (p : Site) (e : HalfEdge) :
    e ∈ incoming S p ↔ e ∈ boundary S ∧ target e = p := Finset.mem_filter

theorem outgoing_eq_filter_candidates (S : Finset Site) (a : Site) :
    outgoing S (corner a) = (outgoingCandidates a).filter (fun e => e ∈ boundary S) := by
  ext e
  simp only [mem_outgoing, Finset.mem_filter, ← source_eq_corner_iff]
  tauto

theorem incoming_eq_filter_candidates (S : Finset Site) (a : Site) :
    incoming S (corner a) = (incomingCandidates a).filter (fun e => e ∈ boundary S) := by
  ext e
  simp only [mem_incoming, Finset.mem_filter, ← target_eq_corner_iff]
  tauto

/-- Complete sixteen-pattern classification, proved from actual membership and endpoints. -/
theorem incidence_counts (S : Finset Site) (a : Site) :
    (outgoing S (corner a)).card = (incoming S (corner a)).card ∧
      (outgoing S (corner a)).card ≤ 2 ∧
      ((outgoing S (corner a)).card = 2 ↔ ¬ NoCheckerboardAt S a) := by
  by_cases hsw : a ∈ S <;> by_cases hse : east a ∈ S <;>
    by_cases hnw : north a ∈ S <;> by_cases hne : north (east a) ∈ S
  all_goals simp_all [outgoing_eq_filter_candidates, incoming_eq_filter_candidates,
    outgoingCandidates, incomingCandidates, GridCellBoundary.mem_boundary,
    GridCellBoundary.neighbor, NoCheckerboardAt, north, east, south, west,
    Finset.filter_insert, Finset.filter_singleton]

theorem card_outgoing_eq_card_incoming (S : Finset Site) (a : Site) :
    (outgoing S (corner a)).card = (incoming S (corner a)).card :=
  (incidence_counts S a).1

theorem card_outgoing_le_two (S : Finset Site) (a : Site) :
    (outgoing S (corner a)).card ≤ 2 := (incidence_counts S a).2.1

theorem card_outgoing_eq_two_iff (S : Finset Site) (a : Site) :
    (outgoing S (corner a)).card = 2 ↔ ¬ NoCheckerboardAt S a :=
  (incidence_counts S a).2.2

theorem local_incidence_one (S : Finset Site) (a : Site) (hnc : NoCheckerboardAt S a)
    (hi : (outgoing S (corner a)).Nonempty ∨ (incoming S (corner a)).Nonempty) :
    (outgoing S (corner a)).card = 1 ∧ (incoming S (corner a)).card = 1 := by
  have hclass := incidence_counts S a
  have hnot : (outgoing S (corner a)).card ≠ 2 := fun h => (hclass.2.2.mp h) hnc
  have hpos : 0 < (outgoing S (corner a)).card := by
    rcases hi with ho | hi
    · exact Finset.card_pos.mpr ho
    · rw [hclass.1]
      exact Finset.card_pos.mpr hi
  constructor <;> omega

theorem mem_vertices (S : Finset Site) (p : Site) :
    p ∈ vertices S ↔ (outgoing S p).Nonempty ∨ (incoming S p).Nonempty := by
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hs | ht
    · obtain ⟨e, he, hep⟩ := Finset.mem_image.mp hs
      exact Or.inl ⟨e, (mem_outgoing S p e).mpr ⟨he, hep⟩⟩
    · obtain ⟨e, he, hep⟩ := Finset.mem_image.mp ht
      exact Or.inr ⟨e, (mem_incoming S p e).mpr ⟨he, hep⟩⟩
  · intro hp
    rcases hp with ⟨e, he⟩ | ⟨e, he⟩
    · obtain ⟨he, hep⟩ := (mem_outgoing S p e).mp he
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, hep⟩)
    · obtain ⟨he, hep⟩ := (mem_incoming S p e).mp he
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, hep⟩)

theorem vertex_odd_coordinates {S : Finset Site} {p : Site} (hp : p ∈ vertices S) :
    p.1 % 2 = 1 ∧ p.2 % 2 = 1 := by
  rcases Finset.mem_union.mp hp with hs | ht
  · obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hs
    exact source_odd_coordinates e
  · obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp ht
    exact target_odd_coordinates e

/-- Each actual boundary vertex has one incoming and one outgoing edge locally.
This is not a connectedness or single-cycle assertion. -/
theorem vertex_incidence_one (S : Finset Site) (hnc : NoCheckerboard S)
    (p : Site) (hp : p ∈ vertices S) :
    (outgoing S p).card = 1 ∧ (incoming S p).card = 1 := by
  obtain ⟨a, rfl⟩ := exists_corner_of_odd_coordinates p (vertex_odd_coordinates hp)
  exact local_incidence_one S a (hnc a) ((mem_vertices S (corner a)).mp hp)

end MathResearchAnalysis.GridBoundaryIncidence


