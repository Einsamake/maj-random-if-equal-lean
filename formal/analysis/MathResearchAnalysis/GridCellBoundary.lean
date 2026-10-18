module

public import MathResearchAnalysis.GridMajorityPeeling

set_option autoImplicit false

/-!
# Actual exposed cell half-edges on the square lattice

Coordinates are multiplied by two. Directions 0,1,2,3 mean north,east,south,
west. A boundary half-edge is present exactly when its owner is occupied and
its actual directional neighbour is empty. Every edge is oriented with the
occupied cell on the left. No simple-contour or corner-count property is
stored as an assumption.
-/

@[expose] public section

namespace MathResearchAnalysis.GridCellBoundary

open InfiniteGridModel

abbrev Site := InfiniteGridModel.Site
abbrev Direction := Fin 4
abbrev HalfEdge := Site × Direction

def neighbor (v : Site) (d : Direction) : Site :=
  match d.val with
  | 0 => north v
  | 1 => east v
  | 2 => south v
  | _ => west v

def source (e : HalfEdge) : Site :=
  match e.2.val with
  | 0 => (2 * e.1.1 + 1, 2 * e.1.2 + 1)
  | 1 => (2 * e.1.1 + 1, 2 * e.1.2 - 1)
  | 2 => (2 * e.1.1 - 1, 2 * e.1.2 - 1)
  | _ => (2 * e.1.1 - 1, 2 * e.1.2 + 1)

def target (e : HalfEdge) : Site :=
  match e.2.val with
  | 0 => (2 * e.1.1 - 1, 2 * e.1.2 + 1)
  | 1 => (2 * e.1.1 + 1, 2 * e.1.2 + 1)
  | 2 => (2 * e.1.1 + 1, 2 * e.1.2 - 1)
  | _ => (2 * e.1.1 - 1, 2 * e.1.2 - 1)

def boundary (S : Finset Site) : Finset HalfEdge :=
  (S ×ˢ (Finset.univ : Finset Direction)).filter
    (fun e => neighbor e.1 e.2 ∉ S)

def cellCorners (v : Site) : Finset Site :=
  {(2 * v.1 + 1, 2 * v.2 + 1), (2 * v.1 - 1, 2 * v.2 + 1),
    (2 * v.1 - 1, 2 * v.2 - 1), (2 * v.1 + 1, 2 * v.2 - 1)}

def directedSegment (e : HalfEdge) : Site × Site := (source e, target e)

def opposite (d : Direction) : Direction := ⟨(d.val + 2) % 4, Nat.mod_lt _ (by decide)⟩

def perimeter (S : Finset Site) : Nat := (boundary S).card

@[simp] theorem neighbor_north (v : Site) : neighbor v 0 = north v := rfl
@[simp] theorem neighbor_east (v : Site) : neighbor v 1 = east v := rfl
@[simp] theorem neighbor_south (v : Site) : neighbor v 2 = south v := rfl
@[simp] theorem neighbor_west (v : Site) : neighbor v 3 = west v := rfl

@[simp] theorem source_north (v : Site) : source (v, 0) = (2*v.1+1, 2*v.2+1) := rfl
@[simp] theorem source_east (v : Site) : source (v, 1) = (2*v.1+1, 2*v.2-1) := rfl
@[simp] theorem source_south (v : Site) : source (v, 2) = (2*v.1-1, 2*v.2-1) := rfl
@[simp] theorem source_west (v : Site) : source (v, 3) = (2*v.1-1, 2*v.2+1) := rfl

@[simp] theorem target_north (v : Site) : target (v, 0) = (2*v.1-1, 2*v.2+1) := rfl
@[simp] theorem target_east (v : Site) : target (v, 1) = (2*v.1+1, 2*v.2+1) := rfl
@[simp] theorem target_south (v : Site) : target (v, 2) = (2*v.1+1, 2*v.2-1) := rfl
@[simp] theorem target_west (v : Site) : target (v, 3) = (2*v.1-1, 2*v.2-1) := rfl

theorem mem_boundary (S : Finset Site) (e : HalfEdge) :
    e ∈ boundary S ↔ e.1 ∈ S ∧ neighbor e.1 e.2 ∉ S := by
  simp [boundary]

theorem neighbor_mem_neighbors4 (v : Site) (d : Direction) :
    neighbor v d ∈ GridMajorityPeeling.neighbors4 v := by
  fin_cases d <;> simp [neighbor, GridMajorityPeeling.mem_neighbors4]

theorem mem_boundary_north (S : Finset Site) (v : Site) :
    (v, 0) ∈ boundary S ↔ v ∈ S ∧ north v ∉ S := by rw [mem_boundary, neighbor_north]

theorem mem_boundary_east (S : Finset Site) (v : Site) :
    (v, 1) ∈ boundary S ↔ v ∈ S ∧ east v ∉ S := by rw [mem_boundary, neighbor_east]

theorem mem_boundary_south (S : Finset Site) (v : Site) :
    (v, 2) ∈ boundary S ↔ v ∈ S ∧ south v ∉ S := by rw [mem_boundary, neighbor_south]

theorem mem_boundary_west (S : Finset Site) (v : Site) :
    (v, 3) ∈ boundary S ↔ v ∈ S ∧ west v ∉ S := by rw [mem_boundary, neighbor_west]

theorem boundary_owner_mem {S : Finset Site} {e : HalfEdge} (h : e ∈ boundary S) : e.1 ∈ S :=
  ((mem_boundary S e).mp h).1

theorem boundary_neighbor_not_mem {S : Finset Site} {e : HalfEdge} (h : e ∈ boundary S) :
    neighbor e.1 e.2 ∉ S := ((mem_boundary S e).mp h).2

theorem source_mem_cellCorners (e : HalfEdge) : source e ∈ cellCorners e.1 := by
  rcases e with ⟨v, d⟩
  fin_cases d <;> simp [source, cellCorners]

theorem target_mem_cellCorners (e : HalfEdge) : target e ∈ cellCorners e.1 := by
  rcases e with ⟨v, d⟩
  fin_cases d <;> simp [target, cellCorners]

theorem source_support {S : Finset Site} {e : HalfEdge} (h : e ∈ boundary S) :
    source e ∈ S.biUnion cellCorners :=
  Finset.mem_biUnion.mpr ⟨e.1, boundary_owner_mem h, source_mem_cellCorners e⟩

theorem target_support {S : Finset Site} {e : HalfEdge} (h : e ∈ boundary S) :
    target e ∈ S.biUnion cellCorners :=
  Finset.mem_biUnion.mpr ⟨e.1, boundary_owner_mem h, target_mem_cellCorners e⟩

theorem source_odd_coordinates (e : HalfEdge) :
    (source e).1 % 2 = 1 ∧ (source e).2 % 2 = 1 := by
  rcases e with ⟨v, d⟩
  fin_cases d <;> dsimp [source] <;> constructor <;> omega

theorem target_odd_coordinates (e : HalfEdge) :
    (target e).1 % 2 = 1 ∧ (target e).2 % 2 = 1 := by
  rcases e with ⟨v, d⟩
  fin_cases d <;> dsimp [target] <;> constructor <;> omega

theorem source_ne_target (e : HalfEdge) : source e ≠ target e := by
  rcases e with ⟨v, d⟩
  intro h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases d <;> dsimp [source, target] at hx hy <;> omega

theorem edge_displacement (e : HalfEdge) :
    ((target e).1 - (source e).1, (target e).2 - (source e).2) =
      match e.2.val with
      | 0 => (-2, 0)
      | 1 => (0, 2)
      | 2 => (2, 0)
      | _ => (0, -2) := by
  rcases e with ⟨v, d⟩
  fin_cases d <;> apply Prod.ext <;> norm_num [source, target] <;> omega

theorem scaled_edge_length (e : HalfEdge) :
    |(target e).1 - (source e).1| + |(target e).2 - (source e).2| = 2 := by
  rcases e with ⟨v, d⟩
  fin_cases d <;> dsimp [source, target]
  all_goals have hx : 2 * v.1 + 1 - (2 * v.1 - 1) = 2 := by omega
  all_goals have hy : 2 * v.2 + 1 - (2 * v.2 - 1) = 2 := by omega
  all_goals have hnx : 2 * v.1 - 1 - (2 * v.1 + 1) = -2 := by omega
  all_goals have hny : 2 * v.2 - 1 - (2 * v.2 + 1) = -2 := by omega
  all_goals simp_all

/-- Positive signed cross product: the actual occupied cell center is on the left. -/
theorem occupied_center_left (e : HalfEdge) :
    ((target e).1 - (source e).1) * (2 * e.1.2 - (source e).2) -
      ((target e).2 - (source e).2) * (2 * e.1.1 - (source e).1) = 2 := by
  rcases e with ⟨v, d⟩
  fin_cases d <;> dsimp [source, target] <;> ring

theorem source_injective_same_direction (d : Direction) :
    Function.Injective (fun v : Site => source (v, d)) := by
  intro v w h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext
  all_goals fin_cases d <;> dsimp [source] at hx hy <;> omega

theorem target_injective_same_direction (d : Direction) :
    Function.Injective (fun v : Site => target (v, d)) := by
  intro v w h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext
  all_goals fin_cases d <;> dsimp [target] at hx hy <;> omega

theorem direction_eq_of_endpoints_eq {e f : HalfEdge}
    (hs : source e = source f) (ht : target e = target f) : e.2 = f.2 := by
  rcases e with ⟨v, d⟩
  rcases f with ⟨w, c⟩
  have hsx := congrArg Prod.fst hs
  have hsy := congrArg Prod.snd hs
  have htx := congrArg Prod.fst ht
  have hty := congrArg Prod.snd ht
  fin_cases d <;> fin_cases c <;> dsimp [source, target] at hsx hsy htx hty
  all_goals first | rfl | omega

theorem directedSegment_injective : Function.Injective directedSegment := by
  rintro ⟨v, d⟩ ⟨w, c⟩ h
  have hs : source (v, d) = source (w, c) := congrArg Prod.fst h
  have ht : target (v, d) = target (w, c) := congrArg Prod.snd h
  have hd : d = c := direction_eq_of_endpoints_eq hs ht
  subst c
  exact Prod.ext (source_injective_same_direction d hs) rfl

theorem boundary_segments_card (S : Finset Site) :
    ((boundary S).image directedSegment).card = (boundary S).card :=
  Finset.card_image_of_injective _ directedSegment_injective

theorem opposite_involutive : Function.Involutive opposite := by
  intro d
  fin_cases d <;> rfl

theorem neighbor_opposite (v : Site) (d : Direction) :
    neighbor (neighbor v d) (opposite d) = v := by
  fin_cases d <;> apply Prod.ext <;> norm_num [neighbor, opposite, north, east, south, west]

theorem source_opposite (v : Site) (d : Direction) :
    source (neighbor v d, opposite d) = target (v, d) := by
  fin_cases d <;> apply Prod.ext <;> norm_num [source, target, neighbor, opposite, north, east, south, west] <;> omega

theorem target_opposite (v : Site) (d : Direction) :
    target (neighbor v d, opposite d) = source (v, d) := by
  fin_cases d <;> apply Prod.ext <;> norm_num [source, target, neighbor, opposite, north, east, south, west] <;> omega

theorem opposite_not_boundary {S : Finset Site} {e : HalfEdge} (h : e ∈ boundary S) :
    (neighbor e.1 e.2, opposite e.2) ∉ boundary S := by
  intro hreverse
  exact boundary_neighbor_not_mem h (boundary_owner_mem hreverse)

@[simp] theorem boundary_empty : boundary ∅ = ∅ := by simp [boundary]

@[simp] theorem perimeter_empty : perimeter ∅ = 0 := by simp [perimeter]

end MathResearchAnalysis.GridCellBoundary


