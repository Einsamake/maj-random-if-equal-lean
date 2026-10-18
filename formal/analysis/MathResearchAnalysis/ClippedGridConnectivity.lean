module

public import MathResearchAnalysis.ClippedOrthogonalSections
public import Mathlib.Logic.Relation

set_option autoImplicit false

/-!
# Finite four-neighbour paths inside the actual clipped domain

An InternalStep has both endpoints in clippedDomain and follows one of the
actual four nearest-neighbour grid edges. Path is its finite reflexive
transitive closure. Its zero-edge case is reflexive at every lattice site;
the geometric theorems below explicitly assume their endpoints lie in the
domain, including L = 0. No contour simplicity or dynamic preservation is
asserted.
-/

@[expose] public section

namespace MathResearchAnalysis.ClippedGridConnectivity

open ClippedDiamondGeometry ClippedOrthogonalSections
open GridMajorityPeeling
open InfiniteGridModel (north east south west)

def InternalStep (L : Nat) (u v : Site) : Prop :=
  u ∈ clippedDomain L ∧ v ∈ clippedDomain L ∧ v ∈ neighbors4 u

abbrev Path (L : Nat) : Site → Site → Prop :=
  Relation.ReflTransGen (InternalStep L)

theorem toward_abs_lt (a : Int) (ha : a ≠ 0) : |toward a| < |a| := by
  by_cases hp : 0 < a
  · have ha0 : 0 ≤ a := by omega
    have ht0 : 0 ≤ a - 1 := by omega
    simp only [toward, ite_eq_left hp, abs_of_nonneg ht0, abs_of_nonneg ha0]
    omega
  · have ha0 : a ≤ 0 := by omega
    have ht0 : a + 1 ≤ 0 := by omega
    simp only [toward, ite_eq_right hp, abs_of_nonpos ht0, abs_of_nonpos ha0]
    omega

theorem toward_natAbs_lt (a : Int) (ha : a ≠ 0) :
    (toward a).natAbs < a.natAbs := by
  have h : ((toward a).natAbs : Int) < (a.natAbs : Int) := by
    simpa only [Int.natCast_natAbs] using toward_abs_lt a ha
  exact_mod_cast h

theorem internalStep_symm {L : Nat} {u v : Site} (h : InternalStep L u v) :
    InternalStep L v u := by
  refine ⟨h.2.1, h.1, ?_⟩
  have hgrid := (mem_neighbors4 u v).mp h.2.2
  rw [mem_neighbors4]
  rcases hgrid with hn | he | hs | hw
  · right; right; left
    rw [hn]
    simp [north, south]
  · right; right; right
    rw [he]
    simp [east, west]
  · left
    rw [hs]
    simp [south, north]
  · right; left
    rw [hw]
    simp [west, east]

theorem horizontalNeighbor_mem_of_ne_zero {L : Nat} {z : Site}
    (hz : z ∈ clippedDomain L) (hx : z.1 ≠ 0) :
    horizontalNeighbor z ∈ clippedDomain L := by
  exact mem_of_abs_coordinates_le hz (le_of_lt (toward_abs_lt z.1 hx)) le_rfl

theorem verticalNeighbor_mem_of_ne_zero {L : Nat} {z : Site}
    (hz : z ∈ clippedDomain L) (hy : z.2 ≠ 0) :
    verticalNeighbor z ∈ clippedDomain L := by
  exact mem_of_abs_coordinates_le hz le_rfl (le_of_lt (toward_abs_lt z.2 hy))

theorem horizontal_internalStep {L : Nat} {z : Site}
    (hz : z ∈ clippedDomain L) (hx : z.1 ≠ 0) :
    InternalStep L z (horizontalNeighbor z) :=
  ⟨hz, horizontalNeighbor_mem_of_ne_zero hz hx,
    horizontalNeighbor_mem_neighbors4 z⟩

theorem vertical_internalStep {L : Nat} {z : Site}
    (hz : z ∈ clippedDomain L) (hy : z.2 ≠ 0) :
    InternalStep L z (verticalNeighbor z) :=
  ⟨hz, verticalNeighbor_mem_of_ne_zero hz hy,
    verticalNeighbor_mem_neighbors4 z⟩

theorem path_reverse {L : Nat} {u v : Site} (h : Path L u v) : Path L v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact (Relation.ReflTransGen.single (internalStep_symm hstep)).trans ih

theorem path_end_mem {L : Nat} {u v : Site} (hu : u ∈ clippedDomain L)
    (h : Path L u v) : v ∈ clippedDomain L := by
  induction h with
  | refl => exact hu
  | tail _ hstep _ => exact hstep.2.1

theorem path_to_vertical_axis (L : Nat) (z : Site) (hz : z ∈ clippedDomain L) :
    Path L z (0, z.2) := by
  suffices haux : ∀ n : Nat, ∀ w : Site, w.1.natAbs = n →
      w ∈ clippedDomain L → Path L w (0, w.2) from haux z.1.natAbs z rfl hz
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro w hwn hw
      by_cases hx : w.1 = 0
      · have he : w = (0, w.2) := Prod.ext hx rfl
        rw [he]
      · have hlt : (horizontalNeighbor w).1.natAbs < n := by
          simpa only [horizontalNeighbor, hwn] using toward_natAbs_lt w.1 hx
        have hnext := horizontalNeighbor_mem_of_ne_zero hw hx
        have hrec := ih _ hlt (horizontalNeighbor w) rfl hnext
        exact (Relation.ReflTransGen.single (horizontal_internalStep hw hx)).trans
          hrec

theorem path_to_horizontal_axis (L : Nat) (z : Site) (hz : z ∈ clippedDomain L) :
    Path L z (z.1, 0) := by
  suffices haux : ∀ n : Nat, ∀ w : Site, w.2.natAbs = n →
      w ∈ clippedDomain L → Path L w (w.1, 0) from haux z.2.natAbs z rfl hz
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro w hwn hw
      by_cases hy : w.2 = 0
      · have he : w = (w.1, 0) := Prod.ext rfl hy
        rw [he]
      · have hlt : (verticalNeighbor w).2.natAbs < n := by
          simpa only [verticalNeighbor, hwn] using toward_natAbs_lt w.2 hy
        have hnext := verticalNeighbor_mem_of_ne_zero hw hy
        have hrec := ih _ hlt (verticalNeighbor w) rfl hnext
        exact (Relation.ReflTransGen.single (vertical_internalStep hw hy)).trans
          hrec

theorem path_to_origin (L : Nat) (z : Site) (hz : z ∈ clippedDomain L) :
    Path L z (0, 0) := by
  have haxis : (0, z.2) ∈ clippedDomain L :=
    (vertical_axis_mem_iff L z.2).mpr ((mem_clippedDomain L z).mp hz).2.1
  exact (path_to_vertical_axis L z hz).trans
    (path_to_horizontal_axis L (0, z.2) haxis)

theorem path_between (L : Nat) (u v : Site)
    (hu : u ∈ clippedDomain L) (hv : v ∈ clippedDomain L) : Path L u v :=
  (path_to_origin L u hu).trans (path_reverse (path_to_origin L v hv))

theorem path_to_abs_coordinate_shrink {L : Nat} {u v : Site}
    (hu : u ∈ clippedDomain L) (hx : |v.1| ≤ |u.1|) (hy : |v.2| ≤ |u.2|) :
    Path L u v :=
  path_between L u v hu (mem_of_abs_coordinates_le hu hx hy)

end MathResearchAnalysis.ClippedGridConnectivity
