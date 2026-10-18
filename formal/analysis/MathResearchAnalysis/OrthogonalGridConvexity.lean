module

public import MathResearchAnalysis.GridBoundaryIncidence
public import MathResearchAnalysis.ClippedGridConnectivity

set_option autoImplicit false

/-!
# Orthogonal interval convexity and actual four-neighbour paths

RowConvex and ColumnConvex are coordinate-between properties of the occupied
sites. FourConnected means that every ordered pair of occupied sites admits a
finite path of actual occupied four-neighbour steps; this universal convention
also holds for the empty set. Row convexity together with those real paths
excludes each alternating 2x2 occupancy pattern by an actual horizontal cut.
These statements do not define or characterize the original Good class.
-/

@[expose] public section

namespace MathResearchAnalysis.OrthogonalGridConvexity

open GridCellBoundary (Site)
open InfiniteGridModel (north east south west)
open GridMajorityPeeling (neighbors4 mem_neighbors4)
open ClippedDiamondGeometry (clippedDomain)

def InternalStep (S : Finset Site) (u v : Site) : Prop :=
  u ∈ S ∧ v ∈ S ∧ v ∈ neighbors4 u

abbrev Path (S : Finset Site) : Site → Site → Prop :=
  Relation.ReflTransGen (InternalStep S)

def FourConnected (S : Finset Site) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, Path S u v

def RowConvex (S : Finset Site) : Prop :=
  ∀ a b x y : Int, (a, y) ∈ S → (b, y) ∈ S →
    a ≤ x → x ≤ b → (x, y) ∈ S

def ColumnConvex (S : Finset Site) : Prop :=
  ∀ x a b y : Int, (x, a) ∈ S → (x, b) ∈ S →
    a ≤ y → y ≤ b → (x, y) ∈ S

theorem step_crosses_horizontal_cut {S : Finset Site} {u v : Site} (y : Int)
    (hstep : InternalStep S u v) (hu : u.2 ≤ y) (hv : y < v.2) :
    ∃ x : Int, (x, y) ∈ S ∧ (x, y + 1) ∈ S := by
  rcases u with ⟨ux, uy⟩
  rcases v with ⟨vx, vy⟩
  change uy ≤ y at hu
  change y < vy at hv
  have hgrid := (mem_neighbors4 (ux, uy) (vx, vy)).mp hstep.2.2
  rcases hgrid with hn | he | hs | hw
  · have hx := congrArg Prod.fst hn
    have hy := congrArg Prod.snd hn
    dsimp [north] at hx hy
    have hy0 : uy = y := by omega
    refine ⟨ux, ?_, ?_⟩
    · simpa only [hy0] using hstep.1
    · have hxy : (vx, vy) = (ux, y + 1) := Prod.ext hx (by omega)
      simpa only [hxy] using hstep.2.1
  · have hy := congrArg Prod.snd he
    dsimp [east] at hy
    omega
  · have hy := congrArg Prod.snd hs
    dsimp [south] at hy
    omega
  · have hy := congrArg Prod.snd hw
    dsimp [west] at hy
    omega

theorem path_preserves_horizontal_cut {S : Finset Site} {u v : Site} (y : Int)
    (hcut : ∀ x : Int, (x, y) ∈ S → (x, y + 1) ∉ S)
    (hu : u.2 ≤ y) (hpath : Path S u v) : v.2 ≤ y := by
  induction hpath with
  | refl => exact hu
  | tail _ hs ih =>
      by_contra hv
      obtain ⟨x, hx, hx1⟩ := step_crosses_horizontal_cut y hs ih (lt_of_not_ge hv)
      exact hcut x hx hx1

theorem path_crosses_horizontal_cut {S : Finset Site} {u v : Site} (y : Int)
    (hpath : Path S u v) (hu : u.2 ≤ y) (hv : y < v.2) :
    ∃ x : Int, (x, y) ∈ S ∧ (x, y + 1) ∈ S := by
  by_contra hnone
  have hcut : ∀ x : Int, (x, y) ∈ S → (x, y + 1) ∉ S := by
    intro x hx hx1
    exact hnone ⟨x, hx, hx1⟩
  exact (not_le_of_gt hv) (path_preserves_horizontal_cut y hcut hu hpath)

theorem first_checkerboard_impossible (S : Finset Site) (hrow : RowConvex S)
    (hconn : FourConnected S) (a : Site)
    (hsw : a ∈ S) (hne : north (east a) ∈ S)
    (hse : east a ∉ S) (hnw : north a ∉ S) : False := by
  rcases a with ⟨ax, ay⟩
  change (ax, ay) ∈ S at hsw
  change (ax + 1, ay + 1) ∈ S at hne
  change (ax + 1, ay) ∉ S at hse
  change (ax, ay + 1) ∉ S at hnw
  have hcut : ∀ x : Int, (x, ay) ∈ S → (x, ay + 1) ∉ S := by
    intro x hx0 hx1
    have hleft : x ≤ ax := by
      by_contra h
      apply hse
      exact hrow ax x (ax + 1) ay hsw hx0 (by omega) (by omega)
    have hright : ax + 1 ≤ x := by
      by_contra h
      apply hnw
      exact hrow x (ax + 1) ax (ay + 1) hx1 hne (by omega) (by omega)
    omega
  have hp := hconn (ax, ay) hsw (ax + 1, ay + 1) hne
  obtain ⟨x, hx, hx1⟩ := path_crosses_horizontal_cut ay hp (by rfl) (by dsimp; omega)
  exact hcut x hx hx1

theorem second_checkerboard_impossible (S : Finset Site) (hrow : RowConvex S)
    (hconn : FourConnected S) (a : Site)
    (hsw : a ∉ S) (hne : north (east a) ∉ S)
    (hse : east a ∈ S) (hnw : north a ∈ S) : False := by
  rcases a with ⟨ax, ay⟩
  change (ax, ay) ∉ S at hsw
  change (ax + 1, ay + 1) ∉ S at hne
  change (ax + 1, ay) ∈ S at hse
  change (ax, ay + 1) ∈ S at hnw
  have hcut : ∀ x : Int, (x, ay) ∈ S → (x, ay + 1) ∉ S := by
    intro x hx0 hx1
    have hright : ax + 1 ≤ x := by
      by_contra h
      apply hsw
      exact hrow x (ax + 1) ax ay hx0 hse (by omega) (by omega)
    have hleft : x ≤ ax := by
      by_contra h
      apply hne
      exact hrow ax x (ax + 1) (ay + 1) hnw hx1 (by omega) (by omega)
    omega
  have hp := hconn (ax + 1, ay) hse (ax, ay + 1) hnw
  obtain ⟨x, hx, hx1⟩ := path_crosses_horizontal_cut ay hp (by rfl) (by dsimp; omega)
  exact hcut x hx hx1

theorem rowConvex_fourConnected_noCheckerboard (S : Finset Site)
    (hrow : RowConvex S) (hconn : FourConnected S) :
    GridBoundaryIncidence.NoCheckerboard S := by
  intro a
  constructor
  · rintro ⟨hsw, hne, hse, hnw⟩
    exact first_checkerboard_impossible S hrow hconn a hsw hne hse hnw
  · rintro ⟨hsw, hne, hse, hnw⟩
    exact second_checkerboard_impossible S hrow hconn a hsw hne hse hnw

theorem clipped_rowConvex (L : Nat) : RowConvex (clippedDomain L) := by
  intro a b x y ha hb hax hxb
  exact ClippedOrthogonalSections.row_interval_convex L a b x y ha hb hax hxb

theorem clipped_columnConvex (L : Nat) : ColumnConvex (clippedDomain L) := by
  intro x a b y ha hb hay hyb
  exact ClippedOrthogonalSections.column_interval_convex L x a b y ha hb hay hyb

theorem clipped_fourConnected (L : Nat) : FourConnected (clippedDomain L) := by
  intro u hu v hv
  exact ClippedGridConnectivity.path_between L u v hu hv

theorem clipped_noCheckerboard (L : Nat) :
    GridBoundaryIncidence.NoCheckerboard (clippedDomain L) :=
  rowConvex_fourConnected_noCheckerboard _ (clipped_rowConvex L) (clipped_fourConnected L)

end MathResearchAnalysis.OrthogonalGridConvexity
