module

public import MathResearchAnalysis.ConvexLocalUpdate

set_option autoImplicit false

/-!
# Orthogonal interval convexity under legal cleanup

Erasing a site preserves row convexity when its two horizontal neighbours are
not both occupied; the vertical statement is analogous. Every legal strict-
majority cleanup deletion has degree below two, hence satisfies both tests.
This proves that the actual cleanup preserves row and column convexity, but
asserts neither connectedness nor a geometric Good invariant.
-/

@[expose] public section
namespace MathResearchAnalysis.ConvexCleanupUpdate

open GridCellBoundary (Site)
open InfiniteGridModel (north east south west)
open GridMajorityPeeling
open OrthogonalGridConvexity

theorem rowConvex_erase_of_no_opposites {S : Finset Site} {v : Site}
    (hr : RowConvex S) (hno : ¬ (east v ∈ S ∧ west v ∈ S)) : RowConvex (S.erase v) := by
  rcases v with ⟨vx,vy⟩
  intro a b x y ha hb hax hxb
  obtain ⟨hane,ha⟩ := Finset.mem_erase.mp ha
  obtain ⟨hbne,hb⟩ := Finset.mem_erase.mp hb
  refine Finset.mem_erase.mpr ⟨?_,hr a b x y ha hb hax hxb⟩
  intro heq
  have hx : x = vx := congrArg Prod.fst heq
  have hy : y = vy := congrArg Prod.snd heq
  subst x
  subst y
  have hna : a ≠ vx := fun h => hane (Prod.ext h rfl)
  have hnb : b ≠ vx := fun h => hbne (Prod.ext h rfl)
  exact hno ⟨hr a b (vx+1) vy ha hb (by omega) (by omega),
    hr a b (vx-1) vy ha hb (by omega) (by omega)⟩

theorem columnConvex_erase_of_no_opposites {S : Finset Site} {v : Site}
    (hc : ColumnConvex S) (hno : ¬ (north v ∈ S ∧ south v ∈ S)) : ColumnConvex (S.erase v) := by
  rcases v with ⟨vx,vy⟩
  intro x a b y ha hb hay hyb
  obtain ⟨hane,ha⟩ := Finset.mem_erase.mp ha
  obtain ⟨hbne,hb⟩ := Finset.mem_erase.mp hb
  refine Finset.mem_erase.mpr ⟨?_,hc x a b y ha hb hay hyb⟩
  intro heq
  have hx : x = vx := congrArg Prod.fst heq
  have hy : y = vy := congrArg Prod.snd heq
  subst x
  subst y
  have hna : a ≠ vy := fun h => hane (Prod.ext rfl h)
  have hnb : b ≠ vy := fun h => hbne (Prod.ext rfl h)
  exact hno ⟨hc vx a b (vy+1) ha hb (by omega) (by omega),
    hc vx a b (vy-1) ha hb (by omega) (by omega)⟩

theorem low_degree_no_opposites {S : Finset Site} {v : Site} (hd : degree4 S v < 2) :
    ¬ (east v ∈ S ∧ west v ∈ S) ∧ ¬ (north v ∈ S ∧ south v ∈ S) := by
  rw [degree4_eq_four_inputs] at hd
  constructor
  · rintro ⟨he,hw⟩
    have he' : state S (east v) = true := by simp [state,he]
    have hw' : state S (west v) = true := by simp [state,hw]
    rw [he',hw'] at hd
    simp only [Bool.toNat_true] at hd
    omega
  · rintro ⟨hn,hs⟩
    have hn' : state S (north v) = true := by simp [state,hn]
    have hs' : state S (south v) = true := by simp [state,hs]
    rw [hn',hs'] at hd
    simp only [Bool.toNat_true] at hd
    omega

theorem legal_delete_preserves_convexity {S T : Finset Site}
    (hr : RowConvex S) (hc : ColumnConvex S)
    (hdel : FiniteMajorityPeeling.Delete neighbors4 S T) : RowConvex T ∧ ColumnConvex T := by
  obtain ⟨v,_,hd,rfl⟩ := hdel
  have hno := low_degree_no_opposites (S := S) (v := v) hd
  exact ⟨rowConvex_erase_of_no_opposites hr hno.1,
    columnConvex_erase_of_no_opposites hc hno.2⟩

theorem legal_deletes_preserve_convexity {S T : Finset Site}
    (hr : RowConvex S) (hc : ColumnConvex S)
    (hdel : FiniteMajorityPeeling.Deletes neighbors4 S T) : RowConvex T ∧ ColumnConvex T := by
  induction hdel with
  | refl => exact ⟨hr,hc⟩
  | tail _ hs ih => exact legal_delete_preserves_convexity ih.1 ih.2 hs

theorem cleanup_preserves_convexity {S : Finset Site} (hr : RowConvex S) (hc : ColumnConvex S) :
    RowConvex (cleanup S) ∧ ColumnConvex (cleanup S) :=
  legal_deletes_preserve_convexity hr hc (cleanup_reachable S)

theorem cleanup_erase_convex_of_no_opposites {S : Finset Site} {v : Site}
    (hr : RowConvex S) (hc : ColumnConvex S)
    (hh : ¬ (east v ∈ S ∧ west v ∈ S)) (hv : ¬ (north v ∈ S ∧ south v ∈ S)) :
    RowConvex (cleanup (S.erase v)) ∧ ColumnConvex (cleanup (S.erase v)) :=
  cleanup_preserves_convexity (rowConvex_erase_of_no_opposites hr hh)
    (columnConvex_erase_of_no_opposites hc hv)

theorem actual_death_cleanup_convex {D S : Finset Site} {v : Site}
    (hr : RowConvex S) (hc : ColumnConvex S) (hst : DropletModifiedWord.Stable S)
    (hvD : v ∈ D) (hvS : v ∈ S) (hd : degree4 S v = 2)
    (hh : ¬ (east v ∈ S ∧ west v ∈ S)) (hv : ¬ (north v ∈ S ∧ south v ∈ S)) :
    RowConvex (DropletModifiedWord.modifiedStep D S v false) ∧
      ColumnConvex (DropletModifiedWord.modifiedStep D S v false) := by
  rw [DropletModifiedWord.modifiedStep, ite_eq_left hvD,
    ConvexLocalUpdate.rawStep_of_death hst hvS hd]
  exact cleanup_erase_convex_of_no_opposites hr hc hh hv

end MathResearchAnalysis.ConvexCleanupUpdate
