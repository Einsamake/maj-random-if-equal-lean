module

public import MathResearchAnalysis.ConvexBirthUpdate

set_option autoImplicit false

/-!
# Actual majority cleanup preserves occupied four-neighbour connectivity

A legal cleanup erases a vertex with fewer than two occupied neighbours. Its
occupied neighbourhood therefore lies in one singleton, possibly empty. A
path retraction sends the erased vertex to that singleton: any step touching
it contracts to a zero-edge path, and all remaining steps survive. Reflexive
paths need no membership premise, while the theorem endpoints are surviving
occupied sites. This covers the empty-set convention without changing the
actual grid. No assertion concerns arbitrary degree-two heat-bath deaths.
-/

@[expose] public section
namespace MathResearchAnalysis.CleanupConnectivity

open GridCellBoundary (Site)
open GridMajorityPeeling (neighbors4 degree4 cleanup)
open OrthogonalGridConvexity

theorem low_degree_neighbors_in_singleton {S : Finset Site} {v : Site}
    (hd : degree4 S v < 2) :
    ∃ z : Site, ∀ w ∈ S, w ∈ neighbors4 v → w = z := by
  have hc : (neighbors4 v ∩ S).card ≤ 1 := by
    change (neighbors4 v ∩ S).card < 2 at hd
    omega
  obtain ⟨z, hz⟩ := Finset.card_le_one_iff_subset_singleton.mp hc
  refine ⟨z, ?_⟩
  intro w hw hn
  exact Finset.mem_singleton.mp (hz (Finset.mem_inter.mpr ⟨hn, hw⟩))

theorem path_erase_of_degree_lt_two {S : Finset Site} {v a b : Site}
    (hd : degree4 S v < 2) (hav : a ≠ v) (hbv : b ≠ v)
    (hp : Path S a b) : Path (S.erase v) a b := by
  obtain ⟨z, hz⟩ := low_degree_neighbors_in_singleton hd
  let project : Site → Site := fun x => if x = v then z else x
  have hstep : ∀ x y : Site, InternalStep S x y →
      Path (S.erase v) (project x) (project y) := by
    intro x y hxy
    by_cases hx : x = v
    · have hyn : y ∈ neighbors4 v := by simpa only [hx] using hxy.2.2
      have hy : y ≠ v := by
        intro hy
        exact GridMajorityPeeling.not_mem_neighbors4_self v (hy ▸ hyn)
      have hyz : y = z := hz y hxy.2.1 hyn
      have hpx : project x = z := by simp only [project, hx, ite_true]
      have hpy : project y = z := by
        simp only [project, hy, ite_false]
        exact hyz
      rw [hpx, hpy]
    · by_cases hy : y = v
      · have hxn : x ∈ neighbors4 v := by
          simpa only [hy] using ConvexBirthUpdate.neighbors4_symmetric hxy.2.2
        have hxz : x = z := hz x hxy.1 hxn
        have hpx : project x = z := by
          simp only [project, hx, ite_false]
          exact hxz
        have hpy : project y = z := by simp only [project, hy, ite_true]
        rw [hpx, hpy]
      · simp only [project, hx, hy, ite_false]
        exact Relation.ReflTransGen.single
          ⟨Finset.mem_erase.mpr ⟨hx, hxy.1⟩,
            Finset.mem_erase.mpr ⟨hy, hxy.2.1⟩, hxy.2.2⟩
  have hm : Path (S.erase v) (project a) (project b) :=
    Relation.ReflTransGen.lift' project hstep a b hp
  simpa only [project, hav, hbv, ite_false] using hm

theorem fourConnected_erase_of_degree_lt_two {S : Finset Site} {v : Site}
    (hconn : FourConnected S) (hd : degree4 S v < 2) :
    FourConnected (S.erase v) := by
  intro a ha b hb
  obtain ⟨hav, haS⟩ := Finset.mem_erase.mp ha
  obtain ⟨hbv, hbS⟩ := Finset.mem_erase.mp hb
  exact path_erase_of_degree_lt_two hd hav hbv (hconn a haS b hbS)

theorem legal_delete_preserves_fourConnected {S T : Finset Site}
    (hconn : FourConnected S)
    (hdel : FiniteMajorityPeeling.Delete neighbors4 S T) : FourConnected T := by
  obtain ⟨v, _, hd, rfl⟩ := hdel
  exact fourConnected_erase_of_degree_lt_two hconn hd

theorem deletes_preserve_fourConnected {S T : Finset Site}
    (hconn : FourConnected S)
    (hdel : FiniteMajorityPeeling.Deletes neighbors4 S T) : FourConnected T := by
  induction hdel with
  | refl => exact hconn
  | tail _ hstep ih => exact legal_delete_preserves_fourConnected ih hstep

theorem cleanup_fourConnected {S : Finset Site} (hconn : FourConnected S) :
    FourConnected (cleanup S) :=
  deletes_preserve_fourConnected hconn (GridMajorityPeeling.cleanup_reachable S)

end MathResearchAnalysis.CleanupConnectivity
