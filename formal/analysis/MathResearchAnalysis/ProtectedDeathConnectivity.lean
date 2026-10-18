module
public import MathResearchAnalysis.ProtectedColumnGeometry
public import MathResearchAnalysis.ProtectedCornerGeometry
public import MathResearchAnalysis.CleanupConnectivity
set_option autoImplicit false
/-! Local occupied detours under the actual protected domains, and their lift to
four-neighbour connectivity after an actual degree-two death and cleanup.
The original geometric Good invariant and probabilistic droplet tails are not asserted. -/
@[expose] public section
namespace MathResearchAnalysis.ProtectedDeathConnectivity
open GridCellBoundary (Site)
open InfiniteGridModel (north east south west)
open GridMajorityPeeling (neighbors4 degree4 cleanup mem_neighbors4)
open OrthogonalGridConvexity
open ClippedProtectedGeometry (innerDiamond)

/-- Retract each occurrence of the removed vertex to one of its neighbours. -/
theorem path_erase_of_neighbor_bypass {S : Finset Site} {v a b : Site}
    (hlink : ∀ u ∈ S, u ∈ neighbors4 v → ∀ w ∈ S, w ∈ neighbors4 v →
      Path (S.erase v) u w)
    (hav : a ≠ v) (hbv : b ≠ v) (hp : Path S a b) : Path (S.erase v) a b := by
  by_cases hex : ∃ z ∈ S, z ∈ neighbors4 v
  · obtain ⟨z,hz,hzn⟩ := hex
    let project : Site → Site := fun x => if x = v then z else x
    have hstep : ∀ x y : Site, InternalStep S x y →
        Path (S.erase v) (project x) (project y) := by
      intro x y hxy
      by_cases hx : x = v
      · have hyn : y ∈ neighbors4 v := by simpa only [hx] using hxy.2.2
        have hy : y ≠ v := fun h => GridMajorityPeeling.not_mem_neighbors4_self v (h ▸ hyn)
        simpa only [project,hx,hy,ite_true,ite_false] using hlink z hz hzn y hxy.2.1 hyn
      · by_cases hy : y = v
        · have hxn : x ∈ neighbors4 v := by
            simpa only [hy] using ConvexBirthUpdate.neighbors4_symmetric hxy.2.2
          simpa only [project,hx,hy,ite_true,ite_false] using hlink x hxy.1 hxn z hz hzn
        · simp only [project,hx,hy,ite_false]
          exact Relation.ReflTransGen.single
            ⟨Finset.mem_erase.mpr ⟨hx,hxy.1⟩,Finset.mem_erase.mpr ⟨hy,hxy.2.1⟩,hxy.2.2⟩
    have hm : Path (S.erase v) (project a) (project b) :=
      Relation.ReflTransGen.lift' project hstep a b hp
    simpa only [project,hav,hbv,ite_false] using hm
  · have hd : degree4 S v < 2 := by
      have he : neighbors4 v ∩ S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact hex ⟨z,(Finset.mem_inter.mp hz).2,(Finset.mem_inter.mp hz).1⟩
      simp [degree4,he]
    exact CleanupConnectivity.path_erase_of_degree_lt_two hd hav hbv hp

theorem fourConnected_erase_of_neighbor_bypass {S : Finset Site} {v : Site}
    (hconn : FourConnected S)
    (hlink : ∀ u ∈ S, u ∈ neighbors4 v → ∀ w ∈ S, w ∈ neighbors4 v →
      Path (S.erase v) u w) : FourConnected (S.erase v) := by
  intro a ha b hb
  obtain ⟨hav,haS⟩ := Finset.mem_erase.mp ha
  obtain ⟨hbv,hbS⟩ := Finset.mem_erase.mp hb
  exact path_erase_of_neighbor_bypass hlink hav hbv (hconn a haS b hbS)

theorem neighbor_bypass_via {S : Finset Site} {v z : Site}
    (hz : z ∈ S) (hzv : z ≠ v)
    (hall : ∀ a ∈ S, a ∈ neighbors4 v → a ∈ neighbors4 z) :
    ∀ a ∈ S, a ∈ neighbors4 v → ∀ b ∈ S, b ∈ neighbors4 v → Path (S.erase v) a b := by
  intro a ha han b hb hbn
  have hav : a ≠ v := fun h => GridMajorityPeeling.not_mem_neighbors4_self v (h ▸ han)
  have hbv : b ≠ v := fun h => GridMajorityPeeling.not_mem_neighbors4_self v (h ▸ hbn)
  exact (Relation.ReflTransGen.single
    ⟨Finset.mem_erase.mpr ⟨hav,ha⟩,Finset.mem_erase.mpr ⟨hzv,hz⟩,
      ConvexBirthUpdate.neighbors4_symmetric (hall a ha han)⟩).trans
    (Relation.ReflTransGen.single
      ⟨Finset.mem_erase.mpr ⟨hzv,hz⟩,Finset.mem_erase.mpr ⟨hbv,hb⟩,hall b hb hbn⟩)

theorem northeast_neighbor_bypass {S : Finset Site} {v : Site}
    (hc : south v ∉ S) (hd : west v ∉ S) (hz : north (east v) ∈ S) :
    ∀ u ∈ S, u ∈ neighbors4 v → ∀ w ∈ S, w ∈ neighbors4 v → Path (S.erase v) u w := by
  apply neighbor_bypass_via hz
  · intro h
    have hx := congrArg Prod.fst h
    dsimp [north,east,south,west] at hx
    omega
  · intro u hu hun
    rcases (mem_neighbors4 v u).mp hun with h | h | h | h
    all_goals subst u
    all_goals first
      | exact False.elim (hc hu)
      | exact False.elim (hd hu)
      | simp [mem_neighbors4,north,east,south,west]

theorem northwest_neighbor_bypass {S : Finset Site} {v : Site}
    (hc : south v ∉ S) (hd : east v ∉ S) (hz : north (west v) ∈ S) :
    ∀ u ∈ S, u ∈ neighbors4 v → ∀ w ∈ S, w ∈ neighbors4 v → Path (S.erase v) u w := by
  apply neighbor_bypass_via hz
  · intro h
    have hx := congrArg Prod.fst h
    dsimp [north,east,south,west] at hx
    omega
  · intro u hu hun
    rcases (mem_neighbors4 v u).mp hun with h | h | h | h
    all_goals subst u
    all_goals first
      | exact False.elim (hc hu)
      | exact False.elim (hd hu)
      | simp [mem_neighbors4,north,east,south,west]

theorem southeast_neighbor_bypass {S : Finset Site} {v : Site}
    (hc : north v ∉ S) (hd : west v ∉ S) (hz : south (east v) ∈ S) :
    ∀ u ∈ S, u ∈ neighbors4 v → ∀ w ∈ S, w ∈ neighbors4 v → Path (S.erase v) u w := by
  apply neighbor_bypass_via hz
  · intro h
    have hx := congrArg Prod.fst h
    dsimp [north,east,south,west] at hx
    omega
  · intro u hu hun
    rcases (mem_neighbors4 v u).mp hun with h | h | h | h
    all_goals subst u
    all_goals first
      | exact False.elim (hc hu)
      | exact False.elim (hd hu)
      | simp [mem_neighbors4,north,east,south,west]

theorem southwest_neighbor_bypass {S : Finset Site} {v : Site}
    (hc : north v ∉ S) (hd : east v ∉ S) (hz : south (west v) ∈ S) :
    ∀ u ∈ S, u ∈ neighbors4 v → ∀ w ∈ S, w ∈ neighbors4 v → Path (S.erase v) u w := by
  apply neighbor_bypass_via hz
  · intro h
    have hx := congrArg Prod.fst h
    dsimp [north,east,south,west] at hx
    omega
  · intro u hu hun
    rcases (mem_neighbors4 v u).mp hun with h | h | h | h
    all_goals subst u
    all_goals first
      | exact False.elim (hc hu)
      | exact False.elim (hd hu)
      | simp [mem_neighbors4,north,east,south,west]


theorem protected_neighbor_bypass {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} {v : Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hst : DropletModifiedWord.Stable S) (hvS : v ∈ S)
    (hD : innerDiamond L ⊆ S) (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    (hd : degree4 S v = 2) :
    ∀ u ∈ S, u ∈ neighbors4 v → ∀ w ∈ S, w ∈ neighbors4 v → Path (S.erase v) u w := by
  have hh := ProtectedColumnGeometry.protected_no_horizontal_opposites hL hr hc hst hvS hD hclip hd
  have hv := ProtectedColumnGeometry.protected_no_vertical_opposites hL hr hc hst hvS hD hclip hd
  by_cases hn : north v ∈ S <;> by_cases he : east v ∈ S <;>
    by_cases hs : south v ∈ S <;> by_cases hw : west v ∈ S
  all_goals simp [hn,he,hs,hw] at hh hv
  all_goals simp [GridMajorityPeeling.degree4_eq_four_inputs,GridMajorityPeeling.state,hn,he,hs,hw] at hd
  all_goals first
    | exact northeast_neighbor_bypass hs hw
        (ProtectedCornerGeometry.northeast_diagonal hL hr hc hvS hn he hs hw hD hclip)
    | exact northwest_neighbor_bypass hs he
        (ProtectedCornerGeometry.northwest_diagonal hL hr hc hvS hn hw hs he hD hclip)
    | exact southeast_neighbor_bypass hn hw
        (ProtectedCornerGeometry.southeast_diagonal hL hr hc hvS hs he hn hw hD hclip)
    | exact southwest_neighbor_bypass hn he
        (ProtectedCornerGeometry.southwest_diagonal hL hr hc hvS hs hw hn he hD hclip)

theorem protected_erase_fourConnected {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} {v : Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hst : DropletModifiedWord.Stable S) (hvS : v ∈ S) (hconn : FourConnected S)
    (hD : innerDiamond L ⊆ S) (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    (hd : degree4 S v = 2) : FourConnected (S.erase v) :=
  fourConnected_erase_of_neighbor_bypass hconn
    (protected_neighbor_bypass hL hr hc hst hvS hD hclip hd)

theorem protected_cleanup_erase_fourConnected {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} {v : Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hst : DropletModifiedWord.Stable S) (hvS : v ∈ S) (hconn : FourConnected S)
    (hD : innerDiamond L ⊆ S) (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    (hd : degree4 S v = 2) : FourConnected (cleanup (S.erase v)) :=
  CleanupConnectivity.cleanup_fourConnected
    (protected_erase_fourConnected hL hr hc hst hvS hconn hD hclip hd)

theorem actual_protected_death_preserves {L : Nat} (hL : 2 ≤ L)
    {D S : Finset Site} {v : Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hst : DropletModifiedWord.Stable S) (hvS : v ∈ S) (hconn : FourConnected S)
    (hD : innerDiamond L ⊆ S) (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    (hvD : v ∈ D) (hd : degree4 S v = 2) :
    RowConvex (DropletModifiedWord.modifiedStep D S v false) ∧
    ColumnConvex (DropletModifiedWord.modifiedStep D S v false) ∧
    FourConnected (DropletModifiedWord.modifiedStep D S v false) := by
  rw [DropletModifiedWord.modifiedStep,ite_eq_left hvD,ConvexLocalUpdate.rawStep_of_death hst hvS hd]
  have hcv := ProtectedColumnGeometry.protected_cleanup_erase_convexity hL hr hc hst hvS hD hclip hd
  exact ⟨hcv.1,hcv.2,protected_cleanup_erase_fourConnected hL hr hc hst hvS hconn hD hclip hd⟩

end MathResearchAnalysis.ProtectedDeathConnectivity
