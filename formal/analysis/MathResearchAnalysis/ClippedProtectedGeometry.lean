module

public import MathResearchAnalysis.ClippedDiamondGeometry

set_option autoImplicit false

/-!
# The actual closed protected diamond in CMST Section 8

The inner integer diamond is D = {z : 10 (|x|+|y|) ≤ 9L}. Its boundary is
outside D, with a genuine four-neighbour in D, as in CMST Section 2.
The stopping protection is D ∪ ∂D, not D alone (Section 8, Definition 7 and
its following stopping rule). Source: https://arxiv.org/html/1007.3599v2.
This module proves only finite geometry, not Good invariance or exit area.
-/

@[expose] public section

namespace MathResearchAnalysis.ClippedProtectedGeometry

open InfiniteGridModel

abbrev Site := InfiniteGridModel.Site

def norm1 (z : Site) : Int := |z.1| + |z.2|

def innerDiamond (L : Nat) : Finset Site :=
  ((Finset.Icc (-(L : Int)) L) ×ˢ (Finset.Icc (-(L : Int)) L)).filter
    (fun z => 10 * norm1 z ≤ 9 * (L : Int))

def outerBoundary (L : Nat) : Finset Site :=
  ((innerDiamond L).biUnion GridMajorityPeeling.neighbors4) \ innerDiamond L

def protectedSites (L : Nat) : Finset Site := innerDiamond L ∪ outerBoundary L

theorem norm1_nonneg (z : Site) : 0 ≤ norm1 z :=
  add_nonneg (abs_nonneg z.1) (abs_nonneg z.2)

theorem coordinate_abs_le_norm1 (z : Site) : |z.1| ≤ norm1 z ∧ |z.2| ≤ norm1 z := by
  have hx := abs_nonneg z.1
  have hy := abs_nonneg z.2
  unfold norm1
  omega

theorem mem_innerDiamond (L : Nat) (z : Site) :
    z ∈ innerDiamond L ↔ 10 * norm1 z ≤ 9 * (L : Int) := by
  simp only [innerDiamond, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    have hn : norm1 z ≤ (L : Int) := by omega
    have hc := coordinate_abs_le_norm1 z
    have hx := (abs_le.mp (hc.1.trans hn))
    have hy := (abs_le.mp (hc.2.trans hn))
    exact ⟨⟨hx, hy⟩, h⟩

theorem mem_innerDiamond_iff_real (L : Nat) (z : Site) :
    z ∈ innerDiamond L ↔ (norm1 z : Real) ≤ (9 / 10 : Real) * L := by
  rw [mem_innerDiamond]
  constructor
  · intro h
    have hr : (10 : Real) * norm1 z ≤ 9 * (L : Real) := by exact_mod_cast h
    nlinarith
  · intro h
    have hr : (10 : Real) * norm1 z ≤ 9 * (L : Real) := by nlinarith
    exact_mod_cast hr

theorem zero_mem_innerDiamond (L : Nat) : (0, 0) ∈ innerDiamond L := by
  rw [mem_innerDiamond]
  simp [norm1]

theorem mem_outerBoundary (L : Nat) (z : Site) :
    z ∈ outerBoundary L ↔ z ∉ innerDiamond L ∧
      ∃ y ∈ innerDiamond L, z ∈ GridMajorityPeeling.neighbors4 y := by
  simp only [outerBoundary, Finset.mem_sdiff, Finset.mem_biUnion]
  tauto

theorem mem_protectedSites (L : Nat) (z : Site) :
    z ∈ protectedSites L ↔ z ∈ innerDiamond L ∨
      ∃ y ∈ innerDiamond L, z ∈ GridMajorityPeeling.neighbors4 y := by
  simp only [protectedSites, Finset.mem_union, mem_outerBoundary]
  tauto

theorem innerDiamond_subset_protectedSites (L : Nat) :
    innerDiamond L ⊆ protectedSites L := Finset.subset_union_left

theorem outerBoundary_subset_protectedSites (L : Nat) :
    outerBoundary L ⊆ protectedSites L := Finset.subset_union_right

theorem boundary_disjoint_inner (L : Nat) : Disjoint (outerBoundary L) (innerDiamond L) := by
  apply Finset.disjoint_left.mpr
  intro z hz hi
  exact ((mem_outerBoundary L z).mp hz).1 hi

theorem neighbors4_symmetric (z y : Site) :
    y ∈ GridMajorityPeeling.neighbors4 z ↔ z ∈ GridMajorityPeeling.neighbors4 y := by
  simp only [GridMajorityPeeling.mem_neighbors4, north, east, south, west, Prod.ext_iff]
  omega

theorem norm1_neighbor_le (z y : Site) (h : y ∈ GridMajorityPeeling.neighbors4 z) :
    norm1 y ≤ norm1 z + 1 := by
  have hxp := abs_add_le z.1 (1 : Int)
  have hxm := abs_add_le z.1 (-1 : Int)
  have hyp := abs_add_le z.2 (1 : Int)
  have hym := abs_add_le z.2 (-1 : Int)
  norm_num at hxp hxm hyp hym
  rcases (GridMajorityPeeling.mem_neighbors4 z y).mp h with rfl | rfl | rfl | rfl
  all_goals dsimp [norm1, north, east, south, west]
  all_goals try simp only [sub_eq_add_neg] at *
  all_goals omega

private theorem abs_toward_of_ne_zero (a : Int) (ha : a ≠ 0) :
    |ClippedDiamondGeometry.toward a| + 1 = |a| := by
  by_cases hp : 0 < a
  · have hp0 : 0 ≤ a := by omega
    have hp1 : 0 ≤ a - 1 := by omega
    simp only [ClippedDiamondGeometry.toward, ite_eq_left hp, abs_of_nonneg hp0, abs_of_nonneg hp1]
    omega
  · have hn0 : a ≤ 0 := by omega
    have hn1 : a + 1 ≤ 0 := by omega
    simp only [ClippedDiamondGeometry.toward, ite_eq_right hp, abs_of_nonpos hn0, abs_of_nonpos hn1]
    omega

theorem exists_neighbor_smaller_norm1 (z : Site) (hz : 0 < norm1 z) :
    ∃ y, y ∈ GridMajorityPeeling.neighbors4 z ∧ norm1 y + 1 = norm1 z := by
  by_cases hx : z.1 = 0
  · have hy : z.2 ≠ 0 := by
      intro hy
      simp [norm1, hx, hy] at hz
    refine ⟨ClippedDiamondGeometry.verticalNeighbor z,
      ClippedDiamondGeometry.verticalNeighbor_mem_neighbors4 z, ?_⟩
    have h := abs_toward_of_ne_zero z.2 hy
    dsimp [norm1, ClippedDiamondGeometry.verticalNeighbor]
    omega
  · refine ⟨ClippedDiamondGeometry.horizontalNeighbor z,
      ClippedDiamondGeometry.horizontalNeighbor_mem_neighbors4 z, ?_⟩
    have h := abs_toward_of_ne_zero z.1 hx
    dsimp [norm1, ClippedDiamondGeometry.horizontalNeighbor]
    omega

theorem boundaryBand_of_mem_innerDiamond (L : Nat) {z : Site}
    (hz : z ∈ innerDiamond L) : ClippedDiamondGeometry.boundaryBand L z := by
  have h := (mem_innerDiamond L z).mp hz
  change 10 * norm1 z ≤ 9 * (L : Int) + 10
  omega

theorem boundaryBand_of_mem_outerBoundary (L : Nat) {z : Site}
    (hz : z ∈ outerBoundary L) : ClippedDiamondGeometry.boundaryBand L z := by
  obtain ⟨_, y, hy, hn⟩ := (mem_outerBoundary L z).mp hz
  have hd := (mem_innerDiamond L y).mp hy
  have hs := norm1_neighbor_le y z hn
  change 10 * norm1 z ≤ 9 * (L : Int) + 10
  omega

theorem mem_outerBoundary_iff_band (L : Nat) (z : Site) :
    z ∈ outerBoundary L ↔ z ∉ innerDiamond L ∧ ClippedDiamondGeometry.boundaryBand L z := by
  constructor
  · intro hz
    exact ⟨((mem_outerBoundary L z).mp hz).1, boundaryBand_of_mem_outerBoundary L hz⟩
  · rintro ⟨hnot, hband⟩
    have hn := norm1_nonneg z
    have hout : ¬ 10 * norm1 z ≤ 9 * (L : Int) := by simpa only [← mem_innerDiamond] using hnot
    have hz : 0 < norm1 z := by omega
    obtain ⟨y, hy, heq⟩ := exists_neighbor_smaller_norm1 z hz
    apply (mem_outerBoundary L z).mpr
    refine ⟨hnot, y, (mem_innerDiamond L y).mpr ?_, (neighbors4_symmetric z y).mp hy⟩
    change 10 * norm1 z ≤ 9 * (L : Int) + 10 at hband
    omega

theorem mem_protectedSites_iff_band (L : Nat) (z : Site) :
    z ∈ protectedSites L ↔ ClippedDiamondGeometry.boundaryBand L z := by
  constructor
  · intro hz
    rcases Finset.mem_union.mp hz with hi | hb
    · exact boundaryBand_of_mem_innerDiamond L hi
    · exact boundaryBand_of_mem_outerBoundary L hb
  · intro hz
    by_cases hi : z ∈ innerDiamond L
    · exact Finset.mem_union_left _ hi
    · exact Finset.mem_union_right _ ((mem_outerBoundary_iff_band L z).mpr ⟨hi, hz⟩)

theorem protectedSites_nonempty (L : Nat) : (protectedSites L).Nonempty :=
  ⟨(0, 0), innerDiamond_subset_protectedSites L (zero_mem_innerDiamond L)⟩

theorem protectedSites_subset_clippedDomain_of_pos {L : Nat} (hL : 1 ≤ L) :
    protectedSites L ⊆ ClippedDiamondGeometry.clippedDomain L := by
  intro z hz
  have hb := (mem_protectedSites_iff_band L z).mp hz
  change 10 * norm1 z ≤ 9 * (L : Int) + 10 at hb
  have hLZ : 1 ≤ (L : Int) := by exact_mod_cast hL
  have hn : norm1 z ≤ (L : Int) := by omega
  have hc := coordinate_abs_le_norm1 z
  exact (ClippedDiamondGeometry.mem_clippedDomain L z).mpr
    ⟨hc.1.trans hn, hc.2.trans hn, by change norm1 z ≤ (L : Int) + 1; omega⟩

theorem protectedSites_subset_clippedDomain {L : Nat} (hL : 40 ≤ L) :
    protectedSites L ⊆ ClippedDiamondGeometry.clippedDomain L :=
  protectedSites_subset_clippedDomain_of_pos (by omega)
theorem initial_all_minus_on_protected {L : Nat} (hL : 40 ≤ L) {z : Site}
    (hz : z ∈ protectedSites L) :
    GridMajorityPeeling.state (ClippedDiamondGeometry.clippedDomain L) z = true := by
  exact decide_eq_true (protectedSites_subset_clippedDomain hL hz)

theorem initial_cleanup_contains_protected {L : Nat} (hL : 40 ≤ L) :
    protectedSites L ⊆ GridMajorityPeeling.cleanup (ClippedDiamondGeometry.clippedDomain L) := by
  rw [ClippedDiamondGeometry.cleanup_clippedDomain (by omega : 1 ≤ L)]
  exact protectedSites_subset_clippedDomain hL

theorem directedBlock_control {L : Nat} (hL : 40 ≤ L) {z : Site}
    (hz : z ∈ protectedSites L) (horizontal vertical : Bool) :
    ClippedDiamondGeometry.directedBlock L z horizontal vertical ⊆
        ClippedDiamondGeometry.clippedDomain L ∧
      (ClippedDiamondGeometry.directedBlock L z horizontal vertical).card = (L / 20) ^ 2 ∧
      (L : Real) ^ 2 / 1600 ≤
        ((ClippedDiamondGeometry.directedBlock L z horizontal vertical).card : Real) := by
  exact ⟨ClippedDiamondGeometry.directedBlock_subset_clippedDomain hL
      ((mem_protectedSites_iff_band L z).mp hz) horizontal vertical,
    ClippedDiamondGeometry.directedBlock_card L z horizontal vertical,
    ClippedDiamondGeometry.real_sq_div_le_directedBlock_card hL z horizontal vertical⟩

end MathResearchAnalysis.ClippedProtectedGeometry

