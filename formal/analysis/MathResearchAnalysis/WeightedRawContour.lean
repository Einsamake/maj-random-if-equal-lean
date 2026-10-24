module

public import MathResearchAnalysis.ForbiddenBirthControl
public import MathResearchAnalysis.OrthogonalBoundaryConnectivity
public import MathResearchAnalysis.ProtectedEvolution

set_option autoImplicit false

/-!
# Actual corner-to-valley pairs across adjacent occupied columns

A rising north endpoint is paired to the vacant site just above the previous
column. Their weight difference is paid by genuine exposed west half-edges.
These are components of a weighted raw-rate estimate, not that final estimate.
-/

@[expose] public noncomputable section
namespace MathResearchAnalysis.WeightedRawContour

open InfiniteGridModel (Site north east south west)
open OrthogonalGridConvexity (RowConvex ColumnConvex FourConnected)
open OrthogonalPerimeter (northCells)
open GridCellBoundary (HalfEdge boundary perimeter)
open ForbiddenBirthControl (weight)

/-- A northwestern top corner with an occupied preceding column must rise. -/
theorem northwest_previous_top_lower {S : Finset Site}
    (hc : ColumnConvex S) (hconn : FourConnected S) {u v : Site}
    (hu : u ∈ northCells S) (hv : v ∈ northCells S)
    (hx : v.1 = u.1 + 1) (hw : west v ∉ S) : u.2 < v.2 := by
  obtain ⟨y,hyL,hyR⟩ := OrthogonalVacantQuadrant.path_crosses_vertical_cut u.1
    (hconn u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1)
    (by rfl) (by omega)
  have hyu := OrthogonalBoundaryConnectivity.north_occupied_le hc hu hyL rfl
  have hyv := OrthogonalBoundaryConnectivity.north_occupied_le hc hv hyR (by dsimp; omega)
  by_contra hn
  have hs := hc u.1 y u.2 v.2 hyL (Finset.mem_filter.mp hu).1 hyv (by omega)
  apply hw
  convert hs using 1
  apply congrArg (fun x => (x,v.2))
  omega

/-- The actual candidate valley has its east and south neighbours occupied. -/
theorem rising_tops_valley {S : Finset Site}
    (hc : ColumnConvex S) (hconn : FourConnected S) {u v : Site}
    (hu : u ∈ northCells S) (hv : v ∈ northCells S)
    (hx : v.1 = u.1 + 1) (hy : u.2 < v.2) :
    north u ∉ S ∧ east (north u) ∈ S ∧ south (north u) ∈ S := by
  obtain ⟨y,hyL,hyR⟩ := OrthogonalVacantQuadrant.path_crosses_vertical_cut u.1
    (hconn u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1)
    (by rfl) (by omega)
  have hyu := OrthogonalBoundaryConnectivity.north_occupied_le hc hu hyL rfl
  have hright : (v.1,y) ∈ S := by simpa only [hx] using hyR
  have he := hc v.1 y v.2 (u.2+1) hright (Finset.mem_filter.mp hv).1 (by omega) (by omega)
  refine ⟨(Finset.mem_filter.mp hu).2,?_,?_⟩
  · simpa only [north,east,hx] using he
  · simpa only [north,south,add_sub_cancel_right] using (Finset.mem_filter.mp hu).1

/-- Orthogonal convexity makes this valley an actual fair-tie birth site. -/
theorem rising_tops_valley_degree {S : Finset Site}
    (hr : RowConvex S) (hc : ColumnConvex S) (hconn : FourConnected S) {u v : Site}
    (hu : u ∈ northCells S) (hv : v ∈ northCells S)
    (hx : v.1 = u.1 + 1) (hy : u.2 < v.2) :
    GridMajorityPeeling.degree4 S (north u) = 2 := by
  obtain ⟨hn,he,hs⟩ := rising_tops_valley hc hconn hu hv hx hy
  have hlo : 2 ≤ GridMajorityPeeling.degree4 S (north u) := by
    rw [GridMajorityPeeling.degree4_eq_four_inputs]
    have he' : GridMajorityPeeling.state S (east (north u)) = true := by
      simp [GridMajorityPeeling.state,he]
    have hs' : GridMajorityPeeling.state S (south (north u)) = true := by
      simp [GridMajorityPeeling.state,hs]
    rw [he',hs']
    cases GridMajorityPeeling.state S (north (north u)) <;>
      cases GridMajorityPeeling.state S (west (north u)) <;> norm_num
  exact le_antisymm (ConvexLocalUpdate.vacant_degree4_le_two hr hc hn) hlo

/-- Every vertical unit paid for by a rise is an actual exposed west edge. -/
theorem rising_tops_west_edges {S : Finset Site}
    (hc : ColumnConvex S) (hconn : FourConnected S) {u v : Site}
    (hu : u ∈ northCells S) (hv : v ∈ northCells S)
    (hx : v.1 = u.1 + 1) (_hy : u.2 < v.2) :
    ∀ z : Int, u.2 < z → z ≤ v.2 → ((v.1,z),3) ∈ boundary S := by
  obtain ⟨y,hyL,hyR⟩ := OrthogonalVacantQuadrant.path_crosses_vertical_cut u.1
    (hconn u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1)
    (by rfl) (by omega)
  have hyu := OrthogonalBoundaryConnectivity.north_occupied_le hc hu hyL rfl
  intro z hza hzb
  apply (GridCellBoundary.mem_boundary_west S (v.1,z)).mpr
  constructor
  · exact hc v.1 y v.2 z (by simpa only [hx] using hyR)
      (Finset.mem_filter.mp hv).1 (by omega) hzb
  · intro hw
    have hbound := OrthogonalBoundaryConnectivity.north_occupied_le hc hu hw
      (by change v.1-1 = u.1; omega)
    change z ≤ u.2 at hbound
    omega

/-- The concrete 1-Lipschitz weight needs at most the vertical rise budget. -/
theorem rising_tops_weight_difference (L : Nat) {u v : Site}
    (hx : v.1 = u.1 + 1) (hy : u.2 < v.2) :
    weight L v - weight L (north u) ≤ ((v.2-u.2 : Int) : Real) := by
  have hxabs : |u.1| ≤ |v.1| + 1 := by
    have h := abs_add_le v.1 (-1 : Int)
    have he : v.1 + -1 = u.1 := by omega
    rw [he] at h
    simpa only [abs_neg,abs_one] using h
  have hyabs : |u.2+1| ≤ |v.2| + (v.2-u.2-1) := by
    calc
      |u.2+1| = |v.2+(u.2+1-v.2)| := by congr 1; ring
      _ ≤ |v.2| + |u.2+1-v.2| := abs_add_le _ _
      _ = _ := by rw [abs_of_nonpos (by omega : u.2+1-v.2 ≤ 0)]; ring
  have hsum : |u.1| + |u.2+1| ≤ |v.1| + |v.2| + (v.2-u.2) := by omega
  have hr : ((|u.1|+|u.2+1| : Int) : Real) ≤
      ((|v.1|+|v.2| : Int) : Real) + ((v.2-u.2 : Int) : Real) := by exact_mod_cast hsum
  unfold weight
  dsimp [north]
  linarith

def westSegment (u v : Site) : Finset HalfEdge :=
  (Finset.Icc (u.2+1) v.2).image (fun y : Int => ((v.1,y),3))

theorem westSegment_card (u v : Site) :
    (westSegment u v).card = (v.2-u.2).toNat := by
  rw [westSegment,Finset.card_image_of_injective _ (show Function.Injective
    (fun y : Int => (((v.1,y),3) : HalfEdge)) from fun a b h =>
      congrArg (fun e : HalfEdge => e.1.2) h),Int.card_Icc]
  congr 1
  omega

theorem rising_tops_westSegment_subset {S : Finset Site}
    (hc : ColumnConvex S) (hconn : FourConnected S) {u v : Site}
    (hu : u ∈ northCells S) (hv : v ∈ northCells S)
    (hx : v.1 = u.1 + 1) (hy : u.2 < v.2) : westSegment u v ⊆ boundary S := by
  intro e he
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp he
  have hz := Finset.mem_Icc.mp hz
  exact rising_tops_west_edges hc hconn hu hv hx hy z (by omega) hz.2

theorem rising_tops_weight_le_segment (L : Nat) {u v : Site}
    (hx : v.1 = u.1 + 1) (hy : u.2 < v.2) :
    weight L v - weight L (north u) ≤ ((westSegment u v).card : Real) := by
  have hnat : (((v.2-u.2).toNat : Nat) : Real) = ((v.2-u.2 : Int) : Real) := by
    exact_mod_cast (Int.toNat_of_nonneg (by omega : 0 ≤ v.2-u.2))
  rw [westSegment_card,hnat]
  exact rising_tops_weight_difference L hx hy

theorem paired_valley_injective {S : Finset Site} (hc : ColumnConvex S)
    {u v u' v' : Site} (hv : v ∈ northCells S) (hv' : v' ∈ northCells S)
    (hx : v.1 = u.1 + 1) (hx' : v'.1 = u'.1 + 1)
    (he : north u = north u') : v = v' := by
  apply OrthogonalPerimeter.north_endpoint_unique hc hv hv'
  have h := congrArg Prod.fst he
  dsimp [north] at h
  omega


/-- Actual occupied NW corners. Stability will be used only when all four
orientations are identified with the complete raw update rate. -/
def northwestCorners (S : Finset Site) : Finset Site :=
  S.filter (fun v => north v ∉ S ∧ west v ∉ S)

def northwestValleys (E S : Finset Site) : Finset Site :=
  E.filter (fun v => v ∉ S ∧ east v ∈ S ∧ south v ∈ S)

def northwestCharge (L : Nat) (E S : Finset Site) : Real :=
  (∑ v ∈ northwestCorners S, weight L v) -
    ∑ v ∈ northwestValleys E S, weight L v

def northwestPairs (S : Finset Site) : Finset Site :=
  (northwestCorners S).filter (fun v => v.1-1 ∈ S.image Prod.fst)

def previousTop (S : Finset Site) (v : Site) : Site := by
  classical
  exact if h : ∃ u ∈ northCells S, u.1 = v.1-1 then h.choose else v

def pairedValley (S : Finset Site) (v : Site) : Site := north (previousTop S v)

theorem northwestCorner_north {S : Finset Site} {v : Site}
    (hv : v ∈ northwestCorners S) : v ∈ northCells S := by
  obtain ⟨hvS,hn,_⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hvS,hn⟩

theorem pair_spec {S : Finset Site} {v : Site} (hv : v ∈ northwestPairs S) :
    v ∈ northwestCorners S ∧ previousTop S v ∈ northCells S ∧
      (previousTop S v).1 = v.1-1 := by
  classical
  obtain ⟨hv,hx⟩ := Finset.mem_filter.mp hv
  have hex : ∃ u ∈ northCells S, u.1 = v.1-1 := OrthogonalPerimeter.north_endpoint_exists S hx
  refine ⟨hv,?_⟩
  unfold previousTop
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem pair_rises {S : Finset Site} (hc : ColumnConvex S) (hconn : FourConnected S)
    {v : Site} (hv : v ∈ northwestPairs S) : (previousTop S v).2 < v.2 := by
  obtain ⟨hcorner,hprev,hx⟩ := pair_spec hv
  exact northwest_previous_top_lower hc hconn hprev (northwestCorner_north hcorner)
    (by omega) (Finset.mem_filter.mp hcorner).2.2

theorem pairedValley_facts {S : Finset Site} (hc : ColumnConvex S) (hconn : FourConnected S)
    {v : Site} (hv : v ∈ northwestPairs S) :
    pairedValley S v ∉ S ∧ east (pairedValley S v) ∈ S ∧ south (pairedValley S v) ∈ S := by
  obtain ⟨hcorner,hprev,hx⟩ := pair_spec hv
  exact rising_tops_valley hc hconn hprev (northwestCorner_north hcorner)
    (by omega) (pair_rises hc hconn hv)

theorem east_south_degree_ge_two {S : Finset Site} {v : Site}
    (he : east v ∈ S) (hs : south v ∈ S) : 2 ≤ GridMajorityPeeling.degree4 S v := by
  rw [GridMajorityPeeling.degree4_eq_four_inputs]
  have he' : GridMajorityPeeling.state S (east v) = true := by simp [GridMajorityPeeling.state,he]
  have hs' : GridMajorityPeeling.state S (south v) = true := by simp [GridMajorityPeeling.state,hs]
  rw [he',hs']
  cases GridMajorityPeeling.state S (north v) <;>
    cases GridMajorityPeeling.state S (west v) <;> norm_num

theorem pairedValley_mem_actual {L : Nat} (hL : 1 ≤ L) {S : Finset Site}
    (hc : ColumnConvex S) (hconn : FourConnected S)
    (hSD : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    {v : Site} (hv : v ∈ northwestPairs S) :
    pairedValley S v ∈ northwestValleys (ClippedSquareCoordinates.centeredSites L) S := by
  have hf := pairedValley_facts hc hconn hv
  apply Finset.mem_filter.mpr
  refine ⟨?_,hf⟩
  apply (ClippedSquareCoordinates.mem_centeredSites L hL _).mpr
  exact ForbiddenBirthControl.two_neighbours_in_centered_square hSD _
    (east_south_degree_ge_two hf.2.1 hf.2.2)

theorem pairedValley_injOn {S : Finset Site} (hc : ColumnConvex S) :
    Set.InjOn (pairedValley S) (northwestPairs S : Set Site) := by
  intro v hv v' hv' he
  obtain ⟨hcorner,hprev,hx⟩ := pair_spec hv
  obtain ⟨hcorner',hprev',hx'⟩ := pair_spec hv'
  exact paired_valley_injective hc (northwestCorner_north hcorner)
    (northwestCorner_north hcorner') (by omega) (by omega) he

/-- There is at most one unpaired NW corner: the north endpoint of the
leftmost occupied column. -/
theorem northwest_unpaired_card_le_one {S : Finset Site} (hc : ColumnConvex S)
    (hconn : FourConnected S) : (northwestCorners S \ northwestPairs S).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨huc,hup⟩ := Finset.mem_sdiff.mp hu
  obtain ⟨hvc,hvp⟩ := Finset.mem_sdiff.mp hv
  have huX : u.1 ∈ S.image Prod.fst := Finset.mem_image.mpr ⟨u,(Finset.mem_filter.mp huc).1,rfl⟩
  have hvX : v.1 ∈ S.image Prod.fst := Finset.mem_image.mpr ⟨v,(Finset.mem_filter.mp hvc).1,rfl⟩
  have hnu : u.1-1 ∉ S.image Prod.fst := by
    intro h; exact hup (Finset.mem_filter.mpr ⟨huc,h⟩)
  have hnv : v.1-1 ∉ S.image Prod.fst := by
    intro h; exact hvp (Finset.mem_filter.mpr ⟨hvc,h⟩)
  have heq : u.1 = v.1 := by
    rcases lt_trichotomy u.1 v.1 with h | h | h
    · exact False.elim (hnv (OrthogonalPerimeter.fst_projection_interval hconn huX hvX (by omega) (by omega)))
    · exact h
    · exact False.elim (hnu (OrthogonalPerimeter.fst_projection_interval hconn hvX huX (by omega) (by omega)))
  exact OrthogonalPerimeter.north_endpoint_unique hc
    (northwestCorner_north huc) (northwestCorner_north hvc) heq

theorem northwest_unpaired_weight_le (L : Nat) {S : Finset Site}
    (hc : ColumnConvex S) (hconn : FourConnected S) :
    (∑ v ∈ northwestCorners S \ northwestPairs S, weight L v) ≤ (L : Real)+2 := by
  have h := Finset.sum_le_sum (s := northwestCorners S \ northwestPairs S)
    (fun v _ => ForbiddenBirthControl.weight_upper_bound L v)
  have hn : (((northwestCorners S \ northwestPairs S).card : Nat) : Real) ≤ 1 := by
    exact_mod_cast northwest_unpaired_card_le_one hc hconn
  simp only [Finset.sum_const,nsmul_eq_mul] at h
  have hL : (0 : Real) ≤ (L : Real) := Nat.cast_nonneg L
  nlinarith

theorem paired_segments_disjoint {S : Finset Site} (hc : ColumnConvex S) :
    (northwestPairs S : Set Site).PairwiseDisjoint (fun v => westSegment (previousTop S v) v) := by
  classical
  intro v hv v' hv' hne
  apply Finset.disjoint_left.mpr
  intro e he he'
  obtain ⟨z,hz,hze⟩ := Finset.mem_image.mp he
  obtain ⟨z',hz',hze'⟩ := Finset.mem_image.mp he'
  have heq : (((v.1,z),3) : HalfEdge) = ((v'.1,z'),3) := hze.trans hze'.symm
  have hx : v.1 = v'.1 := congrArg (fun e : HalfEdge => e.1.1) heq
  exact hne (OrthogonalPerimeter.north_endpoint_unique hc
    (northwestCorner_north (pair_spec hv).1) (northwestCorner_north (pair_spec hv').1) hx)

/-- All paid NW edge segments are genuinely disjoint subsets of the boundary. -/
theorem paired_segments_card_le {S : Finset Site} (hc : ColumnConvex S)
    (hconn : FourConnected S) :
    (∑ v ∈ northwestPairs S, (westSegment (previousTop S v) v).card) ≤ perimeter S := by
  classical
  have hs : (northwestPairs S).biUnion (fun v => westSegment (previousTop S v) v) ⊆ boundary S := by
    intro e he
    obtain ⟨v,hv,he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨hcorner,hprev,hx⟩ := pair_spec hv
    exact rising_tops_westSegment_subset hc hconn hprev (northwestCorner_north hcorner)
      (by omega) (pair_rises hc hconn hv) he
  rw [← Finset.card_biUnion (paired_segments_disjoint hc)]
  exact Finset.card_le_card hs

theorem paired_weight_difference_le (L : Nat) {S : Finset Site}
    (hc : ColumnConvex S) (hconn : FourConnected S) :
    (∑ v ∈ northwestPairs S, (weight L v-weight L (pairedValley S v))) ≤ (perimeter S : Real) := by
  have h : (∑ v ∈ northwestPairs S, (weight L v-weight L (pairedValley S v))) ≤
      ∑ v ∈ northwestPairs S, ((westSegment (previousTop S v) v).card : Real) := by
    apply Finset.sum_le_sum
    intro v hv
    have hs := pair_spec hv
    exact rising_tops_weight_le_segment L (by omega) (pair_rises hc hconn hv)
  have h' : (∑ v ∈ northwestPairs S, ((westSegment (previousTop S v) v).card : Real)) ≤ (perimeter S : Real) := by
    exact_mod_cast paired_segments_card_le hc hconn
  exact h.trans h'

theorem valley_weight_nonnegative {L : Nat} {E S : Finset Site}
    (hSD : S ⊆ ClippedDiamondGeometry.clippedDomain L) {v : Site}
    (hv : v ∈ northwestValleys E S) : 0 ≤ weight L v := by
  obtain ⟨_,hnot,he,hs⟩ := Finset.mem_filter.mp hv
  by_cases hD : v ∈ ClippedDiamondGeometry.clippedDomain L
  · exact le_trans (by norm_num) (ForbiddenBirthControl.weight_nonnegative_on_domain L v hD)
  · rw [ForbiddenBirthControl.weight_zero_at_outside_birth hSD v hD (east_south_degree_ge_two he hs)]

theorem paired_valley_weight_sum_le (L : Nat) (hL : 1 ≤ L) {S : Finset Site}
    (hc : ColumnConvex S) (hconn : FourConnected S)
    (hSD : S ⊆ ClippedDiamondGeometry.clippedDomain L) :
    (∑ v ∈ northwestPairs S, weight L (pairedValley S v)) ≤
      ∑ v ∈ northwestValleys (ClippedSquareCoordinates.centeredSites L) S, weight L v := by
  classical
  have hs : (northwestPairs S).image (pairedValley S) ⊆
      northwestValleys (ClippedSquareCoordinates.centeredSites L) S := by
    intro u hu
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    exact pairedValley_mem_actual hL hc hconn hSD hv
  rw [← Finset.sum_image (pairedValley_injOn hc)]
  exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun v hv _ => valley_weight_nonnegative hSD hv)

/-- A fully instantiated one-orientation weighted curvature estimate. No
turn count, matching, raw drift or geometric rate bound is supplied as input. -/
theorem northwestCharge_le (L : Nat) (hL : 1 ≤ L) {S : Finset Site}
    (hc : ColumnConvex S) (hconn : FourConnected S)
    (hSD : S ⊆ ClippedDiamondGeometry.clippedDomain L) :
    northwestCharge L (ClippedSquareCoordinates.centeredSites L) S ≤
      (L : Real)+2+(perimeter S : Real) := by
  have hpart : northwestPairs S ⊆ northwestCorners S := Finset.filter_subset _ _
  have heq := Finset.sum_sdiff (f := weight L) hpart
  have horphan := northwest_unpaired_weight_le L hc hconn
  have hdiff := paired_weight_difference_le L hc hconn
  have hvalley := paired_valley_weight_sum_le L hL hc hconn hSD
  rw [Finset.sum_sub_distrib] at hdiff
  unfold northwestCharge
  linarith

end MathResearchAnalysis.WeightedRawContour
