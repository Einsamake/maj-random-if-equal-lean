module
public import MathResearchAnalysis.GridPerimeterUpdate
public import MathResearchAnalysis.ProtectedColumnGeometry
public import MathResearchAnalysis.OrthogonalVacantQuadrant
set_option autoImplicit false
/-! Actual exposed-edge perimeter and interval projections for finite orthogonally convex sets. No geometric Good or probabilistic statement is assumed. -/
@[expose] public section
namespace MathResearchAnalysis.OrthogonalPerimeter
open GridCellBoundary (Site perimeter)
open InfiniteGridModel (north east south west)
open OrthogonalGridConvexity
open ProtectedColumnGeometry (transpose mem_transpose)
open scoped BigOperators

def northCells (S : Finset Site) : Finset Site := S.filter (fun v => north v ∉ S)
def southCells (S : Finset Site) : Finset Site := S.filter (fun v => south v ∉ S)
def eastCells (S : Finset Site) : Finset Site := S.filter (fun v => east v ∉ S)
def westCells (S : Finset Site) : Finset Site := S.filter (fun v => west v ∉ S)

theorem north_endpoint_exists (S : Finset Site) {x : Int} (hx : x ∈ S.image Prod.fst) :
    ∃ u ∈ northCells S, u.1 = x := by
  obtain ⟨v,hv,hvx⟩ := Finset.mem_image.mp hx
  let T := S.filter (fun w => w.1 = x)
  have hT : v ∈ T := Finset.mem_filter.mpr ⟨hv,hvx⟩
  have hne : (T.image Prod.snd).Nonempty := ⟨v.2,Finset.mem_image.mpr ⟨v,hT,rfl⟩⟩
  obtain ⟨u,hu,heq⟩ := Finset.mem_image.mp (Finset.max'_mem (T.image Prod.snd) hne)
  have huS := (Finset.mem_filter.mp hu).1
  have hux := (Finset.mem_filter.mp hu).2
  have hout : north u ∉ S := by
    intro h
    have hnt : north u ∈ T := Finset.mem_filter.mpr ⟨h,by simpa only [north] using hux⟩
    have hnimg : (north u).2 ∈ T.image Prod.snd := Finset.mem_image.mpr ⟨north u,hnt,rfl⟩
    have hbound := Finset.le_max' (T.image Prod.snd) (north u).2 hnimg
    rw [← heq] at hbound
    dsimp [north] at hbound
    omega
  exact ⟨u,Finset.mem_filter.mpr ⟨huS,hout⟩,hux⟩

theorem north_endpoint_unique {S : Finset Site} (hc : ColumnConvex S)
    {u v : Site} (hu : u ∈ northCells S) (hv : v ∈ northCells S) (hx : u.1 = v.1) : u = v := by
  obtain ⟨huS,hun⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvS,hvn⟩ := Finset.mem_filter.mp hv
  apply Prod.ext hx
  apply le_antisymm <;> by_contra h
  · apply hvn
    have hp := hc v.1 v.2 u.2 (v.2+1) hvS (by simpa only [hx] using (show (u.1,u.2) ∈ S from huS)) (by omega) (by omega)
    exact hp
  · apply hun
    have hp := hc u.1 u.2 v.2 (u.2+1) huS (by simpa only [hx] using (show (v.1,v.2) ∈ S from hvS)) (by omega) (by omega)
    exact hp

theorem northCells_card {S : Finset Site} (hc : ColumnConvex S) :
    (northCells S).card = (S.image Prod.fst).card := by
  apply Finset.card_bij (fun u _ => u.1)
  · intro u hu
    exact Finset.mem_image.mpr ⟨u,(Finset.mem_filter.mp hu).1,rfl⟩
  · intro u hu v hv hx
    exact north_endpoint_unique hc hu hv hx
  · intro x hx
    obtain ⟨u,hu,heq⟩ := north_endpoint_exists S hx
    exact ⟨u,hu,heq⟩

theorem south_endpoint_exists (S : Finset Site) {x : Int} (hx : x ∈ S.image Prod.fst) :
    ∃ u ∈ southCells S, u.1 = x := by
  obtain ⟨v,hv,hvx⟩ := Finset.mem_image.mp hx
  let T := S.filter (fun w => w.1 = x)
  have hT : v ∈ T := Finset.mem_filter.mpr ⟨hv,hvx⟩
  have hne : (T.image Prod.snd).Nonempty := ⟨v.2,Finset.mem_image.mpr ⟨v,hT,rfl⟩⟩
  obtain ⟨u,hu,heq⟩ := Finset.mem_image.mp (Finset.min'_mem (T.image Prod.snd) hne)
  have huS := (Finset.mem_filter.mp hu).1
  have hux := (Finset.mem_filter.mp hu).2
  have hout : south u ∉ S := by
    intro h
    have hnt : south u ∈ T := Finset.mem_filter.mpr ⟨h,by simpa only [south] using hux⟩
    have hnimg : (south u).2 ∈ T.image Prod.snd := Finset.mem_image.mpr ⟨south u,hnt,rfl⟩
    have hbound := Finset.min'_le (T.image Prod.snd) (south u).2 hnimg
    rw [← heq] at hbound
    dsimp [south] at hbound
    omega
  exact ⟨u,Finset.mem_filter.mpr ⟨huS,hout⟩,hux⟩

theorem south_endpoint_unique {S : Finset Site} (hc : ColumnConvex S)
    {u v : Site} (hu : u ∈ southCells S) (hv : v ∈ southCells S) (hx : u.1 = v.1) : u = v := by
  obtain ⟨huS,hun⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvS,hvn⟩ := Finset.mem_filter.mp hv
  apply Prod.ext hx
  apply le_antisymm <;> by_contra h
  · apply hun
    exact hc u.1 v.2 u.2 (u.2-1) (by simpa only [hx] using (show (v.1,v.2) ∈ S from hvS)) huS (by omega) (by omega)
  · apply hvn
    exact hc v.1 u.2 v.2 (v.2-1) (by simpa only [hx] using (show (u.1,u.2) ∈ S from huS)) hvS (by omega) (by omega)

theorem southCells_card {S : Finset Site} (hc : ColumnConvex S) :
    (southCells S).card = (S.image Prod.fst).card := by
  apply Finset.card_bij (fun u _ => u.1)
  · intro u hu
    exact Finset.mem_image.mpr ⟨u,(Finset.mem_filter.mp hu).1,rfl⟩
  · intro u hu v hv hx
    exact south_endpoint_unique hc hu hv hx
  · intro x hx
    obtain ⟨u,hu,heq⟩ := south_endpoint_exists S hx
    exact ⟨u,hu,heq⟩

theorem northCells_transpose (S : Finset Site) : northCells (transpose S) = transpose (eastCells S) := by
  ext u
  simp only [northCells,eastCells,Finset.mem_filter,mem_transpose,Prod.swap,north,east]
  exact (Finset.mem_filter (p := fun v : Site => east v ∉ S) (s := S) (a := u.swap)).symm

theorem southCells_transpose (S : Finset Site) : southCells (transpose S) = transpose (westCells S) := by
  ext u
  simp only [southCells,westCells,Finset.mem_filter,mem_transpose,Prod.swap,south,west]
  exact (Finset.mem_filter (p := fun v : Site => west v ∉ S) (s := S) (a := u.swap)).symm

theorem card_transpose (S : Finset Site) : (transpose S).card = S.card :=
  Finset.card_image_of_injective _ Prod.swap_injective

theorem transpose_image_fst (S : Finset Site) : (transpose S).image Prod.fst = S.image Prod.snd := by
  rw [transpose,Finset.image_image]
  rfl

theorem eastCells_card {S : Finset Site} (hr : RowConvex S) :
    (eastCells S).card = (S.image Prod.snd).card := by
  have h := northCells_card (ProtectedColumnGeometry.columnConvex_transpose hr)
  rw [northCells_transpose,card_transpose,transpose_image_fst] at h
  exact h

theorem westCells_card {S : Finset Site} (hr : RowConvex S) :
    (westCells S).card = (S.image Prod.snd).card := by
  have h := southCells_card (ProtectedColumnGeometry.columnConvex_transpose hr)
  rw [southCells_transpose,card_transpose,transpose_image_fst] at h
  exact h

theorem perimeter_eq_directional_cells (S : Finset Site) :
    perimeter S = (northCells S).card + (eastCells S).card +
      (southCells S).card + (westCells S).card := by
  rw [GridPerimeterUpdate.perimeter_eq_sum_exposed]
  simp only [Fin.sum_univ_four,GridCellBoundary.neighbor_north,GridCellBoundary.neighbor_east,
    GridCellBoundary.neighbor_south,GridCellBoundary.neighbor_west,Finset.sum_add_distrib]
  simp only [northCells,eastCells,southCells,westCells,Finset.card_eq_sum_ones,Finset.sum_filter]
  rfl

theorem perimeter_eq_projection_cards {S : Finset Site} (hr : RowConvex S) (hc : ColumnConvex S) :
    perimeter S = 2 * ((S.image Prod.fst).card + (S.image Prod.snd).card) := by
  rw [perimeter_eq_directional_cells,northCells_card hc,southCells_card hc,eastCells_card hr,westCells_card hr]
  omega


theorem fst_projection_interval {S : Finset Site} (hconn : FourConnected S)
    {a b x : Int} (ha : a ∈ S.image Prod.fst) (hb : b ∈ S.image Prod.fst)
    (hax : a ≤ x) (hxb : x ≤ b) : x ∈ S.image Prod.fst := by
  obtain ⟨u,hu,hua⟩ := Finset.mem_image.mp ha
  obtain ⟨v,hv,hvb⟩ := Finset.mem_image.mp hb
  by_cases h : x = b
  · exact h ▸ hb
  · obtain ⟨y,hy,_⟩ := OrthogonalVacantQuadrant.path_crosses_vertical_cut x
      (hconn u hu v hv) (by omega) (by omega)
    exact Finset.mem_image.mpr ⟨(x,y),hy,rfl⟩

theorem snd_projection_interval {S : Finset Site} (hconn : FourConnected S)
    {a b y : Int} (ha : a ∈ S.image Prod.snd) (hb : b ∈ S.image Prod.snd)
    (hay : a ≤ y) (hyb : y ≤ b) : y ∈ S.image Prod.snd := by
  obtain ⟨u,hu,hua⟩ := Finset.mem_image.mp ha
  obtain ⟨v,hv,hvb⟩ := Finset.mem_image.mp hb
  by_cases h : y = b
  · exact h ▸ hb
  · obtain ⟨x,hx,_⟩ := path_crosses_horizontal_cut y
      (hconn u hu v hv) (by omega) (by omega)
    exact Finset.mem_image.mpr ⟨(x,y),hx,rfl⟩

theorem int_finset_eq_Icc {T : Finset Int} (hne : T.Nonempty)
    (hbetween : ∀ a ∈ T, ∀ b ∈ T, ∀ x, a ≤ x → x ≤ b → x ∈ T) :
    T = Finset.Icc (T.min' hne) (T.max' hne) := by
  ext x
  constructor
  · intro hx
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le T x hx,Finset.le_max' T x hx⟩
  · intro hx
    obtain ⟨hmin,hmax⟩ := Finset.mem_Icc.mp hx
    exact hbetween _ (Finset.min'_mem T hne) _ (Finset.max'_mem T hne) x hmin hmax

theorem fst_projection_eq_Icc {S : Finset Site} (hconn : FourConnected S) (hne : S.Nonempty) :
    S.image Prod.fst = Finset.Icc ((S.image Prod.fst).min' (hne.image Prod.fst))
      ((S.image Prod.fst).max' (hne.image Prod.fst)) :=
  int_finset_eq_Icc (hne.image Prod.fst)
    (fun _ ha _ hb _ hax hxb => fst_projection_interval hconn ha hb hax hxb)

theorem snd_projection_eq_Icc {S : Finset Site} (hconn : FourConnected S) (hne : S.Nonempty) :
    S.image Prod.snd = Finset.Icc ((S.image Prod.snd).min' (hne.image Prod.snd))
      ((S.image Prod.snd).max' (hne.image Prod.snd)) :=
  int_finset_eq_Icc (hne.image Prod.snd)
    (fun _ ha _ hb _ hay hyb => snd_projection_interval hconn ha hb hay hyb)

theorem perimeter_eq_integer_spans {S : Finset Site}
    (hr : RowConvex S) (hc : ColumnConvex S) (hconn : FourConnected S) (hne : S.Nonempty) :
    perimeter S = 2 *
      ((((S.image Prod.fst).max' (hne.image Prod.fst)) + 1 -
        ((S.image Prod.fst).min' (hne.image Prod.fst))).toNat +
       (((S.image Prod.snd).max' (hne.image Prod.snd)) + 1 -
        ((S.image Prod.snd).min' (hne.image Prod.snd))).toNat) := by
  have hx := congrArg Finset.card (fst_projection_eq_Icc hconn hne)
  have hy := congrArg Finset.card (snd_projection_eq_Icc hconn hne)
  rw [Int.card_Icc] at hx hy
  rw [perimeter_eq_projection_cards hr hc,hx,hy]

end MathResearchAnalysis.OrthogonalPerimeter
