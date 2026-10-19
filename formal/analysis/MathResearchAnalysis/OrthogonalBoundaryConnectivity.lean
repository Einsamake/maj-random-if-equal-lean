module
public import MathResearchAnalysis.OrthogonalPerimeter
public import MathResearchAnalysis.OrthogonalVacantQuadrant
public import MathResearchAnalysis.GridBoundaryPermutation
set_option autoImplicit false
/-! Actual boundary connectivity from column convexity and four-neighbour connectivity. All paths consist of exposed unit-cell half-edges and true endpoint contacts; no boundary connectivity assumption is used. -/
@[expose] public section
namespace MathResearchAnalysis.OrthogonalBoundaryConnectivity
open GridCellBoundary (Site HalfEdge Direction source target boundary)
open InfiniteGridModel (north east south west)
open OrthogonalGridConvexity (RowConvex ColumnConvex FourConnected)
open OrthogonalPerimeter (northCells north_endpoint_exists north_endpoint_unique)

def Touch (e f : HalfEdge) : Prop :=
  source e = source f ∨ source e = target f ∨ target e = source f ∨ target e = target f

def Step (S : Finset Site) (e f : HalfEdge) : Prop :=
  e ∈ boundary S ∧ f ∈ boundary S ∧ Touch e f

abbrev Path (S : Finset Site) : HalfEdge → HalfEdge → Prop := Relation.ReflTransGen (Step S)

theorem touch_symm {e f : HalfEdge} (h : Touch e f) : Touch f e := by
  rcases h with h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (Or.inr h.symm))

theorem path_reverse {S : Finset Site} {e f : HalfEdge} (h : Path S e f) : Path S f e := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact (Relation.ReflTransGen.single ⟨hs.2.1,hs.1,touch_symm hs.2.2⟩).trans ih

theorem path_of_touch {S : Finset Site} {e f : HalfEdge}
    (he : e ∈ boundary S) (hf : f ∈ boundary S) (ht : Touch e f) : Path S e f :=
  Relation.ReflTransGen.single ⟨he,hf,ht⟩

theorem interval_path {S : Finset Site} (f : Int → HalfEdge) (a b : Int) (hab : a ≤ b)
    (hf : ∀ k, a ≤ k → k ≤ b → f k ∈ boundary S)
    (ht : ∀ k, a ≤ k → k < b → Touch (f k) (f (k+1))) : Path S (f a) (f b) := by
  have haux : ∀ n : Nat, a + (n : Int) ≤ b → Path S (f a) (f (a+(n : Int))) := by
    intro n
    induction n with
    | zero => intro _; simpa using (Relation.ReflTransGen.refl : Path S (f a) (f a))
    | succ n ih =>
      intro hn
      have hprev : a+(n : Int) ≤ b := by omega
      have hp := (ih hprev).trans (path_of_touch
        (hf _ (by omega) hprev) (hf _ (by omega) (by omega)) (ht _ (by omega) (by omega)))
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using hp
  have heq : a + ((b-a).toNat : Int) = b := by omega
  simpa only [heq] using haux (b-a).toNat (by omega)

theorem vertical_touch (x y : Int) (d : Direction) (hd : d = 1 ∨ d = 3) :
    Touch ((x,y),d) ((x,y+1),d) := by
  rcases hd with rfl | rfl
  · apply Or.inr ∘ Or.inr ∘ Or.inl
    apply Prod.ext <;> dsimp [source,target]
    omega
  · apply Or.inr ∘ Or.inl
    apply Prod.ext <;> dsimp [source,target]
    omega

theorem horizontal_touch (x y : Int) (d : Direction) (hd : d = 0 ∨ d = 2) :
    Touch ((x,y),d) ((x+1,y),d) := by
  rcases hd with rfl | rfl
  · apply Or.inr ∘ Or.inl
    apply Prod.ext <;> dsimp [source,target]
    omega
  · apply Or.inr ∘ Or.inr ∘ Or.inl
    apply Prod.ext <;> dsimp [source,target]
    omega

theorem vertical_run {S : Finset Site} (x a b : Int) (hab : a ≤ b) (d : Direction)
    (hd : d = 1 ∨ d = 3) (hf : ∀ y, a ≤ y → y ≤ b → ((x,y),d) ∈ boundary S) :
    Path S ((x,a),d) ((x,b),d) :=
  interval_path (fun y => ((x,y),d)) a b hab hf (fun y _ _ => vertical_touch x y d hd)

theorem horizontal_run {S : Finset Site} (a b y : Int) (hab : a ≤ b) (d : Direction)
    (hd : d = 0 ∨ d = 2) (hf : ∀ x, a ≤ x → x ≤ b → ((x,y),d) ∈ boundary S) :
    Path S ((a,y),d) ((b,y),d) :=
  interval_path (fun x => ((x,y),d)) a b hab hf (fun x _ _ => horizontal_touch x y d hd)

theorem north_occupied_le {S : Finset Site} (hc : ColumnConvex S)
    {u w : Site} (hu : u ∈ northCells S) (hw : w ∈ S) (hx : w.1 = u.1) : w.2 ≤ u.2 := by
  by_contra h
  obtain ⟨huS,hun⟩ := Finset.mem_filter.mp hu
  apply hun
  exact hc u.1 u.2 w.2 (u.2+1) huS
    (by simpa only [hx] using (show (w.1,w.2) ∈ S from hw)) (by omega) (by omega)

theorem north_adjacent_path {S : Finset Site} (hc : ColumnConvex S) (hconn : FourConnected S)
    {u v : Site} (hu : u ∈ northCells S) (hv : v ∈ northCells S) (hx : v.1 = u.1+1) :
    Path S (u,0) (v,0) := by
  have huS := (Finset.mem_filter.mp hu).1
  have hvS := (Finset.mem_filter.mp hv).1
  have heu : (u,0) ∈ boundary S := (GridCellBoundary.mem_boundary_north S u).mpr (Finset.mem_filter.mp hu)
  have hev : (v,0) ∈ boundary S := (GridCellBoundary.mem_boundary_north S v).mpr (Finset.mem_filter.mp hv)
  obtain ⟨y,hyL,hyR⟩ := OrthogonalVacantQuadrant.path_crosses_vertical_cut u.1
    (hconn u huS v hvS) (by rfl) (by omega)
  have hyu : y ≤ u.2 := north_occupied_le hc hu hyL rfl
  have hyv : y ≤ v.2 := north_occupied_le hc hv hyR (by dsimp; omega)
  rcases lt_trichotomy u.2 v.2 with hlt | heq | hgt
  · have hwest : ∀ z, u.2+1 ≤ z → z ≤ v.2 → ((v.1,z),3) ∈ boundary S := by
      intro z hza hzb
      apply (GridCellBoundary.mem_boundary_west S (v.1,z)).mpr
      constructor
      · exact hc v.1 y v.2 z (by simpa only [hx] using hyR) hvS (by omega) hzb
      · intro hw
        have hbound := north_occupied_le hc hu hw (by change v.1-1 = u.1; omega)
        change z ≤ u.2 at hbound
        omega
    have hlo := hwest (u.2+1) (by rfl) (by omega)
    have hhi := hwest v.2 (by omega) (by rfl)
    have hp0 : Path S (u,0) ((v.1,u.2+1),3) := by
      apply path_of_touch heu hlo
      apply Or.inr ∘ Or.inl
      apply Prod.ext <;> norm_num [source,target] <;> omega
    have hp1 := vertical_run v.1 (u.2+1) v.2 (by omega) 3 (Or.inr rfl) hwest
    have hp2 : Path S ((v.1,v.2),3) (v,0) := by
      apply path_of_touch hhi hev
      apply Or.inr ∘ Or.inl
      apply Prod.ext <;> norm_num [source,target]
    exact hp0.trans (hp1.trans hp2)
  · apply path_of_touch heu hev
    apply Or.inr ∘ Or.inl
    apply Prod.ext <;> norm_num [source,target] <;> omega
  · have heast : ∀ z, v.2+1 ≤ z → z ≤ u.2 → ((u.1,z),1) ∈ boundary S := by
      intro z hza hzb
      apply (GridCellBoundary.mem_boundary_east S (u.1,z)).mpr
      constructor
      · exact hc u.1 y u.2 z hyL huS (by omega) hzb
      · intro hw
        have hbound := north_occupied_le hc hv hw (by change u.1+1 = v.1; omega)
        change z ≤ v.2 at hbound
        omega
    have hlo := heast (v.2+1) (by rfl) (by omega)
    have hhi := heast u.2 (by omega) (by rfl)
    have hp0 : Path S (v,0) ((u.1,v.2+1),1) := by
      apply path_of_touch hev hlo
      apply Or.inr ∘ Or.inr ∘ Or.inl
      apply Prod.ext <;> norm_num [source,target] <;> omega
    have hp1 := vertical_run u.1 (v.2+1) u.2 (by omega) 1 (Or.inl rfl) heast
    have hp2 : Path S ((u.1,u.2),1) (u,0) := by
      apply path_of_touch hhi heu
      apply Or.inr ∘ Or.inr ∘ Or.inl
      apply Prod.ext <;> norm_num [source,target]
    exact path_reverse (hp0.trans (hp1.trans hp2))


theorem north_path_of_le {S : Finset Site} (hc : ColumnConvex S) (hconn : FourConnected S)
    {u v : Site} (hu : u ∈ northCells S) (hv : v ∈ northCells S) (hxx : u.1 ≤ v.1) :
    Path S (u,0) (v,0) := by
  have huX : u.1 ∈ S.image Prod.fst := Finset.mem_image.mpr ⟨u,(Finset.mem_filter.mp hu).1,rfl⟩
  have hvX : v.1 ∈ S.image Prod.fst := Finset.mem_image.mpr ⟨v,(Finset.mem_filter.mp hv).1,rfl⟩
  have haux : ∀ n : Nat, u.1+(n : Int) ≤ v.1 → ∀ w ∈ northCells S,
      w.1 = u.1+(n : Int) → Path S (u,0) (w,0) := by
    intro n
    induction n with
    | zero =>
      intro _ w hw hx
      have heq : u = w := north_endpoint_unique hc hu hw (by omega)
      subst w
      exact Relation.ReflTransGen.refl
    | succ n ih =>
      intro hn w hw hx
      have hxmem := OrthogonalPerimeter.fst_projection_interval hconn huX hvX
        (x := u.1+(n : Int)) (by omega) (by omega)
      obtain ⟨z,hz,hzx⟩ := north_endpoint_exists S hxmem
      exact (ih (by omega) z hz hzx).trans (north_adjacent_path hc hconn hz hw (by omega))
  have heq : u.1 + ((v.1-u.1).toNat : Int) = v.1 := by omega
  exact haux (v.1-u.1).toNat (by omega) v hv heq.symm

theorem north_path {S : Finset Site} (hc : ColumnConvex S) (hconn : FourConnected S)
    {u v : Site} (hu : u ∈ northCells S) (hv : v ∈ northCells S) : Path S (u,0) (v,0) := by
  rcases le_total u.1 v.1 with h | h
  · exact north_path_of_le hc hconn hu hv h
  · exact path_reverse (north_path_of_le hc hconn hv hu h)

def flipDirection (d : Direction) : Direction :=
  match d.val with | 0 => 2 | 1 => 1 | 2 => 0 | _ => 3

def flip (e : HalfEdge) : HalfEdge := ((e.1.1,-e.1.2),flipDirection e.2)

@[simp] theorem flip_flip (e : HalfEdge) : flip (flip e) = e := by
  rcases e with ⟨v,d⟩
  fin_cases d <;> simp [flip,flipDirection]

theorem source_flip (e : HalfEdge) : source (flip e) = ((target e).1,-(target e).2) := by
  rcases e with ⟨v,d⟩
  fin_cases d <;> apply Prod.ext <;> norm_num [source,target,flip,flipDirection] <;> omega

theorem target_flip (e : HalfEdge) : target (flip e) = ((source e).1,-(source e).2) := by
  rcases e with ⟨v,d⟩
  fin_cases d <;> apply Prod.ext <;> norm_num [source,target,flip,flipDirection] <;> omega

theorem flip_mem_boundary {S : Finset Site} {e : HalfEdge} (he : e ∈ boundary S) :
    flip e ∈ boundary (ProtectedCornerGeometry.mirror false true S) := by
  rw [GridCellBoundary.mem_boundary] at he ⊢
  rcases e with ⟨v,d⟩
  fin_cases d <;>
    simpa [flip,flipDirection,ProtectedCornerGeometry.mem_mirror,ClippedDiamondGeometry.reflect,
      GridCellBoundary.neighbor,north,east,south,west,sub_eq_add_neg,add_comm] using he

theorem touch_flip {e f : HalfEdge} (h : Touch e f) : Touch (flip e) (flip f) := by
  unfold Touch at h ⊢
  rw [source_flip,target_flip,source_flip,target_flip]
  rcases h with h | h | h | h
  · exact Or.inr (Or.inr (Or.inr (congrArg (fun p : Site => (p.1,-p.2)) h)))
  · exact Or.inr (Or.inr (Or.inl (congrArg (fun p : Site => (p.1,-p.2)) h)))
  · exact Or.inr (Or.inl (congrArg (fun p : Site => (p.1,-p.2)) h))
  · exact Or.inl (congrArg (fun p : Site => (p.1,-p.2)) h)

theorem path_flip {S : Finset Site} {e f : HalfEdge} (h : Path S e f) :
    Path (ProtectedCornerGeometry.mirror false true S) (flip e) (flip f) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail ⟨flip_mem_boundary hs.1,flip_mem_boundary hs.2.1,touch_flip hs.2.2⟩

@[simp] theorem mirror_mirror (S : Finset Site) :
    ProtectedCornerGeometry.mirror false true (ProtectedCornerGeometry.mirror false true S) = S := by
  ext u
  simp [ProtectedCornerGeometry.mem_mirror,ClippedDiamondGeometry.reflect]

theorem south_path {S : Finset Site} (hc : ColumnConvex S) (hconn : FourConnected S)
    {u v : Site} (hu : u ∈ OrthogonalPerimeter.southCells S)
    (hv : v ∈ OrthogonalPerimeter.southCells S) : Path S (u,2) (v,2) := by
  have hm : ∀ w ∈ OrthogonalPerimeter.southCells S,
      (w.1,-w.2) ∈ northCells (ProtectedCornerGeometry.mirror false true S) := by
    intro w hw
    simpa [northCells,OrthogonalPerimeter.southCells,ProtectedCornerGeometry.mem_mirror,
      ClippedDiamondGeometry.reflect,north,south,sub_eq_add_neg,add_comm] using (Finset.mem_filter.mp hw)
  have hp := north_path (ProtectedCornerGeometry.columnConvex_mirror false true hc)
    (OrthogonalVacantQuadrant.fourConnected_mirror false true hconn) (hm u hu) (hm v hv)
  simpa [flip,flipDirection] using path_flip hp


theorem south_occupied_le {S : Finset Site} (hc : ColumnConvex S)
    {u w : Site} (hu : u ∈ OrthogonalPerimeter.southCells S) (hw : w ∈ S)
    (hx : w.1 = u.1) : u.2 ≤ w.2 := by
  by_contra h
  obtain ⟨huS,hus⟩ := Finset.mem_filter.mp hu
  apply hus
  exact hc u.1 w.2 u.2 (u.2-1)
    (by simpa only [hx] using (show (w.1,w.2) ∈ S from hw)) huS (by omega) (by omega)

def sideOffset (d : Direction) : Int := if d = 1 then 1 else -1

theorem side_boundary_iff (S : Finset Site) (x y : Int) (d : Direction) (hd : d = 1 ∨ d = 3) :
    ((x,y),d) ∈ boundary S ↔ (x,y) ∈ S ∧ (x+sideOffset d,y) ∉ S := by
  rcases hd with rfl | rfl <;>
    simp [GridCellBoundary.mem_boundary,GridCellBoundary.neighbor,sideOffset,east,west,sub_eq_add_neg]

theorem side_top_touch (v : Site) (d : Direction) (hd : d = 1 ∨ d = 3) : Touch (v,d) (v,0) := by
  rcases hd with rfl | rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inl rfl)

theorem side_bottom_touch (v : Site) (d : Direction) (hd : d = 1 ∨ d = 3) : Touch (v,d) (v,2) := by
  rcases hd with rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))

theorem side_path_to_spine {S : Finset Site} (hc : ColumnConvex S)
    (v : Site) (d : Direction) (hd : d = 1 ∨ d = 3) (he : (v,d) ∈ boundary S) :
    (∃ u ∈ northCells S, Path S (v,d) (u,0)) ∨
    (∃ u ∈ OrthogonalPerimeter.southCells S, Path S (v,d) (u,2)) := by
  classical
  obtain ⟨hvS,hvn⟩ := (side_boundary_iff S v.1 v.2 d hd).mp he
  have hxmem : v.1 ∈ S.image Prod.fst := Finset.mem_image.mpr ⟨v,hvS,rfl⟩
  obtain ⟨u,hu,hux⟩ := north_endpoint_exists S hxmem
  have huS := (Finset.mem_filter.mp hu).1
  have hyu := north_occupied_le hc hu hvS hux.symm
  by_cases hupper : ∀ z, v.2 ≤ z → z ≤ u.2 → (v.1+sideOffset d,z) ∉ S
  · left
    refine ⟨u,hu,?_⟩
    have hrun : ∀ z, v.2 ≤ z → z ≤ u.2 → ((v.1,z),d) ∈ boundary S := by
      intro z hza hzb
      apply (side_boundary_iff _ _ _ _ hd).mpr
      exact ⟨hc v.1 v.2 u.2 z hvS (by simpa only [hux] using (show (u.1,u.2) ∈ S from huS)) hza hzb,hupper z hza hzb⟩
    have hp := vertical_run v.1 v.2 u.2 hyu d hd hrun
    have hn : (u,0) ∈ boundary S := (GridCellBoundary.mem_boundary_north S u).mpr (Finset.mem_filter.mp hu)
    exact hp.trans (path_of_touch (hrun _ hyu le_rfl) hn
      (by simpa only [← hux] using side_top_touch u d hd))
  · push Not at hupper
    obtain ⟨z,hzy,hzu,hz⟩ := hupper
    obtain ⟨b,hb,hbx⟩ := OrthogonalPerimeter.south_endpoint_exists S hxmem
    have hbS := (Finset.mem_filter.mp hb).1
    have hby := south_occupied_le hc hb hvS hbx.symm
    have hlower : ∀ t, t ≤ v.2 → (v.1+sideOffset d,t) ∉ S := by
      intro t hty ht
      exact hvn (hc (v.1+sideOffset d) t z v.2 ht hz hty hzy)
    right
    refine ⟨b,hb,?_⟩
    have hrun : ∀ t, b.2 ≤ t → t ≤ v.2 → ((v.1,t),d) ∈ boundary S := by
      intro t hta htb
      apply (side_boundary_iff _ _ _ _ hd).mpr
      exact ⟨hc v.1 b.2 v.2 t (by simpa only [hbx] using (show (b.1,b.2) ∈ S from hbS)) hvS hta htb,hlower t htb⟩
    have hp := path_reverse (vertical_run v.1 b.2 v.2 hby d hd hrun)
    have hs : (b,2) ∈ boundary S := (GridCellBoundary.mem_boundary_south S b).mpr (Finset.mem_filter.mp hb)
    exact hp.trans (path_of_touch (hrun _ le_rfl hby) hs
      (by simpa only [← hbx] using side_bottom_touch b d hd))

theorem spines_connected {S : Finset Site} (hc : ColumnConvex S) (hne : S.Nonempty) :
    ∃ u ∈ northCells S, ∃ b ∈ OrthogonalPerimeter.southCells S, Path S (b,2) (u,0) := by
  have hxne := hne.image Prod.fst
  let x := (S.image Prod.fst).min' hxne
  have hx : x ∈ S.image Prod.fst := Finset.min'_mem _ hxne
  obtain ⟨u,hu,hux⟩ := north_endpoint_exists S hx
  obtain ⟨b,hb,hbx⟩ := OrthogonalPerimeter.south_endpoint_exists S hx
  have huS := (Finset.mem_filter.mp hu).1
  have hbS := (Finset.mem_filter.mp hb).1
  have hbu := south_occupied_le hc hb huS (hux.trans hbx.symm)
  have hwest : ∀ y, b.2 ≤ y → y ≤ u.2 → ((x,y),3) ∈ boundary S := by
    intro y hya hyb
    apply (GridCellBoundary.mem_boundary_west S (x,y)).mpr
    constructor
    · exact hc x b.2 u.2 y (by simpa only [hbx] using (show (b.1,b.2) ∈ S from hbS)) (by simpa only [hux] using (show (u.1,u.2) ∈ S from huS)) hya hyb
    · intro hw
      have hwx : x-1 ∈ S.image Prod.fst := Finset.mem_image.mpr ⟨west (x,y),hw,rfl⟩
      have hmin := Finset.min'_le (S.image Prod.fst) (x-1) hwx
      change x ≤ x-1 at hmin
      omega
  refine ⟨u,hu,b,hb,?_⟩
  have heu : (u,0) ∈ boundary S := (GridCellBoundary.mem_boundary_north S u).mpr (Finset.mem_filter.mp hu)
  have heb : (b,2) ∈ boundary S := (GridCellBoundary.mem_boundary_south S b).mpr (Finset.mem_filter.mp hb)
  have hp0 : Path S (b,2) ((x,b.2),3) := by
    apply path_of_touch heb (hwest _ le_rfl hbu)
    apply Or.inr ∘ Or.inl
    apply Prod.ext <;> norm_num [source,target]
    omega
  have hp1 := vertical_run x b.2 u.2 hbu 3 (Or.inr rfl) hwest
  have hp2 : Path S ((x,u.2),3) (u,0) := by
    apply path_of_touch (hwest _ hbu le_rfl) heu
    apply Or.inr ∘ Or.inl
    apply Prod.ext <;> norm_num [source,target]
    omega
  exact hp0.trans (hp1.trans hp2)

theorem boundary_path_between {S : Finset Site} (hc : ColumnConvex S) (hconn : FourConnected S)
    {e f : HalfEdge} (he : e ∈ boundary S) (hf : f ∈ boundary S) : Path S e f := by
  have hne : S.Nonempty := ⟨e.1,GridCellBoundary.boundary_owner_mem he⟩
  obtain ⟨u,hu,b,hb,hbu⟩ := spines_connected hc hne
  have hconnect : ∀ g ∈ boundary S, Path S g (u,0) := by
    rintro ⟨v,d⟩ hg
    fin_cases d
    · exact north_path hc hconn (Finset.mem_filter.mpr ((GridCellBoundary.mem_boundary_north S v).mp hg)) hu
    · rcases side_path_to_spine hc v 1 (Or.inl rfl) hg with ⟨w,hw,hp⟩ | ⟨w,hw,hp⟩
      · exact hp.trans (north_path hc hconn hw hu)
      · exact hp.trans ((south_path hc hconn hw hb).trans hbu)
    · exact (south_path hc hconn (Finset.mem_filter.mpr ((GridCellBoundary.mem_boundary_south S v).mp hg)) hb).trans hbu
    · rcases side_path_to_spine hc v 3 (Or.inr rfl) hg with ⟨w,hw,hp⟩ | ⟨w,hw,hp⟩
      · exact hp.trans (north_path hc hconn hw hu)
      · exact hp.trans ((south_path hc hconn hw hb).trans hbu)
  exact (hconnect e he).trans (path_reverse (hconnect f hf))

end MathResearchAnalysis.OrthogonalBoundaryConnectivity
