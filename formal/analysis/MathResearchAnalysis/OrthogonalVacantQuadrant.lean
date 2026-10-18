module
public import MathResearchAnalysis.ProtectedCornerGeometry
public import MathResearchAnalysis.ProtectedColumnGeometry
set_option autoImplicit false
/-! Actual four-neighbour path separation: a vacant site of a finite connected orthogonally convex set has an entirely vacant strict coordinate quadrant. No protected domain or probability bound is assumed. -/
@[expose] public section
namespace MathResearchAnalysis.OrthogonalVacantQuadrant
open GridCellBoundary (Site)
open InfiniteGridModel (north east south west)
open GridMajorityPeeling (neighbors4 mem_neighbors4)
open OrthogonalGridConvexity
open ClippedDiamondGeometry (reflect)
open ProtectedCornerGeometry (mirror mem_mirror)

theorem neighbors_reflect (horizontal vertical : Bool) {v u : Site}
    (h : u ∈ neighbors4 v) : reflect horizontal vertical u ∈ neighbors4 (reflect horizontal vertical v) := by
  rcases (mem_neighbors4 v u).mp h with rfl | rfl | rfl | rfl
  all_goals cases horizontal <;> cases vertical <;>
    simp [mem_neighbors4,reflect,north,east,south,west,sub_eq_add_neg,add_comm]

theorem fourConnected_mirror (horizontal vertical : Bool) {S : Finset Site}
    (hconn : FourConnected S) : FourConnected (mirror horizontal vertical S) := by
  have hm : ∀ u ∈ S, reflect horizontal vertical u ∈ mirror horizontal vertical S := by
    intro u hu
    exact Finset.mem_image.mpr ⟨u,hu,rfl⟩
  have hstep : ∀ u v, InternalStep S u v →
      Path (mirror horizontal vertical S) (reflect horizontal vertical u) (reflect horizontal vertical v) := by
    intro u v huv
    exact Relation.ReflTransGen.single ⟨hm u huv.1,hm v huv.2.1,neighbors_reflect _ _ huv.2.2⟩
  intro a ha b hb
  have hp := hconn _ ((mem_mirror _ _ _ _).mp ha) _ ((mem_mirror _ _ _ _).mp hb)
  have hpath : Path (mirror horizontal vertical S)
      (reflect horizontal vertical (reflect horizontal vertical a))
      (reflect horizontal vertical (reflect horizontal vertical b)) :=
    Relation.ReflTransGen.lift' (reflect horizontal vertical) hstep _ _ hp
  cases horizontal <;> cases vertical <;> simpa [reflect] using hpath

theorem neighbors_swap {v u : Site} (h : u ∈ neighbors4 v) : u.swap ∈ neighbors4 v.swap := by
  rcases (mem_neighbors4 v u).mp h with rfl | rfl | rfl | rfl
  all_goals simp [mem_neighbors4,north,east,south,west,Prod.swap]

theorem path_swap {S : Finset Site} {u v : Site} (hp : Path S u v) :
    Path (ProtectedColumnGeometry.transpose S) u.swap v.swap := by
  have hstep : ∀ a b, InternalStep S a b →
      Path (ProtectedColumnGeometry.transpose S) a.swap b.swap := by
    intro a b hab
    exact Relation.ReflTransGen.single
      ⟨Finset.mem_image.mpr ⟨a,hab.1,rfl⟩,Finset.mem_image.mpr ⟨b,hab.2.1,rfl⟩,
        neighbors_swap hab.2.2⟩
  exact Relation.ReflTransGen.lift' Prod.swap hstep u v hp

theorem path_crosses_vertical_cut {S : Finset Site} {u v : Site} (x : Int)
    (hp : Path S u v) (hu : u.1 ≤ x) (hv : x < v.1) :
    ∃ y, (x,y) ∈ S ∧ (x+1,y) ∈ S := by
  obtain ⟨y,hy,hy1⟩ := path_crosses_horizontal_cut x (path_swap hp) hu hv
  exact ⟨y,(ProtectedColumnGeometry.mem_transpose S _).mp hy,
    (ProtectedColumnGeometry.mem_transpose S _).mp hy1⟩

/-- Occupied right/upper axis witnesses prevent any occupied point in the
opposite strict quadrant of a vacant site. The argument uses actual paths. -/
theorem southwest_empty {S : Finset Site} {v : Site} {xr yu : Int}
    (hr : RowConvex S) (hc : ColumnConvex S) (hconn : FourConnected S) (hv : v ∉ S)
    (hR : (xr,v.2) ∈ S) (hxR : v.1 < xr)
    (hU : (v.1,yu) ∈ S) (hyU : v.2 < yu) :
    ∀ u ∈ S, ¬ (u.1 < v.1 ∧ u.2 < v.2) := by
  have hrow : ∀ x ≤ v.1, (x,v.2) ∉ S := by
    intro x hx hh
    exact hv (hr x xr v.1 v.2 hh hR hx (by omega))
  have hcol : ∀ y ≤ v.2, (v.1,y) ∉ S := by
    intro y hy hh
    exact hv (hc v.1 y yu v.2 hh hU hy (by omega))
  have hstep : ∀ a b, InternalStep S a b →
      a.1 < v.1 ∧ a.2 < v.2 → b.1 < v.1 ∧ b.2 < v.2 := by
    intro a b hab ha
    rcases (mem_neighbors4 a b).mp hab.2.2 with rfl | rfl | rfl | rfl
    · refine ⟨ha.1,?_⟩
      change a.2+1 < v.2
      by_contra h
      have hy : a.2+1 = v.2 := by omega
      exact hrow a.1 (by omega) (by simpa only [north,hy] using hab.2.1)
    · refine ⟨?_,ha.2⟩
      change a.1+1 < v.1
      by_contra h
      have hx : a.1+1 = v.1 := by omega
      exact hcol a.2 (by omega) (by simpa only [east,hx] using hab.2.1)
    · change a.1 < v.1 ∧ a.2-1 < v.2
      omega
    · change a.1-1 < v.1 ∧ a.2 < v.2
      omega
  intro u hu hq
  have hp := hconn u hu (xr,v.2) hR
  have hpreserve : ∀ {a b : Site}, Path S a b →
      a.1 < v.1 ∧ a.2 < v.2 → b.1 < v.1 ∧ b.2 < v.2 := by
    intro a b hp
    induction hp with
    | refl => exact id
    | tail _ hs ih => intro h; exact hstep _ _ hs (ih h)
  have hbad := (hpreserve hp hq).2
  exact (lt_irrefl v.2) hbad


theorem empty_quadrant_of_axis_witnesses {S : Finset Site} {v : Site}
    (hr : RowConvex S) (hc : ColumnConvex S) (hconn : FourConnected S) (hv : v ∉ S)
    (hrow : ∃ x : Int, (x,v.2) ∈ S) (hcol : ∃ y : Int, (v.1,y) ∈ S) :
    ∃ horizontal vertical : Bool, ∀ u ∈ S,
      ¬ ((reflect horizontal vertical u).1 < (reflect horizontal vertical v).1 ∧
        (reflect horizontal vertical u).2 < (reflect horizontal vertical v).2) := by
  obtain ⟨xr,hR⟩ := hrow
  obtain ⟨yu,hU⟩ := hcol
  have hxr : xr ≠ v.1 := by intro h; exact hv (by simpa only [h,Prod.eta] using hR)
  have hyu : yu ≠ v.2 := by intro h; exact hv (by simpa only [h,Prod.eta] using hU)
  have hhor : ∃ horizontal : Bool,
      (if horizontal then -v.1 else v.1) < (if horizontal then -xr else xr) := by
    by_cases h : v.1 < xr
    · exact ⟨false,h⟩
    · exact ⟨true,by dsimp; omega⟩
  have hver : ∃ vertical : Bool,
      (if vertical then -v.2 else v.2) < (if vertical then -yu else yu) := by
    by_cases h : v.2 < yu
    · exact ⟨false,h⟩
    · exact ⟨true,by dsimp; omega⟩
  obtain ⟨horizontal,hx⟩ := hhor
  obtain ⟨vertical,hy⟩ := hver
  have hvm : reflect horizontal vertical v ∉ mirror horizontal vertical S := by
    intro h
    have h' := (mem_mirror _ _ _ _).mp h
    cases horizontal <;> cases vertical <;> exact hv (by simpa [reflect] using h')
  have hRm : reflect horizontal vertical (xr,v.2) ∈ mirror horizontal vertical S :=
    Finset.mem_image.mpr ⟨_,hR,rfl⟩
  have hUm : reflect horizontal vertical (v.1,yu) ∈ mirror horizontal vertical S :=
    Finset.mem_image.mpr ⟨_,hU,rfl⟩
  have hm := southwest_empty (ProtectedCornerGeometry.rowConvex_mirror horizontal vertical hr)
    (ProtectedCornerGeometry.columnConvex_mirror horizontal vertical hc)
    (fourConnected_mirror horizontal vertical hconn) hvm hRm hx hUm hy
  refine ⟨horizontal,vertical,?_⟩
  intro u hu
  exact hm _ (Finset.mem_image.mpr ⟨u,hu,rfl⟩)

/-- Every vacant site of a connected orthogonally convex finite set has a whole
strict coordinate quadrant disjoint from the set. No protected domain is assumed. -/
theorem exists_empty_quadrant {S : Finset Site} {v : Site}
    (hr : RowConvex S) (hc : ColumnConvex S) (hconn : FourConnected S) (hv : v ∉ S) :
    ∃ horizontal vertical : Bool, ∀ u ∈ S,
      ¬ ((reflect horizontal vertical u).1 < (reflect horizontal vertical v).1 ∧
        (reflect horizontal vertical u).2 < (reflect horizontal vertical v).2) := by
  by_cases hrow : ∃ x : Int, (x,v.2) ∈ S
  · by_cases hcol : ∃ y : Int, (v.1,y) ∈ S
    · exact empty_quadrant_of_axis_witnesses hr hc hconn hv hrow hcol
    · by_cases hleft : ∃ u ∈ S, u.1 < v.1
      · obtain ⟨u,hu,huv⟩ := hleft
        have hall : ∀ w ∈ S, w.1 < v.1 := by
          intro w hw
          by_contra h
          obtain ⟨y,_,hy⟩ := path_crosses_vertical_cut (v.1-1)
            (hconn u hu w hw) (by omega) (by omega)
          exact hcol ⟨y,by simpa using hy⟩
        refine ⟨true,false,?_⟩
        intro w hw hq
        have h := hall w hw
        dsimp [reflect] at hq
        omega
      · refine ⟨false,false,?_⟩
        intro w hw hq
        exact hleft ⟨w,hw,hq.1⟩
  · by_cases hbelow : ∃ u ∈ S, u.2 < v.2
    · obtain ⟨u,hu,huv⟩ := hbelow
      have hall : ∀ w ∈ S, w.2 < v.2 := by
        intro w hw
        by_contra h
        obtain ⟨x,_,hx⟩ := path_crosses_horizontal_cut (v.2-1)
          (hconn u hu w hw) (by omega) (by omega)
        exact hrow ⟨x,by simpa using hx⟩
      refine ⟨false,true,?_⟩
      intro w hw hq
      have h := hall w hw
      dsimp [reflect] at hq
      omega
    · refine ⟨false,false,?_⟩
      intro w hw hq
      exact hbelow ⟨w,hw,hq.2⟩

end MathResearchAnalysis.OrthogonalVacantQuadrant
