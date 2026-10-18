module
public import MathResearchAnalysis.ConvexCleanupUpdate
public import MathResearchAnalysis.ClippedProtectedGeometry
set_option autoImplicit false
@[expose] public section
namespace MathResearchAnalysis.ProtectedCornerGeometry
open GridCellBoundary (Site)
open InfiniteGridModel (north east south west)
open OrthogonalGridConvexity
open ClippedProtectedGeometry (innerDiamond mem_innerDiamond norm1)

/-- A protected orthogonally convex corner cannot separate its two adjacent neighbours.
This is a deterministic statement about the actual domains, with no probability input. -/
theorem northeast_diagonal {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} {v : Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hv : v ∈ S) (hn : north v ∈ S) (he : east v ∈ S)
    (hs : south v ∉ S) (hw : west v ∉ S)
    (hD : innerDiamond L ⊆ S) (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L) :
    north (east v) ∈ S := by
  by_contra hdiag
  rcases v with ⟨x,y⟩
  have hLz : 2 ≤ (L : Int) := by exact_mod_cast hL
  have hxp : 0 < x → 9 * (L : Int) < 10 * |y| := by
    intro hx
    by_contra h
    have ha : (0,y) ∈ S := hD ((mem_innerDiamond L _).mpr (by simp only [norm1,abs_zero,zero_add]; omega))
    exact hw (hr 0 x (x-1) y ha hv (by omega) (by omega))
  have hyp : 0 < y → 9 * (L : Int) < 10 * |x| := by
    intro hy
    by_contra h
    have ha : (x,0) ∈ S := hD ((mem_innerDiamond L _).mpr (by simp only [norm1,abs_zero,add_zero]; omega))
    exact hs (hc x 0 y (y-1) ha hv (by omega) (by omega))
  have hxn : x < 0 → 9 * (L : Int) < 10 * |y+1| := by
    intro hx
    by_contra h
    have ha : (0,y+1) ∈ S := hD ((mem_innerDiamond L _).mpr (by simp only [norm1,abs_zero,zero_add]; omega))
    exact hdiag (hr x 0 (x+1) (y+1) hn ha (by omega) (by omega))
  have hyn : y < 0 → 9 * (L : Int) < 10 * |x+1| := by
    intro hy
    by_contra h
    have ha : (x+1,0) ∈ S := hD ((mem_innerDiamond L _).mpr (by simp only [norm1,abs_zero,add_zero]; omega))
    exact hdiag (hc (x+1) y 0 (y+1) he ha (by omega) (by omega))
  have hbn := ((ClippedDiamondGeometry.mem_clippedDomain L _).mp (hclip hn)).2.2
  have hbe := ((ClippedDiamondGeometry.mem_clippedDomain L _).mp (hclip he)).2.2
  change |x| + |y+1| ≤ (L : Int)+1 at hbn
  change |x+1| + |y| ≤ (L : Int)+1 at hbe
  rcases lt_trichotomy x 0 with hx | hx | hx <;>
    rcases lt_trichotomy y 0 with hy | hy | hy
  · have a := hxn hx
    have b := hyn hy
    rw [abs_of_nonpos (by omega : y+1 ≤ 0)] at a
    rw [abs_of_nonpos (by omega : x+1 ≤ 0)] at b
    rw [abs_of_neg hx,abs_of_nonpos (by omega : y+1 ≤ 0)] at hbn
    omega
  · have a := hxn hx
    simp only [hy,zero_add,abs_one] at a
    omega
  · have a := hxn hx
    have b := hyp hy
    rw [abs_of_pos (by omega : 0 < y+1)] at a
    rw [abs_of_neg hx] at b hbn
    rw [abs_of_pos (by omega : 0 < y+1)] at hbn
    omega
  · have a := hyn hy
    simp only [hx,zero_add,abs_one] at a
    omega
  · have ha : (-1,0) ∈ S := hD ((mem_innerDiamond L _).mpr (by simp [norm1]; omega))
    exact hw (by simpa only [west,hx,hy,zero_sub] using ha)
  · have a := hyp hy
    simp only [hx,abs_zero] at a
    omega
  · have a := hxp hx
    have b := hyn hy
    rw [abs_of_neg hy] at a hbe
    rw [abs_of_pos (by omega : 0 < x+1)] at b hbe
    omega
  · have a := hxp hx
    simp only [hy,abs_zero] at a
    omega
  · have a := hxp hx
    have b := hyp hy
    rw [abs_of_pos hy] at a
    rw [abs_of_pos hx] at b hbn
    rw [abs_of_pos (by omega : 0 < y+1)] at hbn
    omega


open ClippedDiamondGeometry (reflect)

def mirror (horizontal vertical : Bool) (S : Finset Site) : Finset Site :=
  S.image (reflect horizontal vertical)

@[simp] theorem mem_mirror (horizontal vertical : Bool) (S : Finset Site) (u : Site) :
    u ∈ mirror horizontal vertical S ↔ reflect horizontal vertical u ∈ S := by
  simp only [mirror,Finset.mem_image]
  constructor
  · rintro ⟨v,hv,rfl⟩
    cases horizontal <;> cases vertical <;> simpa [reflect] using hv
  · intro hu
    exact ⟨reflect horizontal vertical u,hu,ClippedDiamondGeometry.reflect_involutive _ _ _⟩

theorem rowConvex_mirror (horizontal vertical : Bool) {S : Finset Site} (hr : RowConvex S) :
    RowConvex (mirror horizontal vertical S) := by
  intro a b x y ha hb hax hxb
  apply (mem_mirror _ _ _ _).mpr
  have ha := (mem_mirror _ _ _ _).mp ha
  have hb := (mem_mirror _ _ _ _).mp hb
  cases horizontal <;> cases vertical <;> dsimp [reflect] at ha hb ⊢
  all_goals first
    | exact hr a b x _ ha hb hax hxb
    | exact hr (-b) (-a) (-x) _ hb ha (by omega) (by omega)

theorem columnConvex_mirror (horizontal vertical : Bool) {S : Finset Site} (hc : ColumnConvex S) :
    ColumnConvex (mirror horizontal vertical S) := by
  intro x a b y ha hb hay hyb
  apply (mem_mirror _ _ _ _).mpr
  have ha := (mem_mirror _ _ _ _).mp ha
  have hb := (mem_mirror _ _ _ _).mp hb
  cases horizontal <;> cases vertical <;> dsimp [reflect] at ha hb ⊢
  all_goals first
    | exact hc _ a b y ha hb hay hyb
    | exact hc _ (-b) (-a) (-y) hb ha (by omega) (by omega)

theorem innerDiamond_reflect_iff (L : Nat) (horizontal vertical : Bool) (u : Site) :
    reflect horizontal vertical u ∈ innerDiamond L ↔ u ∈ innerDiamond L := by
  cases horizontal <;> cases vertical <;> simp [mem_innerDiamond,norm1,reflect]

theorem protected_mirror (L : Nat) (horizontal vertical : Bool) {S : Finset Site}
    (hD : innerDiamond L ⊆ S) (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L) :
    innerDiamond L ⊆ mirror horizontal vertical S ∧
      mirror horizontal vertical S ⊆ ClippedDiamondGeometry.clippedDomain L := by
  constructor
  · intro u hu
    exact (mem_mirror _ _ _ _).mpr (hD ((innerDiamond_reflect_iff _ _ _ _).mpr hu))
  · intro u hu
    have h := hclip ((mem_mirror _ _ _ _).mp hu)
    rw [ClippedDiamondGeometry.mem_clippedDomain,
      ClippedDiamondGeometry.clipped_reflect_iff] at h
    exact (ClippedDiamondGeometry.mem_clippedDomain _ _).mpr h

theorem northwest_diagonal {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} {v : Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hv : v ∈ S) (hn : north v ∈ S) (hw : west v ∈ S)
    (hs : south v ∉ S) (he : east v ∉ S)
    (hD : innerDiamond L ⊆ S) (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L) :
    north (west v) ∈ S := by
  have hp := protected_mirror L true false hD hclip
  have hh := northeast_diagonal (S := mirror true false S) (v := reflect true false v) hL
    (rowConvex_mirror true false hr) (columnConvex_mirror true false hc)
  simp [mem_mirror,reflect,north,east,south,west,sub_eq_add_neg,add_comm] at hh
  have hout := hh (by simpa [north,east,south,west,sub_eq_add_neg,add_comm] using hv) (by simpa [north,east,south,west,sub_eq_add_neg,add_comm] using hn) (by simpa [north,east,south,west,sub_eq_add_neg,add_comm] using hw) (by simpa [north,east,south,west,sub_eq_add_neg,add_comm] using hs) (by simpa [north,east,south,west,sub_eq_add_neg,add_comm] using he) hp.1 hp.2
  simpa [north,east,south,west,sub_eq_add_neg,add_comm] using hout

theorem southeast_diagonal {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} {v : Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hv : v ∈ S) (hs : south v ∈ S) (he : east v ∈ S)
    (hn : north v ∉ S) (hw : west v ∉ S)
    (hD : innerDiamond L ⊆ S) (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L) :
    south (east v) ∈ S := by
  have hp := protected_mirror L false true hD hclip
  have hh := northeast_diagonal (S := mirror false true S) (v := reflect false true v) hL
    (rowConvex_mirror false true hr) (columnConvex_mirror false true hc)
  simp [mem_mirror,reflect,north,east,south,west,sub_eq_add_neg,add_comm] at hh
  have hout := hh (by simpa [north,east,south,west,sub_eq_add_neg,add_comm] using hv) (by simpa [north,east,south,west,sub_eq_add_neg,add_comm] using hs) (by simpa [north,east,south,west,sub_eq_add_neg,add_comm] using he) (by simpa [north,east,south,west,sub_eq_add_neg,add_comm] using hn) (by simpa [north,east,south,west,sub_eq_add_neg,add_comm] using hw) hp.1 hp.2
  simpa [north,east,south,west,sub_eq_add_neg,add_comm] using hout

theorem southwest_diagonal {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} {v : Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hv : v ∈ S) (hs : south v ∈ S) (hw : west v ∈ S)
    (hn : north v ∉ S) (he : east v ∉ S)
    (hD : innerDiamond L ⊆ S) (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L) :
    south (west v) ∈ S := by
  have hp := protected_mirror L true true hD hclip
  have hh := northeast_diagonal (S := mirror true true S) (v := reflect true true v) hL
    (rowConvex_mirror true true hr) (columnConvex_mirror true true hc)
  simp [mem_mirror,reflect,north,east,south,west,sub_eq_add_neg,add_comm] at hh
  have hout := hh (by simpa [north,east,south,west,sub_eq_add_neg,add_comm] using hv) (by simpa [north,east,south,west,sub_eq_add_neg,add_comm] using hs) (by simpa [north,east,south,west,sub_eq_add_neg,add_comm] using hw) (by simpa [north,east,south,west,sub_eq_add_neg,add_comm] using hn) (by simpa [north,east,south,west,sub_eq_add_neg,add_comm] using he) hp.1 hp.2
  simpa [north,east,south,west,sub_eq_add_neg,add_comm] using hout

end MathResearchAnalysis.ProtectedCornerGeometry
#print axioms MathResearchAnalysis.ProtectedCornerGeometry.northeast_diagonal
#print axioms MathResearchAnalysis.ProtectedCornerGeometry.mirror
#print axioms MathResearchAnalysis.ProtectedCornerGeometry.mem_mirror
#print axioms MathResearchAnalysis.ProtectedCornerGeometry.rowConvex_mirror
#print axioms MathResearchAnalysis.ProtectedCornerGeometry.columnConvex_mirror
#print axioms MathResearchAnalysis.ProtectedCornerGeometry.innerDiamond_reflect_iff
#print axioms MathResearchAnalysis.ProtectedCornerGeometry.protected_mirror
#print axioms MathResearchAnalysis.ProtectedCornerGeometry.northwest_diagonal
#print axioms MathResearchAnalysis.ProtectedCornerGeometry.southeast_diagonal
#print axioms MathResearchAnalysis.ProtectedCornerGeometry.southwest_diagonal
