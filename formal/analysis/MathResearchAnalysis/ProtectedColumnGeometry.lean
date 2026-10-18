module
public import MathResearchAnalysis.ConvexLocalUpdate
public import MathResearchAnalysis.ClippedProtectedGeometry
public import MathResearchAnalysis.ConvexCleanupUpdate
set_option autoImplicit false

/-! Actual protected-domain geometry: exclusion of opposite degree-two neighbours, coordinate transport, and preservation of interval convexity under corner erasure. This does not assert connectivity or the geometric Good invariant. -/
@[expose] public section
namespace MathResearchAnalysis.ProtectedColumnGeometry
open GridCellBoundary (Site)
open InfiniteGridModel (north south)
open OrthogonalGridConvexity
open ClippedProtectedGeometry (innerDiamond mem_innerDiamond norm1)

theorem column_singleton_of_missing_vertical {S : Finset Site} {v u : Site}
    (hc : ColumnConvex S) (hv : v ∈ S) (hn : north v ∉ S) (hs : south v ∉ S)
    (hu : u ∈ S) (hx : u.1 = v.1) : u.2 = v.2 := by
  rcases v with ⟨vx,vy⟩
  rcases u with ⟨ux,uy⟩
  dsimp at hx ⊢
  subst ux
  apply le_antisymm
  · by_contra h
    exact hn (hc vx vy uy (vy+1) hv hu (by omega) (by omega))
  · by_contra h
    exact hs (hc vx uy vy (vy-1) hu hv (by omega) (by omega))

theorem protected_singleton_column_bound (L : Nat) {S : Finset Site} {v : Site}
    (hc : ColumnConvex S) (hv : v ∈ S) (hn : north v ∉ S) (hs : south v ∉ S)
    (hD : innerDiamond L ⊆ S) : 9 * (L : Int) < 10 * (|v.1| + 1) := by
  by_contra h
  have hle : 10 * (|v.1| + 1) ≤ 9 * (L : Int) := by omega
  have hp : (v.1,1) ∈ innerDiamond L :=
    (mem_innerDiamond L _).mpr (by simpa [norm1] using hle)
  have hm : (v.1,-1) ∈ innerDiamond L :=
    (mem_innerDiamond L _).mpr (by simpa [norm1] using hle)
  have h1 := column_singleton_of_missing_vertical hc hv hn hs (hD hp) rfl
  have h2 := column_singleton_of_missing_vertical hc hv hn hs (hD hm) rfl
  dsimp at h1 h2
  omega

theorem outward_row_axis_in_innerDiamond {L : Nat} (hL : 2 ≤ L) {v u : Site}
    (hv : 0 < v.1) (hu : v.1 < u.1)
    (hcol : 9 * (L : Int) < 10 * (|v.1| + 1))
    (hclip : u ∈ ClippedDiamondGeometry.clippedDomain L) : (0,u.2) ∈ innerDiamond L := by
  have hLz : 2 ≤ (L : Int) := by exact_mod_cast hL
  have hup : 0 < u.1 := by omega
  have hc := ((ClippedDiamondGeometry.mem_clippedDomain L u).mp hclip).2.2
  rw [abs_of_pos hv] at hcol
  rw [abs_of_pos hup] at hc
  apply (mem_innerDiamond L _).mpr
  simp only [norm1, abs_zero, zero_add]
  omega
theorem outward_occupied_same_row {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} {v u : Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hvS : v ∈ S) (hn : north v ∉ S) (hs : south v ∉ S)
    (hD : innerDiamond L ⊆ S) (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    (hv : 0 < v.1) (hu : v.1 < u.1) (huS : u ∈ S) : u.2 = v.2 := by
  have hb := protected_singleton_column_bound L hc hvS hn hs hD
  have ha := hD (outward_row_axis_in_innerDiamond hL hv hu hb (hclip huS))
  have hpoint : (v.1,u.2) ∈ S := hr 0 u.1 v.1 u.2 ha huS (by omega) (by omega)
  exact column_singleton_of_missing_vertical (u := (v.1,u.2)) hc hvS hn hs hpoint rfl
theorem no_east_on_positive_singleton_column {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} {v : Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hst : DropletModifiedWord.Stable S) (hvS : v ∈ S)
    (hn : north v ∉ S) (hs : south v ∉ S)
    (hD : innerDiamond L ⊆ S) (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    (hv : 0 < v.1) : InfiniteGridModel.east v ∉ S := by
  intro he
  have hne : (S.image Prod.fst).Nonempty :=
    ⟨(InfiniteGridModel.east v).1,Finset.mem_image.mpr ⟨_,he,rfl⟩⟩
  obtain ⟨u,hu,heq⟩ := Finset.mem_image.mp (Finset.max'_mem (S.image Prod.fst) hne)
  have hmax : ∀ w ∈ S, w.1 ≤ u.1 := by
    intro w hw
    have h := Finset.le_max' (S.image Prod.fst) w.1 (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
    rwa [← heq] at h
  have hux : v.1 < u.1 := by
    have h := hmax _ he
    change v.1+1 ≤ u.1 at h
    omega
  have huy := outward_occupied_same_row hL hr hc hvS hn hs hD hclip hv hux hu
  have hnu : north u ∉ S := by
    intro h
    have hy := outward_occupied_same_row (u := north u) hL hr hc hvS hn hs hD hclip hv hux h
    change u.2+1 = v.2 at hy
    omega
  have hsu : south u ∉ S := by
    intro h
    have hy := outward_occupied_same_row (u := south u) hL hr hc hvS hn hs hD hclip hv hux h
    change u.2-1 = v.2 at hy
    omega
  have heu : InfiniteGridModel.east u ∉ S := by
    intro h
    have h' := hmax _ h
    change u.1+1 ≤ u.1 at h'
    omega
  have hd : 2 ≤ GridMajorityPeeling.degree4 S u :=
    (FiniteMajorityPeeling.stable_iff GridMajorityPeeling.neighbors4 S).mp hst u hu
  have hn' : GridMajorityPeeling.state S (north u) = false := by simp [GridMajorityPeeling.state,hnu]
  have hs' : GridMajorityPeeling.state S (south u) = false := by simp [GridMajorityPeeling.state,hsu]
  have he' : GridMajorityPeeling.state S (InfiniteGridModel.east u) = false := by simp [GridMajorityPeeling.state,heu]
  rw [GridMajorityPeeling.degree4_eq_four_inputs,hn',he',hs'] at hd
  simp only [Bool.toNat_false,zero_add] at hd
  cases hw : GridMajorityPeeling.state S (InfiniteGridModel.west u)
  all_goals simp only [hw,Bool.toNat_false,Bool.toNat_true] at hd
  all_goals omega
theorem no_singleton_column_on_axis {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} {v : Site} (hc : ColumnConvex S) (hvS : v ∈ S)
    (hn : north v ∉ S) (hs : south v ∉ S) (hD : innerDiamond L ⊆ S)
    (hx : v.1 = 0) : False := by
  have hb := protected_singleton_column_bound L hc hvS hn hs hD
  rw [hx,abs_zero,zero_add] at hb
  have hLz : 2 ≤ (L : Int) := by exact_mod_cast hL
  omega
theorem no_horizontal_opposites_at_positive_x {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} {v : Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hst : DropletModifiedWord.Stable S) (hvS : v ∈ S)
    (hD : innerDiamond L ⊆ S) (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    (hv : 0 < v.1) (hd : GridMajorityPeeling.degree4 S v = 2) :
    ¬ (InfiniteGridModel.east v ∈ S ∧ InfiniteGridModel.west v ∈ S) := by
  rintro ⟨he,hw⟩
  have he' : GridMajorityPeeling.state S (InfiniteGridModel.east v) = true := by simp [GridMajorityPeeling.state,he]
  have hw' : GridMajorityPeeling.state S (InfiniteGridModel.west v) = true := by simp [GridMajorityPeeling.state,hw]
  rw [GridMajorityPeeling.degree4_eq_four_inputs,he',hw'] at hd
  simp only [Bool.toNat_true] at hd
  have hn : north v ∉ S := by
    intro h
    have h' : GridMajorityPeeling.state S (north v) = true := by simp [GridMajorityPeeling.state,h]
    rw [h'] at hd
    simp only [Bool.toNat_true] at hd
    omega
  have hs : south v ∉ S := by
    intro h
    have h' : GridMajorityPeeling.state S (south v) = true := by simp [GridMajorityPeeling.state,h]
    rw [h'] at hd
    simp only [Bool.toNat_true] at hd
    omega
  exact no_east_on_positive_singleton_column hL hr hc hst hvS hn hs hD hclip hv he
theorem outward_row_axis_in_innerDiamond_negative {L : Nat} (hL : 2 ≤ L) {v u : Site}
    (hv : v.1 < 0) (hu : u.1 < v.1)
    (hcol : 9 * (L : Int) < 10 * (|v.1| + 1))
    (hclip : u ∈ ClippedDiamondGeometry.clippedDomain L) : (0,u.2) ∈ innerDiamond L := by
  have hLz : 2 ≤ (L : Int) := by exact_mod_cast hL
  have hup : u.1 < 0 := by omega
  have hc := ((ClippedDiamondGeometry.mem_clippedDomain L u).mp hclip).2.2
  rw [abs_of_neg hv] at hcol
  rw [abs_of_neg hup] at hc
  apply (mem_innerDiamond L _).mpr
  simp only [norm1,abs_zero,zero_add]
  omega

theorem outward_occupied_same_row_negative {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} {v u : Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hvS : v ∈ S) (hn : north v ∉ S) (hs : south v ∉ S)
    (hD : innerDiamond L ⊆ S) (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    (hv : v.1 < 0) (hu : u.1 < v.1) (huS : u ∈ S) : u.2 = v.2 := by
  have hb := protected_singleton_column_bound L hc hvS hn hs hD
  have ha := hD (outward_row_axis_in_innerDiamond_negative hL hv hu hb (hclip huS))
  have hpoint : (v.1,u.2) ∈ S := hr u.1 0 v.1 u.2 huS ha (by omega) (by omega)
  exact column_singleton_of_missing_vertical (u := (v.1,u.2)) hc hvS hn hs hpoint rfl

theorem no_west_on_negative_singleton_column {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} {v : Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hst : DropletModifiedWord.Stable S) (hvS : v ∈ S)
    (hn : north v ∉ S) (hs : south v ∉ S)
    (hD : innerDiamond L ⊆ S) (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    (hv : v.1 < 0) : InfiniteGridModel.west v ∉ S := by
  intro he
  have hne : (S.image Prod.fst).Nonempty :=
    ⟨(InfiniteGridModel.west v).1,Finset.mem_image.mpr ⟨_,he,rfl⟩⟩
  obtain ⟨u,hu,heq⟩ := Finset.mem_image.mp (Finset.min'_mem (S.image Prod.fst) hne)
  have hmin : ∀ w ∈ S, u.1 ≤ w.1 := by
    intro w hw
    have h := Finset.min'_le (S.image Prod.fst) w.1 (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
    rwa [← heq] at h
  have hux : u.1 < v.1 := by
    have h := hmin _ he
    change u.1 ≤ v.1-1 at h
    omega
  have huy := outward_occupied_same_row_negative hL hr hc hvS hn hs hD hclip hv hux hu
  have hnu : north u ∉ S := by
    intro h
    have hy := outward_occupied_same_row_negative (u := north u) hL hr hc hvS hn hs hD hclip hv hux h
    change u.2+1 = v.2 at hy
    omega
  have hsu : south u ∉ S := by
    intro h
    have hy := outward_occupied_same_row_negative (u := south u) hL hr hc hvS hn hs hD hclip hv hux h
    change u.2-1 = v.2 at hy
    omega
  have heu : InfiniteGridModel.west u ∉ S := by
    intro h
    have h' := hmin _ h
    change u.1 ≤ u.1-1 at h'
    omega
  have hd : 2 ≤ GridMajorityPeeling.degree4 S u :=
    (FiniteMajorityPeeling.stable_iff GridMajorityPeeling.neighbors4 S).mp hst u hu
  have hn' : GridMajorityPeeling.state S (north u) = false := by simp [GridMajorityPeeling.state,hnu]
  have hs' : GridMajorityPeeling.state S (south u) = false := by simp [GridMajorityPeeling.state,hsu]
  have he' : GridMajorityPeeling.state S (InfiniteGridModel.west u) = false := by simp [GridMajorityPeeling.state,heu]
  rw [GridMajorityPeeling.degree4_eq_four_inputs,hn',he',hs'] at hd
  simp only [Bool.toNat_false,zero_add,add_zero] at hd
  cases hw : GridMajorityPeeling.state S (InfiniteGridModel.east u)
  all_goals simp only [hw,Bool.toNat_false,Bool.toNat_true] at hd
  all_goals omega
theorem protected_no_horizontal_opposites {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} {v : Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hst : DropletModifiedWord.Stable S) (hvS : v ∈ S)
    (hD : innerDiamond L ⊆ S) (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    (hd : GridMajorityPeeling.degree4 S v = 2) :
    ¬ (InfiniteGridModel.east v ∈ S ∧ InfiniteGridModel.west v ∈ S) := by
  rintro ⟨he,hw⟩
  have he' : GridMajorityPeeling.state S (InfiniteGridModel.east v) = true := by simp [GridMajorityPeeling.state,he]
  have hw' : GridMajorityPeeling.state S (InfiniteGridModel.west v) = true := by simp [GridMajorityPeeling.state,hw]
  rw [GridMajorityPeeling.degree4_eq_four_inputs,he',hw'] at hd
  simp only [Bool.toNat_true] at hd
  have hn : north v ∉ S := by
    intro h
    have h' : GridMajorityPeeling.state S (north v) = true := by simp [GridMajorityPeeling.state,h]
    rw [h'] at hd
    simp only [Bool.toNat_true] at hd
    omega
  have hs : south v ∉ S := by
    intro h
    have h' : GridMajorityPeeling.state S (south v) = true := by simp [GridMajorityPeeling.state,h]
    rw [h'] at hd
    simp only [Bool.toNat_true] at hd
    omega
  by_cases hz : v.1 = 0
  · exact no_singleton_column_on_axis hL hc hvS hn hs hD hz
  · rcases lt_or_gt_of_ne hz with hneg | hpos
    · exact no_west_on_negative_singleton_column hL hr hc hst hvS hn hs hD hclip hneg hw
    · exact no_east_on_positive_singleton_column hL hr hc hst hvS hn hs hD hclip hpos he
theorem innerDiamond_swap_iff (L : Nat) (u : Site) :
    u.swap ∈ innerDiamond L ↔ u ∈ innerDiamond L := by
  simp [mem_innerDiamond,norm1,Prod.swap,add_comm]

theorem clippedDomain_swap_iff (L : Nat) (u : Site) :
    u.swap ∈ ClippedDiamondGeometry.clippedDomain L ↔ u ∈ ClippedDiamondGeometry.clippedDomain L := by
  simp [ClippedDiamondGeometry.mem_clippedDomain,ClippedDiamondGeometry.clipped,Prod.swap,add_comm,and_left_comm]


-- Coordinate exchange transports the actual finite set and four-neighbour rule.
def transpose (S : Finset Site) : Finset Site := S.image Prod.swap

@[simp] theorem mem_transpose (S : Finset Site) (u : Site) :
    u ∈ transpose S ↔ u.swap ∈ S := by
  simp only [transpose,Finset.mem_image]
  constructor
  · rintro ⟨v,hv,rfl⟩
    simpa using hv
  · intro h
    exact ⟨u.swap,h,by simp⟩

theorem rowConvex_transpose {S : Finset Site} (hc : ColumnConvex S) :
    RowConvex (transpose S) := by
  intro a b x y ha hb hax hxb
  apply (mem_transpose S _).mpr
  exact hc y a b x ((mem_transpose S _).mp ha) ((mem_transpose S _).mp hb) hax hxb

theorem columnConvex_transpose {S : Finset Site} (hr : RowConvex S) :
    ColumnConvex (transpose S) := by
  intro x a b y ha hb hay hyb
  apply (mem_transpose S _).mpr
  exact hr a b y x ((mem_transpose S _).mp ha) ((mem_transpose S _).mp hb) hay hyb

theorem degree4_transpose (S : Finset Site) (u : Site) :
    GridMajorityPeeling.degree4 (transpose S) u = GridMajorityPeeling.degree4 S u.swap := by
  simp only [GridMajorityPeeling.degree4_eq_four_inputs,GridMajorityPeeling.state,
    mem_transpose,InfiniteGridModel.north,InfiniteGridModel.east,
    InfiniteGridModel.south,InfiniteGridModel.west,Prod.swap]
  ac_rfl

theorem stable_transpose {S : Finset Site} (hs : DropletModifiedWord.Stable S) :
    DropletModifiedWord.Stable (transpose S) := by
  apply (FiniteMajorityPeeling.stable_iff GridMajorityPeeling.neighbors4 _).mpr
  intro u hu
  change 2 ≤ GridMajorityPeeling.degree4 (transpose S) u
  rw [degree4_transpose]
  exact (FiniteMajorityPeeling.stable_iff GridMajorityPeeling.neighbors4 _).mp hs u.swap
    ((mem_transpose S u).mp hu)

theorem protected_no_vertical_opposites {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} {v : Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hst : DropletModifiedWord.Stable S) (hvS : v ∈ S)
    (hD : innerDiamond L ⊆ S) (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    (hd : GridMajorityPeeling.degree4 S v = 2) :
    ¬ (north v ∈ S ∧ south v ∈ S) := by
  have hDt : innerDiamond L ⊆ transpose S := by
    intro u hu
    exact (mem_transpose S u).mpr (hD ((innerDiamond_swap_iff L u).mpr hu))
  have hct : transpose S ⊆ ClippedDiamondGeometry.clippedDomain L := by
    intro u hu
    exact (clippedDomain_swap_iff L u).mp (hclip ((mem_transpose S u).mp hu))
  have hvt : v.swap ∈ transpose S := by simpa using hvS
  have hdt : GridMajorityPeeling.degree4 (transpose S) v.swap = 2 := by
    simpa only [degree4_transpose,Prod.swap_swap] using hd
  have h := protected_no_horizontal_opposites hL (rowConvex_transpose hc)
    (columnConvex_transpose hr) (stable_transpose hst) hvt hDt hct hdt
  simpa [InfiniteGridModel.east,InfiniteGridModel.west,InfiniteGridModel.north,
    InfiniteGridModel.south,Prod.swap] using h

theorem protected_erase_convexity {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} {v : Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hst : DropletModifiedWord.Stable S) (hvS : v ∈ S)
    (hD : innerDiamond L ⊆ S) (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    (hd : GridMajorityPeeling.degree4 S v = 2) :
    RowConvex (S.erase v) ∧ ColumnConvex (S.erase v) :=
  ⟨ConvexCleanupUpdate.rowConvex_erase_of_no_opposites hr
    (protected_no_horizontal_opposites hL hr hc hst hvS hD hclip hd),
   ConvexCleanupUpdate.columnConvex_erase_of_no_opposites hc
    (protected_no_vertical_opposites hL hr hc hst hvS hD hclip hd)⟩

theorem protected_cleanup_erase_convexity {L : Nat} (hL : 2 ≤ L)
    {S : Finset Site} {v : Site} (hr : RowConvex S) (hc : ColumnConvex S)
    (hst : DropletModifiedWord.Stable S) (hvS : v ∈ S)
    (hD : innerDiamond L ⊆ S) (hclip : S ⊆ ClippedDiamondGeometry.clippedDomain L)
    (hd : GridMajorityPeeling.degree4 S v = 2) :
    RowConvex (GridMajorityPeeling.cleanup (S.erase v)) ∧
      ColumnConvex (GridMajorityPeeling.cleanup (S.erase v)) := by
  have h := protected_erase_convexity hL hr hc hst hvS hD hclip hd
  exact ConvexCleanupUpdate.cleanup_preserves_convexity h.1 h.2

end MathResearchAnalysis.ProtectedColumnGeometry
