module
public import TriangleLoss
public import Mathlib.Analysis.SpecificLimits.Normed
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchLower.Static
open MathResearchAnalysis MeasureTheory Filter
open InfiniteGridModel (Site)
open ClippedDiamondGeometry (clippedDomain)
open ClippedProtectedGeometry (protectedSites norm1)
open OrthogonalGridConvexity
open WeightedExitArea (missingWeight)
open Triangle (Index)
open scoped Topology

def shape (m : ℕ) : Finset Site :=
  (clippedDomain (20*m)).filter (fun v => v.1 < 9*(m : ℤ) ∨ v.2 < 9*(m : ℤ))

theorem valid (m : ℕ) (hm : 0<m) : RowConvex (shape m) ∧ ColumnConvex (shape m) ∧
    FourConnected (shape m) ∧ ¬ protectedSites (20*m) ⊆ shape m := by
  have hrow : RowConvex (shape m) := by
    intro a b x y ha hb hl hr
    simp only [shape,Finset.mem_filter] at ha hb ⊢
    exact ⟨clipped_rowConvex _ _ _ _ _ ha.1 hb.1 hl hr,by rcases hb.2 with h|h <;> omega⟩
  have hcol : ColumnConvex (shape m) := by
    intro x a b y ha hb hl hr
    simp only [shape,Finset.mem_filter] at ha hb ⊢
    exact ⟨clipped_columnConvex _ _ _ _ _ ha.1 hb.1 hl hr,by rcases hb.2 with h|h <;> omega⟩
  let rec path0 (v : Site) (hv : v ∈ shape m) : Path (shape m) v (0,0) := by
    by_cases hx : v.1=0
    · by_cases hy : v.2=0
      · rw [show v = (0,0) from Prod.ext hx hy]
      · let u := ClippedDiamondGeometry.verticalNeighbor v
        have hd := ClippedGridConnectivity.vertical_internalStep (Finset.mem_filter.mp hv).1 hy
        have hu : u ∈ shape m := Finset.mem_filter.mpr ⟨hd.2.1,Or.inl (by change v.1 < 9*(m : ℤ); omega)⟩
        exact (Relation.ReflTransGen.single (show InternalStep (shape m) v u from ⟨hv,hu,hd.2.2⟩)).trans (path0 u hu)
    · let u := ClippedDiamondGeometry.horizontalNeighbor v
      have hd := ClippedGridConnectivity.horizontal_internalStep (Finset.mem_filter.mp hv).1 hx
      have hu : u ∈ shape m := by
        apply Finset.mem_filter.mpr
        refine ⟨hd.2.1,?_⟩
        rcases (Finset.mem_filter.mp hv).2 with h|h
        · left
          dsimp [u,ClippedDiamondGeometry.horizontalNeighbor,ClippedDiamondGeometry.toward]
          split <;> omega
        · exact Or.inr h
      exact (Relation.ReflTransGen.single (show InternalStep (shape m) v u from ⟨hv,hu,hd.2.2⟩)).trans (path0 u hu)
  termination_by v.1.natAbs + v.2.natAbs
  decreasing_by
    · simpa [ClippedDiamondGeometry.verticalNeighbor] using ClippedGridConnectivity.toward_natAbs_lt v.2 hy
    · simpa [ClippedDiamondGeometry.horizontalNeighbor] using ClippedGridConnectivity.toward_natAbs_lt v.1 hx
  have rev {u v : Site} (h : Path (shape m) u v) : Path (shape m) v u := by
    induction h with
    | refl => exact .refl
    | tail _ hh ih => exact (Relation.ReflTransGen.single
        (show InternalStep _ _ _ from ⟨hh.2.1,hh.1,ConvexBirthUpdate.neighbors4_symmetric hh.2.2⟩)).trans ih
  refine ⟨hrow,hcol,fun u hu v hv => (path0 u hu).trans (rev (path0 v hv)),?_⟩
  intro h
  let x : Site := (9*(m : ℤ),9*(m : ℤ))
  have hi : x ∈ ClippedProtectedGeometry.innerDiamond (20*m) := by
    rw [ClippedProtectedGeometry.mem_innerDiamond]
    dsimp [x,norm1]; rw [abs_of_nonneg (by positivity : (0 : ℤ)≤9*m)]
    omega
  have hs := (Finset.mem_filter.mp (h (ClippedProtectedGeometry.innerDiamond_subset_protectedSites _ hi))).2
  simp [x] at hs

private def cell (m : ℕ) (p : Index (2*m+2)) : Site :=
  (9*(m : ℤ)+p.2.val,9*(m : ℤ)+p.1.val-p.2.val)

private theorem cell_inj (m : ℕ) : Function.Injective (cell m) := by
  rintro ⟨s,i⟩ ⟨t,j⟩ h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [cell] at hx hy
  have hst : s=t := by apply Fin.ext; omega
  subst t
  have : i=j := by apply Fin.ext; omega
  subst j; rfl

private theorem missing_eq_triangle (m : ℕ) (hm : 0<m) :
    clippedDomain (20*m) \ shape m = Finset.univ.image (cell m) := by
  ext v
  constructor
  · intro hv
    obtain ⟨hd,hs⟩ := Finset.mem_sdiff.mp hv
    have hbad : ¬(v.1<9*(m : ℤ) ∨ v.2<9*(m : ℤ)) := fun h => hs (Finset.mem_filter.mpr ⟨hd,h⟩)
    have hh := (ClippedDiamondGeometry.mem_clippedDomain _ _).mp hd
    dsimp [ClippedDiamondGeometry.clipped] at hh
    rw [abs_of_nonneg (by omega : 0 ≤ v.1),abs_of_nonneg (by omega : 0 ≤ v.2)] at hh
    let s : Fin (2*m+2) := ⟨(v.1+v.2-18*m).toNat,by omega⟩
    let i : Fin (s.val+1) := ⟨(v.1-9*m).toNat,by dsimp [s]; omega⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨s,i⟩,Finset.mem_univ _,?_⟩
    apply Prod.ext <;> dsimp [cell,s,i] <;> omega
  · intro hv
    obtain ⟨⟨s,i⟩,_,rfl⟩ := Finset.mem_image.mp hv
    have hs := s.isLt
    have hi := i.isLt
    have hx : 0 ≤ 9*(m : ℤ)+i.val := by omega
    have hy : 0 ≤ 9*(m : ℤ)+s.val-i.val := by omega
    apply Finset.mem_sdiff.mpr
    constructor
    · rw [ClippedDiamondGeometry.mem_clippedDomain]
      dsimp [ClippedDiamondGeometry.clipped,cell]
      rw [abs_of_nonneg hx,abs_of_nonneg hy]
      omega
    · intro h
      have := (Finset.mem_filter.mp h).2
      dsimp [cell] at this
      omega

theorem exact_cost (m : ℕ) (hm : 0<m) :
    missingWeight (20*m) (shape m) = (2*(m : ℝ)+2)*(2*m+3)*(2*m+4)/6 := by
  rw [missingWeight,ForbiddenBirthControl.mass,missing_eq_triangle m hm,
    Finset.sum_image (fun p _ q _ h => cell_inj m h)]
  calc
    _ = ∑ p : Index (2*m+2), (((2*m+2 : ℕ) : ℝ)-p.1.val) := by
      apply Finset.sum_congr rfl
      intro p _
      have hi := p.2.isLt
      have hx : (0 : ℤ) ≤ 9*(m : ℤ)+p.2.val := by omega
      have hy : (0 : ℤ) ≤ 9*(m : ℤ)+p.1.val-p.2.val := by omega
      dsimp [ForbiddenBirthControl.weight,norm1,cell]
      rw [abs_of_nonneg hx,abs_of_nonneg hy]
      push_cast; ring
    _ = _ := by rw [Triangle.weighted_count]; push_cast; ring

/-- The triangular cost has the optimal leading coefficient for the stated static shape class. -/
theorem sharp_limit : Tendsto (fun m : ℕ => missingWeight (20*m) (shape m)/(20*(m : ℝ))^3) atTop (𝓝 (1/6000)) := by
  have hz := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h (j : ℝ) : Tendsto (fun m : ℕ => 2+j*(1/(m : ℝ))) atTop (𝓝 2) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).add (hz.const_mul j)
  have hp : Tendsto (fun m : ℕ => (2+2*(1/(m : ℝ)))*(2+3*(1/(m : ℝ)))*(2+4*(1/(m : ℝ)))/48000)
      atTop (𝓝 (1/6000)) := by convert (((h 2).mul (h 3)).mul (h 4)).div_const 48000 using 1; norm_num
  apply hp.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  rw [exact_cost m hm]
  have hne : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  field_simp [hne]; ring

end MathResearchLower.Static
