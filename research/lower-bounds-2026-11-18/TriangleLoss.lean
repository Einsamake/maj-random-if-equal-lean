module
public import UniformLower
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchLower.Triangle
open MathResearchAnalysis MeasureTheory
open InfiniteGridModel (Site)
open ClippedDiamondGeometry (clippedDomain reflect)
open ClippedProtectedGeometry (protectedSites norm1)
open OrthogonalGridConvexity
open ForbiddenBirthControl (weight mass)
open WeightedExitArea (missingWeight)
open MathResearchExploration.FullBlockThreshold (sum_positive_offsets)

abbrev Index (r : ℕ) := (s : Fin r) × Fin (s.val+1)

def point {r : ℕ} (x : Site) (a b : Bool) (p : Index r) : Site :=
  let i : ℤ := p.2.val+1
  let j : ℤ := (p.1.val : ℤ)+1-p.2.val
  (x.1+(if a then i else -i),x.2+(if b then j else -j))

theorem point_injective {r : ℕ} (x : Site) (a b : Bool) :
    Function.Injective (point (r := r) x a b) := by
  rintro ⟨s,i⟩ ⟨t,j⟩ h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  have hij : i.val=j.val := by cases a <;> dsimp [point] at hx <;> omega
  have hst : s=t := by apply Fin.ext; cases b <;> dsimp [point] at hy <;> omega
  subst t
  have : i=j := Fin.ext hij
  subst j
  rfl

private theorem weighted_count (r : ℕ) :
    (∑ p : Index r, ((r : ℝ)-p.1.val)) = (r : ℝ)*(r+1)*(r+2)/6 := by
  simp only [Fintype.sum_sigma,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,Nat.cast_succ]
    have expand (i : Fin r) : ((i.val : ℝ)+1)*((r : ℝ)+1-i.val) =
        ((i.val : ℝ)+1)*((r : ℝ)-i.val)+((i.val : ℝ)+1) := by ring
    simp_rw [expand]
    rw [Finset.sum_add_distrib,ih,sum_positive_offsets]
    ring

def radius (L : ℕ) := L/10-1

private theorem abs_signed (b : Bool) (v : ℤ) (hv : 0 ≤ v) : |(if b then v else -v)|=v := by
  split
  · exact abs_of_nonneg hv
  · exact (abs_neg v).trans (abs_of_nonneg hv)

private theorem point_bounds {L : ℕ} (hL : 10 ≤ L) {x : Site} (hx : x ∈ protectedSites L)
    (a b : Bool) (p : Index (radius L)) :
    point x a b p ∈ clippedDomain L ∧ ((radius L : ℕ) : ℝ)-p.1.val ≤ weight L (point x a b p) := by
  let r := radius L
  have hs := p.1.isLt
  have hi := p.2.isLt
  have hband := (ClippedProtectedGeometry.mem_protectedSites_iff_band L x).mp hx
  change 10*(|x.1|+|x.2|) ≤ 9*(L : ℤ)+10 at hband
  have hsize : 10*(radius L+1) ≤ L := by dsimp [radius]; omega
  have hsize' : 10*((radius L : ℤ)+1) ≤ (L : ℤ) := by exact_mod_cast hsize
  have hu : |(point x a b p).1| ≤ |x.1|+(p.2.val : ℤ)+1 := by
    calc
      _ ≤ |x.1|+ |(if a then (p.2.val : ℤ)+1 else -((p.2.val : ℤ)+1))| := abs_add_le _ _
      _ = _ := by rw [abs_signed _ _ (by omega)]; ring
  have hv : |(point x a b p).2| ≤ |x.2|+((p.1.val : ℤ)+1-p.2.val) := by
    calc
      _ ≤ |x.2|+ |(if b then (p.1.val : ℤ)+1-p.2.val else -((p.1.val : ℤ)+1-p.2.val))| := abs_add_le _ _
      _ = _ := by rw [abs_signed _ _ (by omega)]
  have hx0 := abs_nonneg x.1
  have hy0 := abs_nonneg x.2
  constructor
  · rw [ClippedDiamondGeometry.mem_clippedDomain]
    change _ ≤ (L : ℤ) ∧ _ ≤ (L : ℤ) ∧ _ ≤ (L : ℤ)+1
    omega
  · change _ ≤ (L : ℝ)+2-(norm1 (point x a b p) : ℝ)
    have hsum : (radius L : ℤ)-(p.1.val : ℤ) ≤ (L : ℤ)+2-norm1 (point x a b p) := by
      unfold norm1
      omega
    exact_mod_cast hsum

/-- Full triangular certificate in a strict vacant quadrant. -/
theorem shape_loss {L : ℕ} (hL : 10 ≤ L) {S : Finset Site}
    (hr : RowConvex S) (hc : ColumnConvex S) (hn : FourConnected S) (hmiss : ¬ protectedSites L ⊆ S) :
    ((radius L : ℝ)*(radius L+1)*(radius L+2)/6) ≤ missingWeight L S := by
  obtain ⟨x,hx,hxs⟩ := Finset.not_subset.mp hmiss
  obtain ⟨a,b,he⟩ := OrthogonalVacantQuadrant.exists_empty_quadrant hr hc hn hxs
  let f := point (r := radius L) x a b
  have hsub : Finset.univ.image f ⊆ clippedDomain L \ S := by
    intro u hu
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hu
    refine Finset.mem_sdiff.mpr ⟨(point_bounds hL hx a b p).1,?_⟩
    intro hmem
    apply he _ hmem
    have hi := p.2.isLt
    cases a <;> cases b <;> dsimp [f,point,reflect] <;> constructor <;> omega
  apply le_trans _ (WeightedExitArea.mass_le_missingWeight hsub)
  rw [← weighted_count, mass,Finset.sum_image (fun p _ q _ hpq => point_injective x a b hpq)]
  exact Finset.sum_le_sum fun p _ => (point_bounds hL hx a b p).2

theorem cubic_cost {L : ℕ} (hL : 10000 ≤ L) {S : Finset Site}
    (hr : RowConvex S) (hc : ColumnConvex S) (hn : FourConnected S) (hmiss : ¬ protectedSites L ⊆ S) :
    (L : ℝ)^3/6100 ≤ missingWeight L S := by
  have hradius : 998*L ≤ 10000*radius L := by unfold radius; omega
  have hf : (998 : ℝ)*L ≤ 10000*(radius L : ℝ) := by exact_mod_cast hradius
  have hp := pow_le_pow_left₀ (by positivity) hf 3
  have hcost := shape_loss (by omega : 10 ≤ L) hr hc hn hmiss
  have hsq : 0 ≤ (radius L : ℝ)^2 := sq_nonneg _
  have hcube : 0 ≤ (radius L : ℝ)^3 := by positivity
  nlinarith [Nat.cast_nonneg (radius L) (α := ℝ)]

end MathResearchLower.Triangle
