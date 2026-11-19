module
public import EarliestSquare
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchLower.Earliest
open MathResearchAnalysis InfiniteGridModel MeasureTheory
open PerturbationSymmetry (squareConfig)
open scoped ENNReal

def squareSites (N : ℕ) : Finset Site :=
  (Finset.Ico (0 : ℤ) N) ×ˢ (Finset.Ico (0 : ℤ) N)

private theorem mem_sites {N : ℕ} {v : Site} : v ∈ squareSites N ↔ Inside N v := by
  simp [squareSites,Inside,and_assoc]

def criticalMarks (N : ℕ) : Finset InfiniteGridRandomDynamics.Event :=
  ((squareSites N).image fun v => (v,(depth N v).toNat+1)) ∪
  ((squareSites N).image fun v => (v,(depth N v).toNat+2))

theorem critical_count (N : ℕ) : (criticalMarks N).card ≤ 2*N^2 := by
  have h : (squareSites N).card = N^2 := by simp [squareSites,Finset.card_product,Int.card_Ico,pow_two]
  unfold criticalMarks
  apply (Finset.card_union_le _ _).trans
  calc
    _ ≤ (squareSites N).card + (squareSites N).card := add_le_add Finset.card_image_le Finset.card_image_le
    _ = _ := by rw [h]; omega

def zeroCylinder (N : ℕ) : Set InfiniteGridRandomDynamics.Sample :=
  Set.pi (criticalMarks N : Set InfiniteGridRandomDynamics.Event) (fun _ => {false})

theorem cylinder_mass (N : ℕ) :
    InfiniteGridRandomDynamics.measure (zeroCylinder N) = ((2 : ℝ≥0∞)⁻¹)^(criticalMarks N).card := by
  unfold InfiniteGridRandomDynamics.measure FairMarks.markMeasure zeroCylinder
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp [FairMarks.fair_singleton]

theorem cylinder_profile {N : ℕ} {η : InfiniteGridRandomDynamics.Sample} (hη : η ∈ zeroCylinder N)
    (t : ℕ) : InfiniteGridRandomDynamics.synchronous (squareConfig N) t η =
      synchronous (fun _ _ => false) (squareConfig N) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext v
    by_cases hin : Inside N v
    · by_cases hu : (t+1 : ℕ) ≤ depth N v
      · exact (survives_to_depth N _ _ v hin (by exact_mod_cast hu)).trans
          (survives_to_depth N _ _ v hin (by exact_mod_cast hu)).symm
      · have hd : 0 ≤ depth N v := by dsimp [Inside,depth,margin] at *; omega
        by_cases hl : (t : ℤ) ≤ depth N v + 1
        · have hm : (v,t+1) ∈ criticalMarks N := by
            have hv := mem_sites.mpr hin
            by_cases he : t+1=(depth N v).toNat+1
            · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,hv,Prod.ext rfl he.symm⟩)
            · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,hv,Prod.ext rfl (by omega)⟩)
          have hz : InfiniteGridRandomDynamics.marks η (t+1) v = false := hη _ hm
          change update (InfiniteGridRandomDynamics.marks η) (t+1) v (InfiniteGridRandomDynamics.synchronous (squareConfig N) t η) = update (fun _ _ => false) (t+1) v (synchronous (fun _ _ => false) (squareConfig N) t)
          rw [ih]
          simp only [update,hz]
        · have bound (x : ℤ) : margin N (x+1) ≤ margin N x+1 ∧ margin N (x-1) ≤ margin N x+1 := by
            dsimp [margin]; omega
          have hx := bound v.1
          have hy := bound v.2
          have off (u : Site) (hu : depth N u ≤ depth N v + 1) :
              synchronous (fun _ _ => false) (squareConfig N) t u = false := by
            apply Bool.eq_false_iff.mpr
            intro h
            have := ((zero_ties_profile N t u).mp h).2
            omega
          change update (InfiniteGridRandomDynamics.marks η) (t+1) v (InfiniteGridRandomDynamics.synchronous (squareConfig N) t η) = update (fun _ _ => false) (t+1) v (synchronous (fun _ _ => false) (squareConfig N) t)
          rw [ih]
          simp only [update]
          rw [off (north v) (by dsimp [depth,north]; omega),
            off (east v) (by dsimp [depth,east]; omega),off (south v) (by dsimp [depth,south]; omega),
            off (west v) (by dsimp [depth,west]; omega)]
          rfl
    · exact (synchronous_supported _ N _ (OriginalQuadraticLower.square_supported_mono (le_refl N)) _ v hin).trans
        (synchronous_supported _ N _ (OriginalQuadraticLower.square_supported_mono (le_refl N)) _ v hin).symm

theorem cylinder_attains {N : ℕ} (hn : 0 < N) {η : InfiniteGridRandomDynamics.Sample} (hη : η ∈ zeroCylinder N) :
    HomogeneousRecoveryTime.synchronous (squareConfig N) η = (lastRound N+1 : ℕ) := by
  have hx := (zero_ties_attain hn).le
  apply le_antisymm _ (pathwise_minimum hn η)
  rw [HomogeneousRecoveryTime.synchronous_eq_zero_background N _
    (OriginalQuadraticLower.square_supported_mono (le_refl N)),InfiniteGridRecoveryTime.synchronous_le_nat_iff] at hx ⊢
  exact (cylinder_profile hη _).trans hx

theorem minimum_atom {N : ℕ} (hn : 0 < N) :
    ((2 : ℝ≥0∞)⁻¹)^(2*N^2) ≤ InfiniteGridRandomDynamics.measure
      {η | HomogeneousRecoveryTime.synchronous (squareConfig N) η = (lastRound N+1 : ℕ)} := by
  calc
    _ ≤ ((2 : ℝ≥0∞)⁻¹)^(criticalMarks N).card :=
      pow_le_pow_right_of_le_one' (by norm_num) (critical_count N)
    _ = _ := (cylinder_mass N).symm
    _ ≤ _ := measure_mono fun _ h => cylinder_attains hn h

end MathResearchLower.Earliest
