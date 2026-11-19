module
public import Packing
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchLower.Earliest
open MathResearchAnalysis InfiniteGridModel MeasureTheory
open PerturbationSymmetry (squareConfig)
open scoped ENNReal

/-- Distance from a coordinate to the nearer side of the containing interval. -/
def margin (N : ℕ) (x : ℤ) : ℤ := min x ((N : ℤ)-1-x)

def depth (N : ℕ) (v : Site) : ℤ := margin N v.1 + margin N v.2

private theorem inside_three {N : ℕ} {v : Site} (hv : Inside N v) (hd : 0 < depth N v) :
    (Inside N (north v) ∧ Inside N (east v) ∧ Inside N (south v)) ∨
    (Inside N (north v) ∧ Inside N (east v) ∧ Inside N (west v)) ∨
    (Inside N (north v) ∧ Inside N (south v) ∧ Inside N (west v)) ∨
    (Inside N (east v) ∧ Inside N (south v) ∧ Inside N (west v)) := by
  dsimp [Inside,north,east,south,west,depth,margin] at *
  omega

private theorem three_force : ∀ n e s w m : Bool,
    ((n = true ∧ e = true ∧ s = true) ∨ (n = true ∧ e = true ∧ w = true) ∨
    (n = true ∧ s = true ∧ w = true) ∨ (e = true ∧ s = true ∧ w = true)) →
    majority4 n e s w m = true := by decide

theorem survives_to_depth (N : ℕ) (marks : Marks) (t : ℕ) (v : Site)
    (hv : Inside N v) (ht : (t : ℤ) ≤ depth N v) :
    synchronous marks (squareConfig N) t v = true := by
  induction t generalizing v with
  | zero => exact decide_eq_true hv
  | succ t ih =>
    have hd : 0 < depth N v := by omega
    have step (x : ℤ) : margin N x - 1 ≤ margin N (x+1) ∧ margin N x - 1 ≤ margin N (x-1) := by
      dsimp [margin]; omega
    have hx := step v.1
    have hy := step v.2
    have hn : (t : ℤ) ≤ depth N (north v) := by dsimp [depth,north] at *; omega
    have he : (t : ℤ) ≤ depth N (east v) := by dsimp [depth,east] at *; omega
    have hs : (t : ℤ) ≤ depth N (south v) := by dsimp [depth,south] at *; omega
    have hw : (t : ℤ) ≤ depth N (west v) := by dsimp [depth,west] at *; omega
    apply three_force
    rcases inside_three hv hd with ⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩|⟨a,b,c⟩
    · exact Or.inl ⟨ih _ a hn,ih _ b he,ih _ c hs⟩
    · exact Or.inr (Or.inl ⟨ih _ a hn,ih _ b he,ih _ c hw⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨ih _ a hn,ih _ b hs,ih _ c hw⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ih _ a he,ih _ b hs,ih _ c hw⟩))

private theorem two_axes : ∀ n e s w : Bool, majority4 n e s w false = true →
    (n = true ∧ s = true) ∨ (e = true ∧ w = true) := by decide

theorem zero_ties_profile (N t : ℕ) (v : Site) :
    synchronous (fun _ _ => false) (squareConfig N) t v = true ↔
    Inside N v ∧ (t : ℤ) ≤ depth N v := by
  refine ⟨?_,fun h => survives_to_depth N _ t v h.1 h.2⟩
  induction t generalizing v with
  | zero =>
    intro h
    have hv : Inside N v := of_decide_eq_true h
    exact ⟨hv, by dsimp [Inside,depth,margin] at *; omega⟩
  | succ t ih =>
    intro h
    have hv := inside_of_state_true N _ (synchronous_supported _ N _
      (OriginalQuadraticLower.square_supported_mono (le_refl N)) (t+1)) h
    refine ⟨hv,?_⟩
    rcases two_axes _ _ _ _ h with ⟨hn,hs⟩|⟨he,hw⟩
    · have a := (ih _ hn).2
      have b := (ih _ hs).2
      dsimp [depth,margin,north,south] at *
      omega
    · have a := (ih _ he).2
      have b := (ih _ hw).2
      dsimp [depth,margin,east,west] at *
      omega

def lastRound (N : ℕ) : ℕ := 2*((N-1)/2)

theorem pathwise_minimum {N : ℕ} (hN : 0 < N) (η : InfiniteGridRandomDynamics.Sample) :
    ((lastRound N+1 : ℕ) : ℕ∞) ≤ HomogeneousRecoveryTime.synchronous (squareConfig N) η := by
  rw [HomogeneousRecoveryTime.synchronous_eq_zero_background N _
    (OriginalQuadraticLower.square_supported_mono (le_refl N))]
  have h : ((lastRound N : ℕ) : ℕ∞) < InfiniteGridRecoveryTime.synchronous (squareConfig N) η := by
    rw [InfiniteGridRecoveryTime.synchronous_tail_iff]
    intro he
    let c : ℤ := ((N-1)/2 : ℕ)
    have hv : Inside N (c,c) := by dsimp [c,Inside]; omega
    have hd : (lastRound N : ℤ) ≤ depth N (c,c) := by dsimp [c,lastRound,depth,margin]; omega
    have hs := survives_to_depth N (InfiniteGridRandomDynamics.marks η) (lastRound N) _ hv hd
    have hz := congrFun he (c,c)
    change synchronous _ _ _ _ = false at hz
    rw [hs] at hz
    contradiction
  cases ht : InfiniteGridRecoveryTime.synchronous (squareConfig N) η using ENat.recTopCoe with
  | top => exact le_top
  | coe k => rw [ht] at h; exact_mod_cast Nat.succ_le_of_lt (ENat.natCast_lt_natCast.mp h)

theorem zero_ties_attain {N : ℕ} (hN : 0 < N) :
    HomogeneousRecoveryTime.synchronous (squareConfig N) (fun _ => false) = (lastRound N+1 : ℕ) := by
  apply le_antisymm _ (pathwise_minimum hN _)
  rw [HomogeneousRecoveryTime.synchronous_eq_zero_background N _
    (OriginalQuadraticLower.square_supported_mono (le_refl N)), InfiniteGridRecoveryTime.synchronous_le_nat_iff]
  funext v
  apply Bool.eq_false_iff.mpr
  intro hv
  have hd := ((zero_ties_profile N (lastRound N+1) v).mp hv).2
  dsimp [depth,margin,lastRound] at hd
  omega

theorem expected_minimum {N : ℕ} (hN : 0 < N) :
    ((lastRound N+1 : ℕ) : ℝ≥0∞) ≤ OriginalRecoveryProfile.expectedRecovery (squareConfig N) := by
  calc
    _ = ∫⁻ _η, ((lastRound N+1 : ℕ) : ℝ≥0∞) ∂InfiniteGridRandomDynamics.measure := by simp
    _ ≤ _ := lintegral_mono fun η => ENat.toENNReal_mono (pathwise_minimum hN η)

end MathResearchLower.Earliest
