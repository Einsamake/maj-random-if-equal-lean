module
public import ForcedCorners
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchLower.ForcedCorners
open MathResearchAnalysis InfiniteGridModel MeasureTheory
open PerturbationSymmetry (squareConfig)
open Earliest (depth margin lastRound squareSites survives_to_depth)
open scoped ENNReal

def minimumEvent (N : ℕ) : Set InfiniteGridRandomDynamics.Sample :=
  {η | HomogeneousRecoveryTime.synchronous (squareConfig N) η = (lastRound N+1 : ℕ)}

private theorem empty_at_minimum {N : ℕ} {η : InfiniteGridRandomDynamics.Sample} (h : η ∈ minimumEvent N) :
    state N η (lastRound N+1) = fun _ => false := by
  have he := le_of_eq (show HomogeneousRecoveryTime.synchronous (squareConfig N) η = (lastRound N+1 : ℕ) from h)
  rw [HomogeneousRecoveryTime.synchronous_eq_zero_background N _
    (OriginalQuadraticLower.square_supported_mono (le_refl N)),InfiniteGridRecoveryTime.synchronous_le_nat_iff] at he
  exact he

private theorem represent_coord {l : ℕ} {z : ℤ} (hz : 0 ≤ z ∧ z < (2*(l+1) : ℕ)) :
    ∃ b : Bool, ∃ x : ℕ, x ≤ l ∧ coord (2*(l+1)) b x = z ∧ (x : ℤ) = margin (2*(l+1)) z := by
  by_cases h : z ≤ l
  · exact ⟨false,z.toNat,by omega,by dsimp [coord]; omega,by dsimp [margin]; omega⟩
  · let y : ℤ := 2*((l : ℤ)+1)-1-z
    exact ⟨true,y.toNat,by dsimp [y]; omega,by dsimp [y,coord]; omega,by dsimp [y,margin]; omega⟩

def firstMarks (N : ℕ) : Finset InfiniteGridRandomDynamics.Event :=
  (squareSites N).image fun v => (v,(depth N v).toNat+1)

theorem first_count (N : ℕ) : (firstMarks N).card = N^2 := by
  unfold firstMarks
  rw [Finset.card_image_of_injective _ (fun _ _ hh => congrArg Prod.fst hh)]
  simp [squareSites,Finset.card_product,Int.card_Ico,pow_two]

theorem even_forces_all (l : ℕ) : minimumEvent (2*(l+1)) ⊆ allZero (firstMarks (2*(l+1))) := by
  let N := 2*(l+1)
  intro η hη e he
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp he
  have hin : Inside N v := by simpa [N,squareSites,Inside,and_assoc] using hv
  obtain ⟨b,x,hx,hbx,hxm⟩ := represent_coord ⟨hin.1,hin.2.1⟩
  obtain ⟨c,y,hy,hcy,hym⟩ := represent_coord ⟨hin.2.2.1,hin.2.2.2⟩
  have hsite : site N b c x y=v := Prod.ext hbx hcy
  have hd : x+y=(depth N v).toNat := by dsimp [depth,N]; omega
  have ht : lastRound N=l+l := by dsimp [lastRound,N]; omega
  have hg : gone N η b c l l := by
    change state N η (l+l+1) _ = false
    rw [← ht]
    exact congrFun (empty_at_minimum hη) _
  have h := force_rectangle (N := N) (h := l+1) (by rfl) (by omega) (by omega) hg hx hy
  rw [hsite,hd] at h
  exact h

theorem even_atom_upper (l : ℕ) : InfiniteGridRandomDynamics.measure (minimumEvent (2*(l+1))) ≤
    ((2 : ℝ≥0∞)⁻¹)^((2*(l+1))^2) := by
  exact (measure_mono (even_forces_all l)).trans_eq ((zero_mass _).trans (by rw [first_count]))

abbrev atSite (N : ℕ) (η : InfiniteGridRandomDynamics.Sample) (t : ℕ) (x y : ℤ) :=
  state N η t (x,y)

private theorem next (N : ℕ) (η : InfiniteGridRandomDynamics.Sample) (t : ℕ) (x y : ℤ) :
    atSite N η (t+1) x y = majority4 (atSite N η t x (y+1)) (atSite N η t (x+1) y)
      (atSite N η t x (y-1)) (atSite N η t (x-1) y) (η ((x,y),t+1)) := rfl

private theorem three_of_four : ∀ n e s w m : Bool,
    ((n = true ∧ e = true ∧ s = true) ∨ (n = true ∧ e = true ∧ w = true) ∨
    (n = true ∧ s = true ∧ w = true) ∨ (e = true ∧ s = true ∧ w = true)) →
    majority4 n e s w m = true := by decide

/-- An occupied centre and its four diagonals guarantee occupancy two rounds later. -/
theorem diagonal_persistence (N : ℕ) (η : InfiniteGridRandomDynamics.Sample) (t : ℕ) (x y : ℤ)
    (h0 : atSite N η t x y = true)
    (hne : atSite N η t (x+1) (y+1) = true) (hnw : atSite N η t (x-1) (y+1) = true)
    (hse : atSite N η t (x+1) (y-1) = true) (hsw : atSite N η t (x-1) (y-1) = true) :
    atSite N η (t+2) x y = true := by
  have hn : atSite N η (t+1) x (y+1) = true := by
    rw [next]; apply three_of_four; exact Or.inr (Or.inr (Or.inr ⟨hne,by simpa using h0,hnw⟩))
  have he : atSite N η (t+1) (x+1) y = true := by
    rw [next]; apply three_of_four; exact Or.inr (Or.inr (Or.inl ⟨hne,hse,by simpa using h0⟩))
  have hs : atSite N η (t+1) x (y-1) = true := by
    rw [next]; apply three_of_four; exact Or.inr (Or.inl ⟨by simpa using h0,hse,hsw⟩)
  have hw : atSite N η (t+1) (x-1) y = true := by
    rw [next]; apply three_of_four; exact Or.inl ⟨hnw,by simpa using h0,hsw⟩
  rw [show t+2=t+1+1 by omega,next,hn,he,hs,hw]
  rfl

private theorem odd_missing_tip (l : ℕ) {η : InfiniteGridRandomDynamics.Sample} (hη : η ∈ minimumEvent (2*l+3)) :
    ∃ b c : Bool, gone (2*l+3) η b c l l := by
  let N := 2*l+3
  let q : ℤ := (l : ℤ)+1
  let t := l+l+1
  by_contra! h
  have ha (b c : Bool) : state N η t (site N b c l l) = true := by
    exact Bool.eq_true_of_not_eq_false (h b c)
  have hdiag (b c : Bool) : atSite N η t (if b then q+1 else q-1) (if c then q+1 else q-1) = true := by
    have coord_id (z : Bool) : (if z then q+1 else q-1) = coord N z l := by
      cases z <;> dsimp [coord,N,q] <;> omega
    rw [coord_id,coord_id]; exact ha b c
  have h0 : atSite N η t q q = true := survives_to_depth N _ t (q,q)
    (by dsimp [N,q,Inside]; omega) (by dsimp [N,q,t,depth,margin]; omega)
  have hs := diagonal_persistence N η t q q h0 (hdiag true true) (hdiag false true) (hdiag true false) (hdiag false false)
  have ht : t+2=lastRound N+1 := by dsimp [t,lastRound,N]; omega
  have hz := congrFun (empty_at_minimum hη) (q,q)
  rw [ht] at hs
  exact Bool.noConfusion (hz.symm.trans hs)

theorem odd_atom_upper (l : ℕ) : InfiniteGridRandomDynamics.measure (minimumEvent (2*l+3)) ≤
    4*((2 : ℝ≥0∞)⁻¹)^((l+1)^2) := by
  let E (b c : Bool) := allZero (quadrantMarks (2*l+3) (l+1) b c)
  have hsub : minimumEvent (2*l+3) ⊆ ⋃ (b : Bool) (c : Bool), E b c := by
    intro η hη
    obtain ⟨b,c,h⟩ := odd_missing_tip l hη
    exact Set.mem_iUnion.mpr ⟨b,Set.mem_iUnion.mpr ⟨c,tip_forces_quadrant (by omega) h⟩⟩
  have hm (b c : Bool) : InfiniteGridRandomDynamics.measure (E b c) = ((2 : ℝ≥0∞)⁻¹)^((l+1)^2) := by
    rw [show E b c=allZero _ by rfl,zero_mass,quadrant_card]
  calc
    _ ≤ _ := measure_mono hsub
    _ ≤ ∑ b : Bool, InfiniteGridRandomDynamics.measure (⋃ c : Bool, E b c) := by
      simpa [tsum_fintype] using measure_iUnion_le (μ := InfiniteGridRandomDynamics.measure) (fun b => ⋃ c : Bool, E b c)
    _ ≤ ∑ b : Bool, ∑ c : Bool, InfiniteGridRandomDynamics.measure (E b c) := by
      apply Finset.sum_le_sum
      intro b _
      simpa [tsum_fintype] using measure_iUnion_le (μ := InfiniteGridRandomDynamics.measure) (E b)
    _ = _ := by simp only [hm,Fintype.sum_bool]; ring

/-- A single area-order certificate for both parities, on the original fair law. -/
theorem minimum_area_bounds {N : ℕ} (hN : 7 ≤ N) :
    ((2 : ℝ≥0∞)⁻¹)^(2*N^2) ≤ InfiniteGridRandomDynamics.measure (minimumEvent N) ∧
    InfiniteGridRandomDynamics.measure (minimumEvent N) ≤ ((2 : ℝ≥0∞)⁻¹)^(N^2/8) := by
  refine ⟨Earliest.minimum_atom (by omega),?_⟩
  have hb : (2 : ℝ≥0∞)⁻¹ ≤ 1 := by norm_num
  by_cases hp : N%2=0
  · let l := N/2-1
    have hn : N=2*(l+1) := by dsimp [l]; omega
    calc
      _ ≤ ((2 : ℝ≥0∞)⁻¹)^(N^2) := by simpa only [hn] using even_atom_upper l
      _ ≤ _ := pow_le_pow_right_of_le_one' hb (Nat.div_le_self _ _)
  · let l := N/2-1
    have hn : N=2*l+3 := by dsimp [l]; omega
    have hl : 2 ≤ l := by dsimp [l]; omega
    have hlin : 4 ≤ l^2 := by nlinarith only [Nat.mul_le_mul hl hl]
    have hq : N^2+16 ≤ 8*((l+1)^2) := by rw [hn]; nlinarith only [hlin,hl]
    have hcomp : N^2/8+2 ≤ (l+1)^2 := by omega
    have hpow := pow_le_pow_right_of_le_one' hb hcomp
    calc
      _ ≤ 4*((2 : ℝ≥0∞)⁻¹)^((l+1)^2) := by simpa only [hn] using odd_atom_upper l
      _ ≤ 4*((2 : ℝ≥0∞)⁻¹)^(N^2/8+2) := by gcongr
      _ = _ := by
        have hc : (4 : ℝ≥0∞)*((2 : ℝ≥0∞)⁻¹)^2 = 1 := by
          rw [← ENNReal.inv_pow, show (2 : ℝ≥0∞)^2=4 by norm_num]
          exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
        rw [pow_add,mul_comm (((2 : ℝ≥0∞)⁻¹)^(N^2/8)),← mul_assoc,hc,one_mul]

end MathResearchLower.ForcedCorners
