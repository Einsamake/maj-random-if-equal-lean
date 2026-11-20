module
public import StoppedOccupation
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchLower.Occupation
open MathResearchAnalysis MeasureTheory Filter
open OriginalQuadraticLower (halfSide)
open PerturbationSymmetry (squareConfig)
open Asymptotic (cleanup slope error)
open Triangle (cost radius)
open scoped ENNReal Topology

def mesh : ℝ := 8*Real.log 2

private theorem mesh_pos : 0 < mesh := by unfold mesh; positivity
private theorem mesh_time (k : ℕ) : SchedulingFailure.time k = mesh*((k : ℝ)+1) := by
  unfold SchedulingFailure.time mesh; push_cast; ring

private theorem at_mesh {N : ℕ} (hN : 100 ≤ N) (k : ℕ) :
    alive (halfSide N) (mesh*((k : ℝ)+1)) ≤ survival N k+error (halfSide N) := by
  let L := halfSide N
  have hL : 40 ≤ L := by dsimp [L,halfSide]; omega
  have hn : 0 ≤ error L := by unfold error; positivity
  by_cases h : 2*k<N
  · have he : {η | (k : ℕ∞) < HomogeneousRecoveryTime.synchronous (squareConfig N) η} = Set.univ :=
      Set.eq_univ_of_forall (pathwise_survival h)
    simp only [survival,he,probReal_univ]
    exact le_trans (measureReal_le_one : alive L _ ≤ 1) (le_add_of_nonneg_right hn)
  · rw [← mesh_time]
    have hk : L ≤ k+1 := by dsimp [L,halfSide]; omega
    have hd : (ClippedSquareCoordinates.parameter L+2 : ℝ) ≤ 3*(L : ℝ) := by
      exact_mod_cast (ClippedSquareCoordinates.parameter_side L (by omega)).le.trans (show 2*L+1 ≤ 3*L by omega)
    have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ (ClippedSquareCoordinates.parameter L+2 : ℝ)) hd
    have hcoef : (6/5 : ℝ)*(ClippedSquareCoordinates.parameter L+2 : ℝ)^2 ≤ 11*(L : ℝ)^2 := by nlinarith [sq_nonneg (L : ℝ)]
    have hpow := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ ≤ 1) hk
    have herr := mul_le_mul hcoef hpow (by positivity) (by positivity)
    have hs := inner_tail_le_outer (N := N) (by omega) k
    have hb := (SquareGridLaw.two_way_clock_tail (ClippedSquareCoordinates.parameter L) false k).1
    change InfiniteGridRandomDynamics.measure.real {η | (k : ℕ∞) < InfiniteGridRecoveryTime.synchronous
      (SquareGridEmbedding.extend (ClippedSquareCoordinates.parameter L) (SquarePWMeasure.topConfig _)) η} ≤ _ at hs
    exact hb.trans (add_le_add hs (by simpa only [error,one_div] using herr))

private theorem antitone_grid (N : ℕ) : Antitone (survival N) := fun i j hij =>
  measureReal_mono fun _ h => lt_of_le_of_lt (ENat.natCast_le_natCast.mpr hij) h

private theorem integral_to_sum {N : ℕ} (hN : 100 ≤ N) (K : ℕ) :
    (∫ t in (0 : ℝ)..(mesh*((K : ℝ)+1)), alive (halfSide N) t) ≤
      mesh*(1+(∑ k ∈ Finset.range K, survival N k)+(K : ℝ)*error (halfSide N)) := by
  let f := alive (halfSide N)
  let s (k : ℕ) := mesh*(k : ℝ)
  have hm : Antitone f := ClockEndpointSurvival.clockProbability_antitone _
  have hcell (j : ℕ) : (∫ t in s j..s (j+1), f t) ≤ mesh*f (s j) := by
    have hj : s j ≤ s (j+1) := by dsimp [s]; push_cast; linarith [mesh_pos]
    have hh := intervalIntegral.integral_mono_on (μ := volume) hj hm.intervalIntegrable
      (g := fun _ => f (s j)) intervalIntegrable_const (fun x hx => hm hx.1)
    calc
      _ ≤ _ := hh
      _ = _ := by rw [intervalIntegral.integral_const,smul_eq_mul]; dsimp [s]; push_cast; ring
  have hh := Finset.sum_le_sum (s := Finset.range (K+1)) (fun j _ => hcell j)
  rw [intervalIntegral.sum_integral_adjacent_intervals (fun j _ => hm.intervalIntegrable),← Finset.mul_sum,
    Finset.sum_range_succ'] at hh
  have hsum := Finset.sum_le_sum (s := Finset.range K) (fun j _ => at_mesh hN j)
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum
  have h0 : f 0 ≤ 1 := measureReal_le_one
  have he (j : ℕ) : s (j+1) = mesh*((j : ℝ)+1) := by simp [s]
  simp_rw [he] at hh
  rw [show s 0 = 0 by simp [s]] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (by dsimp [f] at *; linarith) mesh_pos.le)

private theorem power_error {L : ℕ} (hl : 100 ≤ L) : 1000*(L : ℝ)^5 ≤ 2^L := by
  induction L,hl using Nat.le_induction with
  | base => norm_num
  | succ L hl ih =>
    have h : (100 : ℝ) ≤ L := by exact_mod_cast hl
    have hstep : (L : ℝ)+1 ≤ 11/10*(L : ℝ) := by linarith
    have hp := pow_le_pow_left₀ (by positivity) hstep 5
    rw [pow_succ (2 : ℝ) L]; push_cast
    nlinarith only [hp,ih,pow_nonneg (Nat.cast_nonneg L (α := ℝ)) 5]

theorem cube_error {N : ℕ} (hn : 250 ≤ N) :
    (N : ℝ)^3*error (halfSide N) ≤ 1 := by
  let L := halfSide N
  have hl : 100 ≤ L := by dsimp [L,halfSide]; omega
  have hnL : N ≤ 3*L := by dsimp [L,halfSide]; omega
  have hh : (N : ℝ) ≤ 3*(L : ℝ) := by exact_mod_cast hnL
  have hc := pow_le_pow_left₀ (Nat.cast_nonneg N (α := ℝ)) hh 3
  change (N : ℝ)^3*error L ≤ 1
  rw [error,one_div,inv_pow,← div_eq_mul_inv,← mul_div_assoc,div_le_iff₀ (by positivity)]
  nlinarith only [power_error hl,mul_le_mul_of_nonneg_right hc (sq_nonneg (L : ℝ)),pow_nonneg (Nat.cast_nonneg L (α := ℝ)) 5]

theorem occupation_certificate {N : ℕ} (hN : 250 ≤ N) :
    let L := halfSide N
    ENNReal.ofReal ((cost L*(1-1/(N : ℝ))-cleanup L-2*Asymptotic.slope L)/(Asymptotic.slope L+cost L/(N : ℝ)^3)) ≤
      OriginalRecoveryProfile.expectedRecovery (squareConfig N) := by
  let L := halfSide N
  let K := N^3
  let S := ∑ k ∈ Finset.range K, survival N k
  have hl : 100 ≤ L := by dsimp [L,halfSide]; omega
  have hr : 0 < radius L := by unfold Triangle.radius; omega
  have hcost : 0 < cost L := by unfold cost; positivity
  have hsl : 0 < Asymptotic.slope L := by unfold Asymptotic.slope; positivity
  have hnr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hkp : (0 : ℝ)<(K : ℝ) := by dsimp [K]; positivity
  have ht : 0 ≤ mesh*((K : ℝ)+1) := mul_nonneg mesh_pos.le (by positivity)
  have h := weighted_occupation L (by omega) ⟨_,ht⟩
  have hs := integral_to_sum (by omega : 100 ≤ N) K
  have ha := at_mesh (by omega : 100 ≤ N) K
  change cost L*(1-alive L (mesh*((K : ℝ)+1))) ≤ _ at h
  have hb := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 6*(L : ℝ)+6)
  have hleft := mul_le_mul_of_nonneg_left (show 1-(survival N K+error L) ≤ 1-alive L (mesh*((K : ℝ)+1)) by linarith) hcost.le
  have hall : cost L*(1-(survival N K+error L)) ≤ Asymptotic.slope L*(1+S+(K : ℝ)*error L)+cleanup L := by
    apply hleft.trans (h.trans ?_)
    apply add_le_add _ le_rfl
    calc
      _ ≤ (6*(L : ℝ)+6)*(mesh*(1+S+(K : ℝ)*error L)) := hb
      _ = _ := by unfold Asymptotic.slope mesh; ring
  have hlower := Finset.sum_le_sum (s := Finset.range K) (fun j hj => antitone_grid N (Finset.mem_range.mp hj).le)
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hlower
  have htS : survival N K ≤ S/(K : ℝ) := (le_div_iff₀ hkp).mpr (by simpa [S,mul_comm] using hlower)
  have he : (K : ℝ)*error L ≤ 1 := by simpa [K,L] using cube_error hN
  have hen : error L ≤ 1/(N : ℝ) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hnk : (N : ℝ) ≤ (K : ℝ) := by dsimp [K]; push_cast; nlinarith [mul_le_mul_of_nonneg_right hnr (sq_nonneg (N : ℝ)),mul_le_mul_of_nonneg_right hnr (Nat.cast_nonneg N (α := ℝ))]
    exact le_trans (by simpa [mul_comm] using mul_le_mul_of_nonneg_right hnk (show 0 ≤ error L by unfold error; positivity)) (by simpa [mul_comm] using he)
  have hnum := mul_le_mul_of_nonneg_left (add_le_add htS hen) hcost.le
  have hright := mul_le_mul_of_nonneg_left he hsl.le
  apply le_trans _ (finite_tail_sum_le InfiniteGridRandomDynamics.measure _ (HomogeneousRecoveryTime.synchronous_measurable (squareConfig N)) K)
  apply ENNReal.ofReal_le_ofReal
  change (cost L*(1-1/(N : ℝ))-cleanup L-2*Asymptotic.slope L)/(Asymptotic.slope L+cost L/(N : ℝ)^3) ≤ S
  have hnK : (N : ℝ)^3 = (K : ℝ) := by simp [K]
  rw [hnK]
  apply (div_le_iff₀ (by positivity)).mpr
  simp only [div_eq_mul_inv] at hnum ⊢
  nlinarith only [hnum,hright,hall]

end MathResearchLower.Occupation
