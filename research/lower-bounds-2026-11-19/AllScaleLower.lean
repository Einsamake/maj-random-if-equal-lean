module
public import EarliestAtom
public import LowerConsequences
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchLower.Earliest
open MathResearchAnalysis
open Triangle (cost radius)
open Asymptotic (cleanup)
open OriginalQuadraticLower (halfSide)
open PerturbationSymmetry (squareConfig)
open scoped ENNReal

private theorem refined_cost {L : ℕ} (hl : 400000 ≤ L) : (L : ℝ)^3/6001 ≤ cost L := by
  have hf : (99995 : ℝ)*L ≤ 1000000*(radius L : ℝ) := by
    exact_mod_cast (show 99995*L ≤ 1000000*radius L by unfold radius; omega)
  have hp := pow_le_pow_left₀ (by positivity) hf 3
  unfold cost
  nlinarith [sq_nonneg (radius L : ℝ),show 0 ≤ (radius L : ℝ)^3 by positivity,Nat.cast_nonneg (radius L) (α := ℝ)]

theorem uniform_quadratic (N : ℕ) :
    ENNReal.ofReal ((N : ℝ)^2/850000) ≤ OriginalRecoveryProfile.expectedRecovery (squareConfig N) := by
  by_cases hN : 840000 ≤ N
  · let L := halfSide N
    have hL : 419999 ≤ L := by dsimp [L,halfSide]; omega
    have hl : (419999 : ℝ) ≤ L := by exact_mod_cast hL
    have hr : radius L+2 ≤ N := by dsimp [radius,L,halfSide]; omega
    have hn : N ≤ 2*L+2 := by dsimp [L,halfSide]; omega
    have hn' : (N : ℝ) ≤ 2*(L : ℝ)+2 := by exact_mod_cast hn
    have hN' : (840000 : ℝ) ≤ N := by exact_mod_cast hN
    have hpos : (0 : ℝ)<N := by linarith
    have hr' : (radius L : ℝ)+2 ≤ N := by exact_mod_cast hr
    have hCpos : 0 ≤ cost L := by unfold cost; positivity
    have hC := refined_cost (by omega : 400000 ≤ L)
    have hCtop : cost L ≤ (N : ℝ)^3 := by
      have hprod : (radius L : ℝ)*((radius L : ℝ)+1)*((radius L : ℝ)+2) ≤ (N : ℝ)*N*N := by gcongr <;> linarith
      unfold cost
      nlinarith [pow_nonneg hpos.le 3]
    have hratio := (div_le_one (pow_pos hpos 3)).mpr hCtop
    have hInv : 1/(N : ℝ) ≤ 1/100000 := by apply (div_le_iff₀ hpos).mpr; linarith
    have hnum := mul_le_mul hC (show (99999/100000 : ℝ) ≤ 1-1/(N : ℝ) by linarith) (by norm_num) hCpos
    have hlog : 8*Real.log 2 ≤ 5546/1000 := by linarith [Real.log_two_lt_d9]
    have hD : Asymptotic.slope L ≤ (3328/100 : ℝ)*L := by
      unfold Asymptotic.slope
      nlinarith only [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 6*(L : ℝ)+6 by positivity),hl]
    have hden : Asymptotic.slope L+cost L/(N : ℝ)^3 ≤ (3329/100 : ℝ)*L := by linarith
    have hnsq := mul_self_le_mul_self hpos.le hn'
    have hNprod := mul_le_mul_of_nonneg_right hnsq (Nat.cast_nonneg L (α := ℝ))
    have hsq := mul_le_mul_of_nonneg_right hl (sq_nonneg (L : ℝ))
    have hlin := mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg L (α := ℝ))
    apply le_trans _ (Occupation.occupation_certificate (by omega : 250 ≤ N))
    apply ENNReal.ofReal_le_ofReal
    change _ ≤ (_-cleanup L-2*Asymptotic.slope L)/(Asymptotic.slope L+cost L/(N : ℝ)^3)
    have hdpos : 0 < Asymptotic.slope L := by unfold Asymptotic.slope; positivity
    apply (le_div_iff₀ (by positivity)).mpr
    have hprod := mul_le_mul_of_nonneg_left hden (show 0 ≤ (N : ℝ)^2/850000 by positivity)
    unfold cleanup
    nlinarith only [hprod,hnum,hD,hNprod,hsq,hlin,hl]
  · by_cases hsmall : N ≤ 100
    · apply le_trans _ (square_expected_ge_half N)
      apply ENNReal.ofReal_le_ofReal
      have h := mul_le_mul_of_nonneg_right (show (N : ℝ) ≤ 100 by exact_mod_cast hsmall)
        (Nat.cast_nonneg N (α := ℝ))
      nlinarith only [h,Nat.cast_nonneg N (α := ℝ)]
    · apply le_trans _ (expected_minimum (by omega : 0 < N))
      rw [← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      have hlo : N ≤ lastRound N+2 := by dsimp [lastRound]; omega
      have hl : (N : ℝ) ≤ (lastRound N : ℝ)+2 := by exact_mod_cast hlo
      have hu : (N : ℝ) ≤ 840000 := by exact_mod_cast (show N ≤ 840000 by omega)
      have h100 : (100 : ℝ) ≤ N := by exact_mod_cast (show 100 ≤ N by omega)
      push_cast
      nlinarith only [mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg N (α := ℝ)),hl,h100]

theorem tau_uniform_quadratic (N : ℕ) :
    ENNReal.ofReal ((N : ℝ)^2/850000) ≤ OriginalRecoveryProfile.tau N :=
  (uniform_quadratic N).trans (OriginalRecoveryProfile.square_expectedRecovery_le_tau N)

end MathResearchLower.Earliest
