module
public import Packing
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchLower.Packing
open MathResearchAnalysis MeasureTheory Filter
open PerturbationSymmetry (squareConfig)
open OriginalQuadraticLower (halfSide)
open scoped Topology

def blockSide (k : ℕ) : ℕ := 2000*(k.sqrt+1)

theorem small_square_cdf (k : ℕ) : cdf (blockSide k) k ≤ 1/2 := by
  let r := k.sqrt+1
  let m := blockSide k
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hkr : k+1 ≤ r^2 := by simpa [r,Nat.pow_two] using Nat.lt_succ_sqrt k
  have hm : m = 2000*r := rfl
  change cdf m k ≤ _
  have hc := cdf_add_survival m k
  by_cases h : 2000000 ≤ m
  · have hL : halfSide m = 1000*r-1 := by unfold halfSide; omega
    have hrL : 999*r ≤ halfSide m := by omega
    have hs := Nat.mul_self_le_mul_self hrL
    have hs' : (999*(r : ℝ))^2 ≤ (halfSide m : ℝ)^2 := by
      exact_mod_cast (show (999*r)^2 ≤ (halfSide m)^2 by simpa [pow_two] using hs)
    have hkr' : (k : ℝ)+1 ≤ (r : ℝ)^2 := by exact_mod_cast hkr
    have he := square_survival_envelope h k
    by_contra! hh
    have hpos : (0 : ℝ) < halfSide m := by exact_mod_cast (show 0 < halfSide m by omega)
    have hmul := mul_lt_mul_of_pos_right (show (11/25 : ℝ) < 47/50-survival m k by linarith) (sq_pos_of_pos hpos)
    nlinarith only [he,hmul,hs',hkr',sq_nonneg (r : ℝ)]
  · have hr' : r ≤ 999 := by omega
    have h2 := Nat.mul_le_mul_right r hr'
    have hfast : 2*k < m := by nlinarith only [hkr,h2,hm,hr]
    have hall : {η | (k : ℕ∞) < HomogeneousRecoveryTime.synchronous (squareConfig m) η} = Set.univ :=
      Set.eq_univ_of_forall (pathwise_survival hfast)
    have hp : survival m k = 1 := by simp only [survival,hall,probReal_univ]
    linarith

theorem finite_lower_tail (N k : ℕ) : cdf N k ≤ (1/2 : ℝ)^((N/blockSide k)^2) := by
  let m := blockSide k
  have hm : 2 ≤ m := by dsimp [m,blockSide]; omega
  have hs : m-2+2=m := by omega
  have hf : N/m*(m-2+2) ≤ N := hs ▸ Nat.div_mul_le_self N m
  have hp := packed_cdf hf k
  rw [hs] at hp
  exact hp.trans (pow_le_pow_left₀ measureReal_nonneg (small_square_cdf k) _)

private theorem side_sq_le (k : ℕ) : (blockSide k)^2 ≤ 16000000*(k+1) := by
  have h := Nat.sqrt_le' k
  have hsq : (k.sqrt+1)^2 ≤ 4*(k+1) := by
    nlinarith only [h,Nat.zero_le ((k.sqrt-1)^2),Nat.le_mul_self k.sqrt]
  dsimp [blockSide]
  nlinarith only [hsq]

/-- Uniform essential-singularity bound at the lower end of the diffusive scale. -/
theorem exponential_fast_tail (N k : ℕ) :
    cdf N k ≤ 2*Real.exp (-(Real.log 2)*(N : ℝ)^2/(64000000*((k : ℝ)+1))) := by
  let m := blockSide k
  let d := N/m
  have hm : 0 < m := by dsimp [m,blockSide]; omega
  have hdivide : N < (d+1)*m := by simpa only [d,Nat.mul_comm m] using Nat.lt_mul_div_succ N hm
  have hs := side_sq_le k
  have hdim : N^2 ≤ (d^2+1)*(64000000*(k+1)) := by
    have hd : (d+1)^2 ≤ 4*(d^2+1) := by nlinarith [Nat.le_mul_self d]
    have hN := Nat.pow_le_pow_left hdivide.le 2
    rw [mul_pow] at hN
    exact hN.trans ((Nat.mul_le_mul hd hs).trans_eq (by ring))
  have hreal : (N : ℝ)^2 ≤ ((d : ℝ)^2+1)*(64000000*((k : ℝ)+1)) := by exact_mod_cast hdim
  have hq := (div_le_iff₀ (by positivity : (0 : ℝ)<64000000*((k : ℝ)+1))).mpr hreal
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hexp := Real.exp_le_exp.mpr (show -((d : ℝ)^2)*Real.log 2 ≤
      Real.log 2 + -(Real.log 2)*(N : ℝ)^2/(64000000*((k : ℝ)+1)) by
    have hh := mul_le_mul_of_nonneg_right hq hlog
    linear_combination hh)
  rw [Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ)<2)] at hexp
  have heq : (1/2 : ℝ)^(d^2) = Real.exp (-((d : ℝ)^2)*Real.log 2) := by
    rw [show -((d : ℝ)^2)*Real.log 2 = ((d^2 : ℕ) : ℝ)*(-Real.log 2) by push_cast; ring,
      Real.exp_nat_mul,Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ)<2)]
    simp [one_div]
  exact (finite_lower_tail N k).trans (heq.trans_le hexp)

end MathResearchLower.Packing
