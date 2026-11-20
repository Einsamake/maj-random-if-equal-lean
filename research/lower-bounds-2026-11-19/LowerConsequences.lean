module
public import StoppedLower
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchLower.Results
open MathResearchAnalysis MeasureTheory Filter
open Triangle (cost radius)
open Asymptotic (cleanup slope z ell rad H B D)
open OriginalQuadraticLower (halfSide)
open PerturbationSymmetry (squareConfig)
open scoped Topology ENNReal

theorem square_all_scales (N : ℕ) :
    ENNReal.ofReal ((N : ℝ)^2/920000) ≤ OriginalRecoveryProfile.expectedRecovery (squareConfig N) := by
  by_cases hN : 460000 ≤ N
  · let L := halfSide N
    have hL : 229999 ≤ L := by dsimp [L,halfSide]; omega
    have hl : (229999 : ℝ) ≤ L := by exact_mod_cast hL
    have hr : radius L+2 ≤ N := by dsimp [radius,L,halfSide]; omega
    have hn : N ≤ 2*L+2 := by dsimp [L,halfSide]; omega
    have hn' : (N : ℝ) ≤ 2*(L : ℝ)+2 := by exact_mod_cast hn
    have hN' : (460000 : ℝ) ≤ N := by exact_mod_cast hN
    have hpos : (0 : ℝ)<N := by linarith
    have hr' : (radius L : ℝ)+2 ≤ N := by exact_mod_cast hr
    have hCpos : 0 ≤ cost L := by unfold cost; positivity
    have hC := Triangle.numerical_cost (by omega : 10000 ≤ L)
    have hCtop : cost L ≤ (N : ℝ)^3 := by
      have hprod : (radius L : ℝ)*((radius L : ℝ)+1)*((radius L : ℝ)+2) ≤ (N : ℝ)*N*N := by gcongr <;> linarith
      unfold cost
      nlinarith [pow_nonneg hpos.le 3]
    have hratio := (div_le_one (pow_pos hpos 3)).mpr hCtop
    have hInv : 1/(N : ℝ) ≤ 1/1000 := by apply (div_le_iff₀ hpos).mpr; linarith
    have hnum := mul_le_mul hC (show (999/1000 : ℝ) ≤ 1-1/(N : ℝ) by linarith) (by norm_num) hCpos
    have hlog : 8*Real.log 2 ≤ 111/20 := by linarith [Real.log_two_lt_d9]
    have hD : Asymptotic.slope L ≤ (3331/100 : ℝ)*L := by
      unfold Asymptotic.slope
      nlinarith only [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 6*(L : ℝ)+6 by positivity),hl]
    have hden : Asymptotic.slope L+cost L/(N : ℝ)^3 ≤ (334/10 : ℝ)*L := by linarith
    have hnsq := mul_self_le_mul_self hpos.le hn'
    have hNprod := mul_le_mul_of_nonneg_right hnsq (Nat.cast_nonneg L (α := ℝ))
    have hsq := mul_le_mul_of_nonneg_right hl (sq_nonneg (L : ℝ))
    have hlin := mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg L (α := ℝ))
    apply le_trans _ (Occupation.occupation_certificate (by omega : 250 ≤ N))
    apply ENNReal.ofReal_le_ofReal
    change _ ≤ (_-cleanup L-2*Asymptotic.slope L)/(Asymptotic.slope L+cost L/(N : ℝ)^3)
    have hdpos : 0 < Asymptotic.slope L := by unfold Asymptotic.slope; positivity
    apply (le_div_iff₀ (by positivity)).mpr
    have hprod := mul_le_mul_of_nonneg_left hden (show 0 ≤ (N : ℝ)^2/920000 by positivity)
    unfold cleanup
    nlinarith only [hprod,hnum,hD,hNprod,hsq,hlin,hl]
  · apply le_trans _ (square_expected_ge_half N)
    apply ENNReal.ofReal_le_ofReal
    have hn : (N : ℝ) ≤ 460000 := by exact_mod_cast (show N ≤ 460000 by omega)
    nlinarith only [mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg N (α := ℝ))]

theorem tau_all_scales (N : ℕ) : ENNReal.ofReal ((N : ℝ)^2/920000) ≤ OriginalRecoveryProfile.tau N :=
  (square_all_scales N).trans (OriginalRecoveryProfile.square_expectedRecovery_le_tau N)

private def normalized (N : ℕ) : ℝ :=
  (H N*(1-z N)-B N-2*D N*(z N)^2)/(D N+H N*z N)

private theorem normalized_limit :
    Tendsto normalized atTop (𝓝 (1/(1152000*Real.log 2))) := by
  have hz : Tendsto z atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hr := Asymptotic.rad_limit
  have hl := Asymptotic.ell_limit
  have hh : Tendsto H atTop (𝓝 (1/48000)) := by
    convert ((hr.mul (hr.add hz)).mul (hr.add (hz.const_mul 2))).div_const 6 using 1; norm_num
  have hb : Tendsto B atTop (𝓝 0) := by
    convert (((hl.add (hz.const_mul 2)).mul ((hl.const_mul 4).add (hz.const_mul 2))).mul hz) using 1; norm_num
  have hd : Tendsto D atTop (𝓝 (24*Real.log 2)) := by
    convert (((hl.const_mul 6).add (hz.const_mul 6)).mul_const (8*Real.log 2)) using 1; ring
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := (((hh.mul (tendsto_const_nhds (x := (1:ℝ)) |>.sub hz)).sub hb).sub ((hd.const_mul 2).mul (hz.pow 2))).div
    (hd.add (hh.mul hz)) (by positivity)
  convert h using 1
  · rfl
  field_simp [hlog.ne']; ring

private theorem normalized_lower {N : ℕ} (hn : 250 ≤ N) :
    ENNReal.ofReal (normalized N*(N : ℝ)^2) ≤ OriginalRecoveryProfile.expectedRecovery (squareConfig N) := by
  have hp : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hH : H N = cost (halfSide N)/(N : ℝ)^3 := by dsimp [H,rad,z,cost]; field_simp [hp]
  have hB : B N = cleanup (halfSide N)/(N : ℝ)^3 := by dsimp [B,ell,z,cleanup]; field_simp [hp]
  have hD : D N = Asymptotic.slope (halfSide N)/(N : ℝ) := by dsimp [D,ell,z,Asymptotic.slope]; field_simp [hp]
  apply le_trans _ (Occupation.occupation_certificate hn)
  apply ENNReal.ofReal_le_ofReal
  apply le_of_eq
  rw [normalized,hH,hB,hD]
  dsimp only [z]
  field_simp [hp]

theorem square_asymptotic_lower {c : ℝ} (hc : c < 1/(1152000*Real.log 2)) :
    ∀ᶠ N : ℕ in atTop, ENNReal.ofReal (c*(N : ℝ)^2) ≤ OriginalRecoveryProfile.expectedRecovery (squareConfig N) := by
  filter_upwards [normalized_limit.eventually (lt_mem_nhds hc),eventually_ge_atTop 250] with N h hn
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h.le (sq_nonneg _))).trans (normalized_lower hn)

theorem tau_asymptotic_lower {c : ℝ} (hc : c < 1/(1152000*Real.log 2)) :
    ∀ᶠ N : ℕ in atTop, ENNReal.ofReal (c*(N : ℝ)^2) ≤ OriginalRecoveryProfile.tau N :=
  (square_asymptotic_lower hc).mono fun N h => h.trans (OriginalRecoveryProfile.square_expectedRecovery_le_tau N)

end MathResearchLower.Results
