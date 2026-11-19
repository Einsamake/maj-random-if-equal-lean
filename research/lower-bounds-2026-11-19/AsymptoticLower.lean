module
public import ImprovedMean
public import Mathlib.Analysis.SpecificLimits.Normed
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchLower.Asymptotic
open MathResearchAnalysis MeasureTheory Filter Triangle
open OriginalQuadraticLower (halfSide)
open PerturbationSymmetry (squareConfig)
open scoped Topology ENNReal

def error (L : ℕ) : ℝ := 11*(L : ℝ)^2*(1/2 : ℝ)^L
def cleanup (L : ℕ) : ℝ := ((L : ℝ)+2)*(4*L+2)
def slope (L : ℕ) : ℝ := (6*(L : ℝ)+6)*(8*Real.log 2)

theorem finite_certificate {N : ℕ} (hN : 100 ≤ N) (K : ℕ) :
    let L := halfSide N
    ENNReal.ofReal ((K : ℝ)*(1-error L-cleanup L/cost L-
      slope L/cost L*((K : ℝ)+1)/2)) ≤ OriginalRecoveryProfile.expectedRecovery (squareConfig N) := by
  let L := halfSide N
  have hL : 40 ≤ L := by dsimp [L,halfSide]; omega
  have hrad : 0 < radius L := by unfold radius; omega
  have hC : 0 < cost L := by unfold cost; positivity
  apply integrate_envelope
  intro k
  change 1-error L-cleanup L/cost L-slope L/cost L*((k : ℝ)+1) ≤ survival N k
  by_cases h : 2*k<N
  · have he : {η | (k : ℕ∞) < HomogeneousRecoveryTime.synchronous (squareConfig N) η} = Set.univ :=
      Set.eq_univ_of_forall (pathwise_survival h)
    simp only [survival,he,probReal_univ]
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp [error,cleanup,slope]
    linarith [show (0 : ℝ) ≤ 11*(L : ℝ)^2*(1/2 : ℝ)^L by positivity,
      show (0 : ℝ) ≤ ((L : ℝ)+2)*(4*L+2)/cost L by positivity,
      show (0 : ℝ) ≤ (6*(L : ℝ)+6)*(8*Real.log 2)/cost L*((k : ℝ)+1) by positivity]
  · have hk : L ≤ k+1 := by dsimp [L,halfSide]; omega
    have herr : (6/5 : ℝ)*(ClippedSquareCoordinates.parameter L+2 : ℝ)^2*((2 : ℝ)⁻¹)^(k+1) ≤ error L := by
      have hd : (ClippedSquareCoordinates.parameter L+2 : ℝ) ≤ 3*(L : ℝ) := by
        exact_mod_cast (ClippedSquareCoordinates.parameter_side L (by omega)).le.trans (show 2*L+1 ≤ 3*L by omega)
      have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ (ClippedSquareCoordinates.parameter L+2 : ℝ)) hd
      have hcoef : (6/5 : ℝ)*(ClippedSquareCoordinates.parameter L+2 : ℝ)^2 ≤ 11*(L : ℝ)^2 := by nlinarith [sq_nonneg (L : ℝ)]
      have hpow := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ ≤ 1) hk
      simpa only [error,one_div] using mul_le_mul hcoef hpow (by positivity) (by positivity)
    have hb := extinction_budget (N := N) (k := k) hN
    change cost L * _ ≤ (6*(L : ℝ)+6)*SchedulingFailure.time k+cleanup L at hb
    have ht : (6*(L : ℝ)+6)*SchedulingFailure.time k = slope L*((k : ℝ)+1) := by
      unfold SchedulingFailure.time slope; push_cast; ring
    rw [ht] at hb
    have hmul := mul_le_mul_of_nonneg_left herr hC.le
    field_simp [hC.ne']
    nlinarith only [hb,hmul]

abbrev z (N : ℕ) := (1 : ℝ)/N
abbrev ell (N : ℕ) := (halfSide N : ℝ)*z N
abbrev rad (N : ℕ) := (radius (halfSide N) : ℝ)*z N

private theorem scaled_count {f : ℕ → ℕ} {a C : ℝ}
    (hf : ∀ᶠ N : ℕ in atTop, a*N-C ≤ f N ∧ (f N : ℝ) ≤ a*N) :
    Tendsto (fun N => (f N : ℝ)*z N) atTop (𝓝 a) := by
  have hz := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hlo : Tendsto (fun N : ℕ => a-C*z N) atTop (𝓝 a) := by
    simpa [z] using (tendsto_const_nhds (x := a) (f := (atTop : Filter ℕ))).sub (hz.const_mul C)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo (tendsto_const_nhds (x := a))
  · filter_upwards [hf,eventually_ge_atTop 1] with N h hn
    have hp : (0 : ℝ) < N := by exact_mod_cast hn
    dsimp [z]
    rw [mul_one_div,mul_one_div,le_div_iff₀ hp]
    field_simp [hp.ne']
    nlinarith [mul_le_mul_of_nonneg_right h.1 hp.le]
  · filter_upwards [hf,eventually_ge_atTop 1] with N h hn
    have hp : (0 : ℝ) < N := by exact_mod_cast hn
    simpa only [z,mul_one_div,div_le_iff₀ hp] using h.2

theorem ell_limit : Tendsto ell atTop (𝓝 (1/2)) := by
  apply scaled_count (C := 2)
  filter_upwards [eventually_ge_atTop 1] with N hn
  have h1 : N ≤ 2*halfSide N+2 := by unfold halfSide; omega
  have h2 : 2*halfSide N ≤ N := by unfold halfSide; omega
  have h1' : (N : ℝ) ≤ 2*(halfSide N : ℝ)+2 := by exact_mod_cast h1
  have h2' : 2*(halfSide N : ℝ) ≤ N := by exact_mod_cast h2
  constructor <;> linarith

theorem rad_limit : Tendsto rad atTop (𝓝 (1/20)) := by
  apply scaled_count (C := 3)
  filter_upwards [eventually_ge_atTop 40] with N hn
  have h1 : N ≤ 20*radius (halfSide N)+41 := by unfold radius halfSide; omega
  have h2 : 20*radius (halfSide N) ≤ N := by unfold radius halfSide; omega
  have h1' : (N : ℝ) ≤ 20*(radius (halfSide N) : ℝ)+41 := by exact_mod_cast h1
  have h2' : 20*(radius (halfSide N) : ℝ) ≤ N := by exact_mod_cast h2
  constructor <;> linarith

private theorem error_limit : Tendsto (fun N => error (halfSide N)) atTop (𝓝 0) := by
  have hL : Tendsto halfSide atTop atTop := tendsto_atTop.mpr fun n => by
    filter_upwards [eventually_ge_atTop (2*n+2)] with N h
    unfold halfSide; omega
  simpa [error,mul_assoc] using ((tendsto_pow_const_mul_const_pow_of_lt_one 2
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)).comp hL).const_mul 11

def horizonCoefficient : ℝ := 1/(1152000*Real.log 2)
private def horizon (N : ℕ) : ℕ := ⌊horizonCoefficient*(N : ℝ)^2⌋₊
private abbrev q (N : ℕ) : ℝ := (horizon N : ℝ)*(z N)^2
abbrev H (N : ℕ) : ℝ := rad N*(rad N+z N)*(rad N+2*z N)/6
abbrev B (N : ℕ) : ℝ := (ell N+2*z N)*(4*ell N+2*z N)*z N
abbrev D (N : ℕ) : ℝ := (6*ell N+6*z N)*(8*Real.log 2)
private def cert (N : ℕ) : ℝ := q N*(1-error (halfSide N)-B N/H N-D N/H N*(q N+(z N)^2)/2)

private theorem horizon_pos : 0 < horizonCoefficient := by
  unfold horizonCoefficient; positivity

private theorem q_limit : Tendsto q atTop (𝓝 horizonCoefficient) := by
  have hz := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hlo : Tendsto (fun N : ℕ => horizonCoefficient-(z N)^2) atTop (𝓝 horizonCoefficient) := by
    simpa [z] using (tendsto_const_nhds (x := horizonCoefficient) (f := (atTop : Filter ℕ))).sub (hz.pow 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo (tendsto_const_nhds (x := horizonCoefficient))
  · filter_upwards [eventually_ge_atTop 1] with N hn
    have hp : (0 : ℝ) < N := by exact_mod_cast hn
    have h := Nat.lt_floor_add_one (horizonCoefficient*(N : ℝ)^2)
    change _ ≤ (⌊horizonCoefficient*(N : ℝ)^2⌋₊ : ℝ)*(1/(N : ℝ))^2
    dsimp [z]
    field_simp [hp.ne']
    linarith
  · filter_upwards [eventually_ge_atTop 1] with N hn
    have hp : (0 : ℝ) < N := by exact_mod_cast hn
    have h := Nat.floor_le (mul_nonneg horizon_pos.le (sq_nonneg (N : ℝ)))
    change (⌊horizonCoefficient*(N : ℝ)^2⌋₊ : ℝ)*(1/(N : ℝ))^2 ≤ _
    field_simp [hp.ne']
    linarith

private theorem cert_limit : Tendsto cert atTop (𝓝 (1/(2304000*Real.log 2))) := by
  have hz : Tendsto z atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hh : Tendsto H atTop (𝓝 (1/48000)) := by
    convert ((rad_limit.mul (rad_limit.add hz)).mul (rad_limit.add (hz.const_mul 2))).div_const 6 using 1; norm_num
  have hb : Tendsto B atTop (𝓝 0) := by
    convert (((ell_limit.add (hz.const_mul 2)).mul ((ell_limit.const_mul 4).add (hz.const_mul 2))).mul hz) using 1; norm_num
  have hd : Tendsto D atTop (𝓝 (24*Real.log 2)) := by
    convert (((ell_limit.const_mul 6).add (hz.const_mul 6)).mul_const (8*Real.log 2)) using 1; ring_nf
  have hv := q_limit.mul (((tendsto_const_nhds (x := (1 : ℝ))).sub error_limit).sub (hb.div hh (by norm_num)) |>.sub
    (((hd.div hh (by norm_num)).mul (q_limit.add (hz.pow 2))).div_const 2))
  convert hv using 1
  · rfl
  unfold horizonCoefficient
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp [hl]; ring

private theorem cert_valid {N : ℕ} (hn : 100 ≤ N) :
    ENNReal.ofReal (cert N * (N : ℝ)^2) ≤ OriginalRecoveryProfile.expectedRecovery (squareConfig N) := by
  have hp : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hr : 0 < radius (halfSide N) := by unfold radius halfSide; omega
  have hc : (radius (halfSide N) : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have h1 : (radius (halfSide N) : ℝ)+1 ≠ 0 := by positivity
  have h2 : (radius (halfSide N) : ℝ)+2 ≠ 0 := by positivity
  have hH : H N = cost (halfSide N)/(N : ℝ)^3 := by dsimp [H,rad,z,cost]; field_simp [hp]
  have hB : B N = cleanup (halfSide N)/(N : ℝ)^3 := by dsimp [B,ell,z,cleanup]; field_simp [hp]
  have hD : D N = slope (halfSide N)/(N : ℝ) := by dsimp [D,ell,z,slope]; field_simp [hp]
  have hcost : cost (halfSide N) ≠ 0 := by unfold cost; positivity
  apply le_trans _ (finite_certificate hn (horizon N))
  apply ENNReal.ofReal_le_ofReal
  rw [cert,hH,hB,hD]
  dsimp only [q,z]
  apply le_of_eq
  field_simp [hp,hcost]

/-- All coefficients strictly below the displayed asymptotic lower coefficient hold eventually. -/
theorem eventual_lower {c : ℝ} (hc : c < 1/(2304000*Real.log 2)) :
    ∀ᶠ N : ℕ in atTop, ENNReal.ofReal (c*(N : ℝ)^2) ≤ OriginalRecoveryProfile.expectedRecovery (squareConfig N) := by
  filter_upwards [cert_limit.eventually (lt_mem_nhds hc),eventually_ge_atTop 100] with N h hn
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h.le (sq_nonneg _))).trans (cert_valid hn)

end MathResearchLower.Asymptotic
