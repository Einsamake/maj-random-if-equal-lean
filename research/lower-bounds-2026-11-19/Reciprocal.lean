module
public import FastTail
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchLower.Packing
open MathResearchAnalysis MeasureTheory Filter
open PerturbationSymmetry (squareConfig)
open scoped Topology ENNReal

theorem subquadratic_vanishes (k : ℕ → ℕ)
    (hk : Tendsto (fun N : ℕ => (k N : ℝ)/(N : ℝ)^2) atTop (𝓝 0)) :
    Tendsto (fun N => cdf N (k N)) atTop (𝓝 0) := by
  have hz := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
  have h0 : Tendsto (fun N : ℕ => ((k N : ℝ)+1)/(N : ℝ)^2) atTop (𝓝 0) := by
    simpa only [add_div,div_pow,one_pow,zero_pow (by decide : 2 ≠ 0),add_zero] using hk.add hz
  have hpos : Tendsto (fun N : ℕ => ((k N : ℝ)+1)/(N : ℝ)^2) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨h0,?_⟩
    filter_upwards [eventually_ge_atTop 1] with N h
    exact div_pos (by positivity) (sq_pos_of_pos (by exact_mod_cast h))
  have hcoef : 0 < Real.log 2/64000000 := by positivity
  have hbig := hpos.inv_tendsto_nhdsGT_zero.const_mul_atTop hcoef
  have hexp := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hbig).const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hexp)
    (fun _ => measureReal_nonneg)
  intro N
  apply le_trans (exponential_fast_tail N (k N))
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  apply le_of_eq
  field_simp [show (k N : ℝ)+1 ≠ 0 by positivity]

def coefficient : ℝ := Real.log 2/128000000

/-- The reciprocal is set to zero on the infinite-time event. -/
def inverseTime (N : ℕ) (t : ℕ∞) : ℝ :=
  if t=⊤ then 0 else coefficient*(N : ℝ)^2/((t.toNat : ℝ)+1)

def inverseSample (N : ℕ) (η : InfiniteGridRandomDynamics.Sample) : ℝ :=
  inverseTime N (InfiniteGridRecoveryTime.synchronous (squareConfig N) η)

theorem inverse_nonnegative (N : ℕ) (η : InfiniteGridRandomDynamics.Sample) : 0 ≤ inverseSample N η := by
  unfold inverseSample inverseTime coefficient
  split <;> positivity

theorem inverse_measurable (N : ℕ) : Measurable (inverseSample N) :=
  (measurable_of_countable (inverseTime N)).comp (InfiniteGridRecoveryTime.synchronous_measurable _)

theorem inverse_tail (N : ℕ) {t : ℝ} (ht : 0<t) :
    InfiniteGridRandomDynamics.measure.real {η | t < inverseSample N η} ≤ 2*Real.exp (-2*t) := by
  let R := coefficient*(N : ℝ)^2/t
  have hR0 : 0 ≤ R := by dsimp [R,coefficient]; positivity
  have hf : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le hR0
  have himp (η : InfiniteGridRandomDynamics.Sample) (h : t < inverseSample N η) :
      ∃ s : ℕ, InfiniteGridRecoveryTime.synchronous (squareConfig N) η = s ∧ s+1 ≤ ⌊R⌋₊ := by
    cases he : InfiniteGridRecoveryTime.synchronous (squareConfig N) η using ENat.recTopCoe with
    | top => simp [inverseSample,inverseTime,he] at h; linarith
    | coe s =>
      refine ⟨s,rfl,Nat.le_floor ?_⟩
      simp [inverseSample,inverseTime,he] at h
      have h1 := (lt_div_iff₀ (by positivity)).mp h
      apply (le_div_iff₀ ht).mpr
      push_cast
      linarith
  by_cases hr : 1 ≤ ⌊R⌋₊
  · let k := ⌊R⌋₊-1
    have he : k+1=⌊R⌋₊ := by dsimp [k]; omega
    have hsub : {η | t < inverseSample N η} ⊆
        {η | InfiniteGridRecoveryTime.synchronous (squareConfig N) η ≤ (k : ℕ∞)} := by
      intro η h
      obtain ⟨s,hs,hle⟩ := himp η h
      rw [Set.mem_ofPred_eq,hs,ENat.natCast_le_natCast]
      omega
    apply (measureReal_mono hsub).trans ((exponential_fast_tail N k).trans ?_)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have hk : (k : ℝ)+1 ≤ R := by simpa only [← he,Nat.cast_add,Nat.cast_one] using hf
    have hprod := (le_div_iff₀ ht).mp hk
    unfold coefficient at hprod
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hprod]
  · have he : {η | t < inverseSample N η} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro η h
      obtain ⟨s,_,hs⟩ := himp η h
      omega
    rw [he,measureReal_empty]
    positivity

/-- An inverse exponential moment for the original full-square recovery, uniformly in side length. -/
theorem inverse_exponential_moment (N : ℕ) :
    (∫⁻ η, ENNReal.ofReal (Real.exp (inverseSample N η)) ∂InfiniteGridRandomDynamics.measure) ≤ 3 := by
  let μ := InfiniteGridRandomDynamics.measure
  let Y := inverseSample N
  have hn : ∀ᵐ η ∂μ, 0 ≤ Y η := Eventually.of_forall (inverse_nonnegative N)
  have hl := lintegral_comp_eq_lintegral_meas_lt_mul (g := Real.exp) μ hn (inverse_measurable N).aemeasurable
    (fun t _ => Real.continuous_exp.intervalIntegrable 0 t) (Eventually.of_forall fun t => (Real.exp_pos t).le)
  have hb : (∫⁻ t in Set.Ioi (0 : ℝ), μ {η | t<Y η}*ENNReal.ofReal (Real.exp t)) ≤
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (2*Real.exp (-t)) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
    rw [← ofReal_measureReal (measure_ne_top μ _),← ENNReal.ofReal_mul measureReal_nonneg]
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_right (inverse_tail N ht) (Real.exp_pos t).le
    calc
      _ ≤ _ := h
      _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
  have hval : (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (2*Real.exp (-t))) = 2 := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_const_mul,integral_exp_neg_Ioi_zero]
      norm_num
    · exact (integrableOn_exp_neg_Ioi 0).const_mul 2
    · exact Eventually.of_forall (fun t => by positivity)
  have h1 : (∫⁻ η, ENNReal.ofReal (Real.exp (Y η)-1) ∂μ) ≤ 2 := by
    simpa only [integral_exp,Real.exp_zero] using hl.trans_le (hb.trans_eq hval)
  change (∫⁻ η, ENNReal.ofReal (Real.exp (Y η)) ∂μ) ≤ 3
  have he (η) : ENNReal.ofReal (Real.exp (Y η)) = 1+ENNReal.ofReal (Real.exp (Y η)-1) := by
    have hy : 1 ≤ Real.exp (Y η) := Real.one_le_exp (inverse_nonnegative N η)
    rw [← ENNReal.ofReal_one,← ENNReal.ofReal_add (by norm_num) (by linarith : 0 ≤ Real.exp (Y η)-1)]
    congr 1; ring
  simp_rw [he]
  rw [lintegral_add_left measurable_const]
  simp only [lintegral_const,measure_univ,mul_one]
  calc
    _ ≤ (1 : ℝ≥0∞)+2 := add_le_add le_rfl h1
    _ = 3 := by norm_num

end MathResearchLower.Packing
