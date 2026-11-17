module

public import MathResearchAnalysis.OriginalQuadraticUpper
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Tactic

set_option autoImplicit false

/-! Distributional consequences of the original recovery tail.  The time has
codomain ENat throughout.  Its finite representative is used only after the
genuine geometric tail has proved almost-sure finiteness. -/

@[expose] public noncomputable section

namespace MathResearchRevision.RecoveryMoments

open MeasureTheory
open scoped ENNReal BigOperators

universe u

theorem nat_le_block_successor (t b : Nat) (hb : 0 < b) :
    t ≤ ((t - 1) / b + 1) * b := by
  have h := Nat.mod_lt (t-1) hb
  have he := Nat.mod_add_div (t-1) b
  rw [Nat.mul_comm b] at he
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem block_predecessor_lt (t b : Nat) (ht : 0 < t) :
    ((t-1)/b)*b < t := by
  have h := Nat.div_mul_le_self (t-1) b
  omega

theorem monotone_weight_envelope (F : Nat → ℝ≥0∞) (hF : Monotone F)
    (t b : Nat) (hb : 0 < b) :
    F t ≤ F 0 + ∑' j : Nat, if j*b<t then F ((j+1)*b) else 0 := by
  by_cases ht : t=0
  · simp [ht]
  · have ht' : 0<t := Nat.pos_of_ne_zero ht
    have hle := hF (nat_le_block_successor t b hb)
    have hs := @ENNReal.le_tsum Nat
      (fun j => if j*b<t then F ((j+1)*b) else 0) ((t-1)/b)
    rw [ite_eq_left (block_predecessor_lt t b ht')] at hs
    exact hle.trans (hs.trans (le_add_left le_rfl))

theorem lintegral_monotone_weight_le {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → ℕ∞) (hT : Measurable T) (b : Nat) (hb : 0 < b)
    (hTail : ∀ j : Nat, μ {ω | ((j*b : Nat) : ℕ∞)<T ω} ≤ (1/2 : ℝ≥0∞)^j)
    (F : Nat → ℝ≥0∞) (hF : Monotone F) :
    (∫⁻ ω, F (T ω).toNat ∂μ) ≤
      F 0 + ∑' j : Nat, F ((j+1)*b) * (1/2 : ℝ≥0∞)^j := by
  let W : Nat → Ω → ℝ≥0∞ := fun j ω =>
    if ((j*b : Nat) : ℕ∞)<T ω then F ((j+1)*b) else 0
  have hm (j : Nat) : Measurable (W j) := by
    have he : W j = {ω | ((j*b : Nat) : ℕ∞)<T ω}.indicator
        (fun _ => F ((j+1)*b)) := by
      funext ω
      simp [W, Set.indicator]
    rw [he]
    exact measurable_const.indicator
      (MathResearchAnalysis.ExtendedBlockTail.measurableSet_blockTail T hT b j)
  have hpoint : ∀ᵐ ω ∂μ, F (T ω).toNat ≤ F 0 + ∑' j : Nat, W j ω := by
    filter_upwards [MathResearchAnalysis.ExtendedBlockTail.ae_natCast_toNat_eq
      μ T hT b hb hTail] with ω hω
    have h := monotone_weight_envelope F hF (T ω).toNat b hb
    have he : (fun j : Nat => W j ω) =
        (fun j : Nat => if j*b<(T ω).toNat then F ((j+1)*b) else 0) := by
      funext j
      dsimp only [W]
      rw [← hω]
      simp only [ENat.natCast_lt_natCast, ENat.toNat_natCast]
      rfl
    rw [he]
    exact h
  calc
    _ ≤ ∫⁻ ω, F 0 + ∑' j : Nat, W j ω ∂μ := lintegral_mono_ae hpoint
    _ = F 0 + ∑' j : Nat, ∫⁻ ω, W j ω ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_tsum (fun j => (hm j).aemeasurable)]
      simp
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply ENNReal.tsum_le_tsum
      intro j
      have he : W j = {ω | ((j*b : Nat) : ℕ∞)<T ω}.indicator
          (fun _ => F ((j+1)*b)) := by
        funext ω
        simp [W, Set.indicator]
      rw [he, lintegral_indicator_const
        (MathResearchAnalysis.ExtendedBlockTail.measurableSet_blockTail T hT b j)]
      exact mul_le_mul_right (hTail j) _

def polynomialConstant (k : Nat) : ℝ≥0∞ :=
  ∑' j : Nat, ((j+1 : Nat) : ℝ≥0∞)^k * (1/2 : ℝ≥0∞)^j

theorem polynomial_series_summable (k : Nat) :
    Summable (fun j : Nat => ((j+1 : Nat) : Real)^k * (1/2 : Real)^j) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one k
    (by norm_num : ‖(1/2 : Real)‖ < 1)
  have ht := (summable_nat_add_iff 1).mpr hs
  convert ht.mul_left 2 using 1
  funext j
  simp only [pow_succ]
  ring

theorem polynomialConstant_lt_top (k : Nat) : polynomialConstant k < ⊤ := by
  have hs := (polynomial_series_summable k).tsum_ofReal_lt_top
  have he (j : Nat) : ENNReal.ofReal (((j+1 : Nat) : Real)^k * (1/2 : Real)^j) =
      ((j+1 : Nat) : ℝ≥0∞)^k * (1/2 : ℝ≥0∞)^j := by
    rw [ENNReal.ofReal_mul (pow_nonneg (Nat.cast_nonneg _) k),
      ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow (by norm_num : (0 : Real)≤1/2)]
    norm_num [ENNReal.ofReal_div_of_pos]
  simpa only [polynomialConstant, he] using hs

def momentConstant (r : Real) : ℝ≥0∞ :=
  (332033 : ℝ≥0∞)^r * polynomialConstant ⌈r⌉₊

theorem momentConstant_lt_top (r : Real) (hr : 0<r) : momentConstant r < ⊤ := by
  apply ENNReal.mul_lt_top
  · exact ENNReal.rpow_lt_top_of_nonneg hr.le (by norm_num)
  · exact polynomialConstant_lt_top _

theorem lintegral_rpow_le_blocks {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → ℕ∞) (hT : Measurable T) (b : Nat) (hb : 0 < b)
    (hTail : ∀ j : Nat, μ {ω | ((j*b : Nat) : ℕ∞)<T ω} ≤ (1/2 : ℝ≥0∞)^j)
    (r : Real) (hr : 0<r) :
    (∫⁻ ω, (T ω : ℝ≥0∞)^r ∂μ) ≤
      (b : ℝ≥0∞)^r * polynomialConstant ⌈r⌉₊ := by
  have he : (∫⁻ ω, (T ω : ℝ≥0∞)^r ∂μ) =
      ∫⁻ ω, ((T ω).toNat : ℝ≥0∞)^r ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [MathResearchAnalysis.ExtendedBlockTail.ae_natCast_toNat_eq
      μ T hT b hb hTail] with ω hω
    have hc := congrArg ENat.toENNReal hω
    simpa only [ENat.toENNReal_coe] using congrArg (fun x : ℝ≥0∞ => x^r) hc.symm
  rw [he]
  have hm : Monotone (fun t : Nat => (t : ℝ≥0∞)^r) := by
    intro m n hmn
    exact ENNReal.rpow_le_rpow (by exact_mod_cast hmn) hr.le
  have h := lintegral_monotone_weight_le μ T hT b hb hTail
    (fun t : Nat => (t : ℝ≥0∞)^r) hm
  simp only [Nat.cast_zero, ENNReal.zero_rpow_of_pos hr, zero_add] at h
  apply h.trans
  rw [polynomialConstant, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro j
  have hj : (1 : ℝ≥0∞) ≤ ((j+1 : Nat) : ℝ≥0∞) := by exact_mod_cast Nat.le_add_left 1 j
  have hp := ENNReal.rpow_le_rpow_of_exponent_le hj (Nat.le_ceil r)
  rw [ENNReal.rpow_natCast] at hp
  simp only [Nat.cast_mul]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le]
  calc
    ((j+1 : Nat) : ℝ≥0∞)^r * (b : ℝ≥0∞)^r * (1/2 : ℝ≥0∞)^j
      ≤ ((j+1 : Nat) : ℝ≥0∞)^⌈r⌉₊ * (b : ℝ≥0∞)^r * (1/2 : ℝ≥0∞)^j := by
        gcongr
    _ = _ := by ac_rfl

theorem recovery_rpow_le (N : Nat) (hN : 16≤N)
    (g : MathResearchAnalysis.SquareSpin.Config (N-2)) (r : Real) (hr : 0<r) :
    (∫⁻ η, (MathResearchAnalysis.SquareRecoveryTime.synchronous (N-2) g η : ℝ≥0∞)^r
      ∂MathResearchAnalysis.SquareRandomDynamics.measure (N-2)) ≤
        momentConstant r * (N : ℝ≥0∞)^(2*r) := by
  have hb : 0 < MathResearchAnalysis.SyncUpperScale.block N :=
    MathResearchAnalysis.SyncUpperScale.block_positive N
  have h := lintegral_rpow_le_blocks
    (MathResearchAnalysis.SquareRandomDynamics.measure (N-2))
    (MathResearchAnalysis.SquareRecoveryTime.synchronous (N-2) g)
    (MathResearchAnalysis.SquareRecoveryTime.synchronous_measurable (N-2) g)
    (MathResearchAnalysis.SyncUpperScale.block N) hb
    (MathResearchAnalysis.OriginalQuadraticUpper.recovery_block_tail N hN g) r hr
  have hsize : (MathResearchAnalysis.SyncUpperScale.block N : ℝ≥0∞) ≤
      332033*(N : ℝ≥0∞)^2 := by
    exact_mod_cast MathResearchAnalysis.SyncUpperScale.block_le_quadratic N (by omega : 1≤N)
  apply h.trans
  have hp := ENNReal.rpow_le_rpow hsize hr.le
  calc
    _ ≤ (332033*(N : ℝ≥0∞)^2)^r * polynomialConstant ⌈r⌉₊ := by gcongr
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le]
      rw [← ENNReal.rpow_natCast_mul]
      dsimp only [momentConstant]
      push_cast
      ac_rfl

/-- Positive exponential observables retain the value infinity at infinite
time.  In the applications below the scale is positive and lambda > 0. -/
def extendedExp (lambda scale : Real) (t : ℕ∞) : ℝ≥0∞ :=
  if t=⊤ then ⊤ else ENNReal.ofReal (Real.exp (lambda*(t.toNat : Real)/scale))

def expRatio (lambda : Real) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (332033*lambda)) / 2

def expConstant (lambda : Real) : ℝ≥0∞ :=
  1 + ENNReal.ofReal (Real.exp (332033*lambda)) * (1-expRatio lambda)⁻¹

theorem expRatio_lt_one (lambda : Real) (hl : 332033*lambda<Real.log 2) :
    expRatio lambda<1 := by
  have h : Real.exp (332033*lambda)<2 := by
    simpa only [Real.exp_log (by norm_num : (0 : Real)<2)] using Real.exp_lt_exp.mpr hl
  unfold expRatio
  rw [show (2 : ℝ≥0∞)=ENNReal.ofReal (2 : Real) by norm_num,
    ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real)<2)]
  apply ENNReal.ofReal_lt_one.mpr
  linarith

theorem expConstant_lt_top (lambda : Real) (hl : 332033*lambda<Real.log 2) :
    expConstant lambda<⊤ := by
  unfold expConstant
  apply ENNReal.add_lt_top.mpr
  constructor
  · norm_num
  · apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    exact ENNReal.inv_lt_top.mpr (tsub_pos_iff_lt.mpr (expRatio_lt_one lambda hl))

theorem exponential_weight_series (c : Real) :
    (∑' j : Nat, ENNReal.ofReal (Real.exp (c*(j+1))) * (1/2 : ℝ≥0∞)^j) =
      ENNReal.ofReal (Real.exp c) * (1-ENNReal.ofReal (Real.exp c)/2)⁻¹ := by
  have he (j : Nat) : ENNReal.ofReal (Real.exp (c*(j+1))) * (1/2 : ℝ≥0∞)^j =
      ENNReal.ofReal (Real.exp c) * (ENNReal.ofReal (Real.exp c)/2)^j := by
    have hr : Real.exp (c*(j+1)) = Real.exp c * (Real.exp c)^j := by
      rw [show c*(j+1 : Real) = (j : Real)*c+c by ring, Real.exp_add,
        Real.exp_nat_mul]
      ring
    rw [hr, ENNReal.ofReal_mul (Real.exp_nonneg c),
      ENNReal.ofReal_pow (Real.exp_nonneg c)]
    simp only [div_eq_mul_inv, mul_pow, one_mul]
    ac_rfl
  simp_rw [he]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

theorem lintegral_extendedExp_le {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → ℕ∞) (hT : Measurable T) (b : Nat) (hb : 0 < b)
    (hTail : ∀ j : Nat, μ {ω | ((j*b : Nat) : ℕ∞)<T ω} ≤ (1/2 : ℝ≥0∞)^j)
    (lambda scale : Real) (hl : 0≤lambda) (hs : 0<scale)
    (hsize : (b : Real)≤332033*scale) :
    (∫⁻ ω, extendedExp lambda scale (T ω) ∂μ) ≤ expConstant lambda := by
  have he : (∫⁻ ω, extendedExp lambda scale (T ω) ∂μ) =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (lambda*((T ω).toNat : Real)/scale)) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [MathResearchAnalysis.ExtendedBlockTail.ae_lt_top
      μ T hT b hb hTail] with ω hω
    simp only [extendedExp, ite_eq_right hω.ne]
  rw [he]
  have hm : Monotone (fun t : Nat => ENNReal.ofReal (Real.exp (lambda*(t : Real)/scale))) := by
    intro m n hmn
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hmn) hl) hs.le
  have h := lintegral_monotone_weight_le μ T hT b hb hTail
    (fun t : Nat => ENNReal.ofReal (Real.exp (lambda*(t : Real)/scale))) hm
  simp only [Nat.cast_zero, mul_zero, zero_div, Real.exp_zero, ENNReal.ofReal_one] at h
  apply h.trans
  unfold expConstant expRatio
  rw [← exponential_weight_series]
  apply add_le_add le_rfl
  apply ENNReal.tsum_le_tsum
  intro j
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hratio : (b : Real)/scale≤332033 := (div_le_iff₀ hs).mpr hsize
  calc
    lambda*(((j+1)*b : Nat) : Real)/scale =
        (lambda*(j+1 : Real))*((b : Real)/scale) := by push_cast; ring
    _ ≤ (lambda*(j+1 : Real))*332033 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

theorem recovery_exponential_le (N : Nat) (hN : 16≤N)
    (g : MathResearchAnalysis.SquareSpin.Config (N-2))
    (lambda : Real) (hl : 0<lambda) :
    (∫⁻ η, extendedExp lambda ((N : Real)^2)
      (MathResearchAnalysis.SquareRecoveryTime.synchronous (N-2) g η)
      ∂MathResearchAnalysis.SquareRandomDynamics.measure (N-2)) ≤ expConstant lambda := by
  apply lintegral_extendedExp_le
    (MathResearchAnalysis.SquareRandomDynamics.measure (N-2))
    (MathResearchAnalysis.SquareRecoveryTime.synchronous (N-2) g)
    (MathResearchAnalysis.SquareRecoveryTime.synchronous_measurable (N-2) g)
    (MathResearchAnalysis.SyncUpperScale.block N)
    (MathResearchAnalysis.SyncUpperScale.block_positive N)
    (MathResearchAnalysis.OriginalQuadraticUpper.recovery_block_tail N hN g) lambda
    ((N : Real)^2) hl.le (by positivity)
  exact_mod_cast MathResearchAnalysis.SyncUpperScale.block_le_quadratic N (by omega : 1≤N)

theorem positive_exponential_interval :
    0 < (1/(4*332033) : Real) ∧ 332033*(1/(4*332033) : Real)<Real.log 2 := by
  have h := MathResearchAnalysis.SyncUpperScale.log_two_ge_half
  constructor
  · norm_num
  · norm_num at h ⊢
    linarith

theorem recovery_ae_finite (N : Nat) (hN : 16≤N)
    (g : MathResearchAnalysis.SquareSpin.Config (N-2)) :
    ∀ᵐ η ∂MathResearchAnalysis.SquareRandomDynamics.measure (N-2),
      MathResearchAnalysis.SquareRecoveryTime.synchronous (N-2) g η < ⊤ :=
  MathResearchAnalysis.ExtendedBlockTail.ae_lt_top
    (MathResearchAnalysis.SquareRandomDynamics.measure (N-2))
    (MathResearchAnalysis.SquareRecoveryTime.synchronous (N-2) g)
    (MathResearchAnalysis.SquareRecoveryTime.synchronous_measurable (N-2) g)
    (MathResearchAnalysis.SyncUpperScale.block N)
    (MathResearchAnalysis.SyncUpperScale.block_positive N)
    (MathResearchAnalysis.OriginalQuadraticUpper.recovery_block_tail N hN g)

theorem recovery_rpow_lt_top (N : Nat) (hN : 16≤N)
    (g : MathResearchAnalysis.SquareSpin.Config (N-2)) (r : Real) (hr : 0<r) :
    (∫⁻ η, (MathResearchAnalysis.SquareRecoveryTime.synchronous (N-2) g η : ℝ≥0∞)^r
      ∂MathResearchAnalysis.SquareRandomDynamics.measure (N-2)) < ⊤ := by
  apply (recovery_rpow_le N hN g r hr).trans_lt
  exact ENNReal.mul_lt_top (momentConstant_lt_top r hr)
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) (by finiteness))

theorem recovery_exponential_lt_top (N : Nat) (hN : 16≤N)
    (g : MathResearchAnalysis.SquareSpin.Config (N-2))
    (lambda : Real) (hl : 0<lambda) (hl' : 332033*lambda<Real.log 2) :
    (∫⁻ η, extendedExp lambda ((N : Real)^2)
      (MathResearchAnalysis.SquareRecoveryTime.synchronous (N-2) g η)
      ∂MathResearchAnalysis.SquareRandomDynamics.measure (N-2)) < ⊤ :=
  (recovery_exponential_le N hN g lambda hl).trans_lt (expConstant_lt_top lambda hl')

#print axioms nat_le_block_successor
#print axioms block_predecessor_lt
#print axioms monotone_weight_envelope
#print axioms lintegral_monotone_weight_le
#print axioms polynomialConstant
#print axioms polynomial_series_summable
#print axioms polynomialConstant_lt_top
#print axioms momentConstant
#print axioms momentConstant_lt_top
#print axioms lintegral_rpow_le_blocks
#print axioms recovery_rpow_le
#print axioms extendedExp
#print axioms expRatio
#print axioms expConstant
#print axioms expRatio_lt_one
#print axioms expConstant_lt_top
#print axioms exponential_weight_series
#print axioms lintegral_extendedExp_le
#print axioms recovery_exponential_le
#print axioms positive_exponential_interval
#print axioms recovery_ae_finite
#print axioms recovery_rpow_lt_top
#print axioms recovery_exponential_lt_top

end MathResearchRevision.RecoveryMoments
