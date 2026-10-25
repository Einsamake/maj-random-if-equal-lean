module
public import MathResearchAnalysis.SchedulingFailure
public import MathResearchAnalysis.PhysicalWeightedDrift
set_option autoImplicit false
/-! Explicit deterministic scales for the actual clock-to-synchronous comparison. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.SyncLowerScale
/-- Number of completed comparison layers. -/
def quotient (L : Nat) : Nat := L ^ 2 / 196608000
/-- The actual integer synchronous horizon. -/
def rounds (L : Nat) : Nat := quotient L - 1

theorem quotient_ge_side (L : Nat) (hL : 196608000 ≤ L) : L ≤ quotient L := by
  unfold quotient
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 196608000)).mpr
  nlinarith

theorem quotient_positive (L : Nat) (hL : 196608000 ≤ L) : 0 < quotient L := by
  have h := quotient_ge_side L hL
  omega

theorem rounds_succ (L : Nat) (hL : 196608000 ≤ L) : rounds L + 1 = quotient L := by
  unfold rounds
  have h := quotient_positive L hL
  omega

theorem quotient_mul_le_square (L : Nat) : quotient L * 196608000 ≤ L ^ 2 := by
  exact Nat.div_mul_le_self (L ^ 2) 196608000

theorem square_lt_quotient_succ (L : Nat) : L ^ 2 < (quotient L + 1) * 196608000 := by
  have hm := Nat.mod_lt (L ^ 2) (by norm_num : 0 < 196608000)
  have hd := Nat.mod_add_div (L ^ 2) 196608000
  unfold quotient
  omega

theorem rounds_lower_bound (L : Nat) (hL : 196608000 ≤ L) :
    (L : Real)^2 / 393216000 ≤ (rounds L : Real) := by
  have hq := quotient_ge_side L hL
  have hsucc := rounds_succ L hL
  have hd := square_lt_quotient_succ L
  have hq2 : 2 ≤ quotient L := by omega
  have hr : L^2 ≤ rounds L * 393216000 := by nlinarith
  have hr' : (L : Real)^2 ≤ (rounds L : Real) * 393216000 := by exact_mod_cast hr
  linarith

theorem scheduling_time_le_horizon (L : Nat) (hL : 196608000 ≤ L) :
    SchedulingFailure.time (rounds L) ≤ (PhysicalWeightedDrift.quadraticHorizon L : Real) := by
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h
    exact h
  have hq := quotient_mul_le_square L
  have hq' : (quotient L : Real) * 196608000 ≤ (L : Real)^2 := by exact_mod_cast hq
  have hq0 : (0 : Real) ≤ quotient L := Nat.cast_nonneg _
  unfold SchedulingFailure.time
  rw [rounds_succ L hL]
  change 8 * Real.log 2 * (quotient L : Real) ≤ (L : Real)^2 / 12288000
  have hm := mul_le_mul_of_nonneg_right hlog hq0
  nlinarith

theorem square_exponential_bound (L : Nat) (hL : 16 ≤ L) :
    64 * (L : Real)^2 ≤ (2 : Real)^L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ (2 : Real)]
      have hn' : (16 : Real) ≤ n := by exact_mod_cast hn
      push_cast
      nlinarith [sq_nonneg ((n : Real)-2)]

theorem scheduling_error_le_quarter (L : Nat) (hL : 196608000 ≤ L) :
    ((6 : Real)/5) * (ClippedSquareCoordinates.parameter L + 2 : Real)^2 *
      ((2 : Real)⁻¹)^(rounds L+1) ≤ (1/4 : Real) := by
  have hq := quotient_ge_side L hL
  have hpow : ((2 : Real)⁻¹)^(quotient L) ≤ ((2 : Real)⁻¹)^L :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hq
  have hexp := square_exponential_bound L (by omega)
  have hs : (ClippedSquareCoordinates.parameter L + 2 : Real) = 2*(L : Real)+1 := by
    have he := ClippedSquareCoordinates.parameter_side L (by omega : 1 ≤ L)
    have he' : (ClippedSquareCoordinates.parameter L : Real)+2 = 2*(L : Real)+1 := by
      exact_mod_cast he
    exact he'
  have hL' : (1 : Real) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hside : (2*(L : Real)+1)^2 ≤ 9*(L : Real)^2 := by nlinarith
  rw [rounds_succ L hL, hs]
  apply (mul_le_mul_of_nonneg_left hpow (by positivity)).trans
  rw [inv_pow, ← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : (0 : Real) < 2^L)).mpr
  nlinarith
end MathResearchAnalysis.SyncLowerScale

