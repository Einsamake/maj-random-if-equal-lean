module
public import MathResearchAnalysis.SyncLowerScale
public import MathResearchAnalysis.MixedHeatDecay
public import Mathlib.Tactic
set_option autoImplicit false
/-! Explicit upper-comparison scales in the original side-N parameter.
These are deterministic numerical bounds, not recovery-probability inputs. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.SyncUpperScale
open ClippedSquareCoordinates (parameter)

/-- The scheduling layer budget, expressed in the original square side. -/
def layers (N : Nat) : Nat := 1296*N^2

/-- The actual synchronous horizon in the proved clock comparison. -/
def block (N : Nat) : Nat := 2*SchedulingFailure.rankThreshold (layers N)+1

theorem original_side (N : Nat) (hN : 2≤N) : N-2+2=N := by omega

theorem auxiliary_side (N : Nat) (hN : 1≤N) : parameter (4*N)+2=8*N+1 := by
  unfold parameter
  omega

theorem mixingTime_le_layers (N : Nat) (hN : 1≤N) :
    MixedHeatDecay.mixingTime (4*N) ≤ (layers N : Real) := by
  have hs : (parameter (4*N)+2 : Real)=8*(N : Real)+1 := by
    exact_mod_cast auxiliary_side N hN
  have hNr : (1 : Real)≤N := by exact_mod_cast hN
  unfold MixedHeatDecay.mixingTime layers
  rw [hs]
  push_cast
  nlinarith [sq_nonneg ((N : Real)-1)]

theorem log_two_ge_half : (1/2 : Real)≤Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (x := (2 : Real)) (by norm_num)
  norm_num at h
  exact h

theorem layers_le_scheduling_time (N : Nat) :
    (layers N : Real) ≤ SchedulingFailure.time (layers N) := by
  have hk : (0 : Real) ≤ ((layers N+1 : Nat) : Real) := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_right log_two_ge_half hk
  unfold SchedulingFailure.time
  push_cast at hm ⊢
  nlinarith

theorem mixingTime_le_scheduling_time (N : Nat) (hN : 1≤N) :
    MixedHeatDecay.mixingTime (4*N) ≤ SchedulingFailure.time (layers N) :=
  (mixingTime_le_layers N hN).trans (layers_le_scheduling_time N)

theorem layers_succ_ge_side (N : Nat) : N≤layers N+1 := by
  unfold layers
  nlinarith

/-- The scheduling error uses the true original finite side (N-2)+2=N,
not the larger auxiliary square side. -/
theorem scheduling_error_le_eighth (N : Nat) (hN : 16≤N) :
    ((6 : Real)/5)*(N-2+2 : Nat)^2*((2 : Real)⁻¹)^(layers N+1) ≤ (1/8 : Real) := by
  have hside := original_side N (by omega : 2≤N)
  rw [hside]
  have hpow : ((2 : Real)⁻¹)^(layers N+1) ≤ ((2 : Real)⁻¹)^N :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (layers_succ_ge_side N)
  have hexp := SyncLowerScale.square_exponential_bound N hN
  apply (mul_le_mul_of_nonneg_left hpow (by positivity)).trans
  rw [inv_pow, ← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : (0 : Real)<2^N)).mpr
  nlinarith

theorem block_positive (N : Nat) : 0<block N := by unfold block; omega

theorem block_le_quadratic (N : Nat) (hN : 1≤N) : block N≤332033*N^2 := by
  unfold block SchedulingFailure.rankThreshold layers
  nlinarith

end MathResearchAnalysis.SyncUpperScale
