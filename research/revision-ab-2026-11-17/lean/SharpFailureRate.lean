module
public import SharpRecoveryTail
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchRevision.SharpFailureRate
open MathResearchAnalysis MathResearchRevision.SharpRecoveryTail

theorem layers_succ_ge_twice (N : Nat) : N+N≤SyncUpperScale.layers N+1 := by
  unfold SyncUpperScale.layers
  nlinarith

theorem scheduling_le_inv_side (N : Nat) (hN : 16≤N) :
    (12/5 : Real)*(N : Real)^2*((2 : Real)⁻¹)^(SyncUpperScale.layers N+1)≤1/(N : Real) := by
  have hNr : (16 : Real)≤N := by exact_mod_cast hN
  have hNp : (0 : Real)<N := by linarith
  have hExp := SyncLowerScale.square_exponential_bound N hN
  have hExpN : (N : Real)≤(2 : Real)^N := by nlinarith
  have hCubic : 64*(N : Real)^3≤((2 : Real)^N)^2 := by
    nlinarith [mul_le_mul hExp hExpN (by positivity : (0 : Real)≤N)
      (by positivity : (0 : Real)≤(2 : Real)^N)]
  have hPow : ((2 : Real)⁻¹)^(SyncUpperScale.layers N+1)≤((2 : Real)⁻¹)^(N+N) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (layers_succ_ge_twice N)
  calc
    _ ≤ (12/5 : Real)*(N : Real)^2*((2 : Real)⁻¹)^(N+N) :=
      mul_le_mul_of_nonneg_left hPow (by positivity)
    _ ≤ 1/(N : Real) := by
      rw [pow_add, inv_pow]
      apply (le_div_iff₀ hNp).mpr
      have hp : (0 : Real)<(2 : Real)^N := by positivity
      have hcross : (12/5 : Real)*(N : Real)^3≤((2 : Real)^N)^2 := by nlinarith
      field_simp
      nlinarith

/-- An explicit uniform rate; together with nonnegativity it yields O(1/N). -/
theorem failure_le_five_div (N : Nat) (hN : 16≤N) :
    MathResearchRevision.SharpRecoveryTail.failure N≤5/(N : Real) := by
  have hNr : (16 : Real)≤N := by exact_mod_cast hN
  have hNp : (0 : Real)<N := by linarith
  have hfirst : 32/(8*(N : Real)+1)≤4/(N : Real) := by
    apply (div_le_div_iff₀ (by positivity : (0 : Real)<8*(N : Real)+1) hNp).mpr
    linarith
  have hsecond := scheduling_le_inv_side N hN
  calc
    _ ≤ 4/(N : Real)+1/(N : Real) := add_le_add hfirst hsecond
    _ = _ := by ring

theorem failure_isBigO_inv :
    Asymptotics.IsBigO Filter.atTop MathResearchRevision.SharpRecoveryTail.failure
      (fun N : Nat => (N : Real)⁻¹) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨5, ?_⟩
  filter_upwards [Filter.eventually_atTop.mpr ⟨16, fun N hN => hN⟩] with N hN
  simpa only [Real.norm_eq_abs, abs_of_nonneg (failure_nonneg N),
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N : (0 : Real)≤N)), div_eq_mul_inv]
      using failure_le_five_div N hN

end MathResearchRevision.SharpFailureRate

#print axioms MathResearchRevision.SharpFailureRate.layers_succ_ge_twice
#print axioms MathResearchRevision.SharpFailureRate.scheduling_le_inv_side
#print axioms MathResearchRevision.SharpFailureRate.failure_le_five_div
#print axioms MathResearchRevision.SharpFailureRate.failure_isBigO_inv
