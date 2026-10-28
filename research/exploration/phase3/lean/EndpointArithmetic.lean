module
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.EndpointArithmetic
open Set

def response (z : Real) : Real :=
  1-(7/3 : Real)*z+(3/2 : Real)*z^2-(1/6 : Real)*z^4

def checkDecay : Real := Real.exp (-(21/19 : Real)*Real.log 2)

theorem response_hasDerivAt (z : Real) :
    HasDerivAt response (-(1-z)*(7-2*z-2*z^2)/3) z := by
  have h := (((hasDerivAt_const z (1 : Real)).sub
    ((hasDerivAt_id z).const_mul (7/3 : Real))).add
    (((hasDerivAt_id z).fun_pow 2).const_mul (3/2 : Real))).sub
    (((hasDerivAt_id z).fun_pow 4).const_mul (1/6 : Real))
  convert h using 1
  · ext w
    simp only [response, Pi.sub_apply, Pi.add_apply, id_eq]
  · norm_num
    ring

theorem response_antitone : AntitoneOn response (Icc 0 1) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    ((continuous_iff_continuousAt.mpr (fun z =>
      (response_hasDerivAt z).continuousAt)).continuousOn)
    (fun z _ => (response_hasDerivAt z).hasDerivWithinAt)
  intro z hz
  have hm : z ∈ Icc (0 : Real) 1 := interior_subset hz
  have hs : z^2 ≤ 1 := by
    nlinarith [hm.1,hm.2,mul_nonneg hm.1 (sub_nonneg.mpr hm.2)]
  have hb : 0 ≤ 7-2*z-2*z^2 := by nlinarith [hm.2]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr hm.2)) hb)
    (by norm_num)

theorem checkDecay_nonnegative : 0 ≤ checkDecay := Real.exp_nonneg _

theorem checkDecay_le_one : checkDecay ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
    (Real.log_nonneg (by norm_num : (1 : Real) ≤ 2))

theorem checkDecay_pow : checkDecay^19 = (1/2 : Real)^21 := by
  unfold checkDecay
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (19 : Real)*(-(21/19 : Real)*Real.log 2) =
    (21 : Real)*(-Real.log 2) by ring]
  rw [show (21 : Real)*(-Real.log 2) = (21 : Nat)*(-Real.log 2) by norm_num]
  rw [Real.exp_nat_mul,Real.exp_neg,Real.exp_log (by norm_num : (0 : Real)<2)]
  norm_num

theorem rational_lower_power : (929/2000 : Real)^19 ≤ (1/2 : Real)^21 := by
  norm_num

theorem rational_lower_checkDecay : (929/2000 : Real) ≤ checkDecay := by
  apply le_of_pow_le_pow_left₀ (n := 19) (by norm_num) checkDecay_nonnegative
  rw [checkDecay_pow]
  exact rational_lower_power

theorem response_at_rational : response (929/2000) =
    (7425545410773/32000000000000 : Real) := by norm_num [response]

theorem response_checkDecay_bound : response checkDecay ≤
    (7425545410773/32000000000000 : Real) := by
  rw [← response_at_rational]
  exact response_antitone (by norm_num)
    ⟨checkDecay_nonnegative,checkDecay_le_one⟩ rational_lower_checkDecay

theorem response_checkDecay_lt : response checkDecay < (233/1000 : Real) :=
  response_checkDecay_bound.trans_lt (by norm_num)

end MathExploration.EndpointArithmetic

#print axioms MathExploration.EndpointArithmetic.response
#print axioms MathExploration.EndpointArithmetic.checkDecay
#print axioms MathExploration.EndpointArithmetic.response_hasDerivAt
#print axioms MathExploration.EndpointArithmetic.response_antitone
#print axioms MathExploration.EndpointArithmetic.checkDecay_nonnegative
#print axioms MathExploration.EndpointArithmetic.checkDecay_le_one
#print axioms MathExploration.EndpointArithmetic.checkDecay_pow
#print axioms MathExploration.EndpointArithmetic.rational_lower_power
#print axioms MathExploration.EndpointArithmetic.rational_lower_checkDecay
#print axioms MathExploration.EndpointArithmetic.response_at_rational
#print axioms MathExploration.EndpointArithmetic.response_checkDecay_bound
#print axioms MathExploration.EndpointArithmetic.response_checkDecay_lt
