module
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

set_option autoImplicit false

/-! A classical parameter-sensitivity counterexample, independent of phase 1.
For the same smooth inlet exp(-t), changing a tank's turnover coefficient need
not preserve an ordering of its concentration at a fixed positive time.
The k=1 branch is included so every real parameter has an actual smooth
trajectory. No claim that the displayed interior parameter is optimal is made.
This is not a novelty or physical-apparatus certification. -/
@[expose] public noncomputable section
namespace MathExploration.ParameterCounterexample
open Set

def inlet (t : Real) : Real := Real.exp (-t)

def response (k t : Real) : Real :=
  if k=1 then t*Real.exp (-t)
  else k/(k-1)*(Real.exp (-t)-Real.exp (-k*t))

def horizon : Real := Real.log 4

theorem inlet_positive (t : Real) : 0 < inlet t := Real.exp_pos _

theorem inlet_contDiff : ContDiff Real 1 inlet := by
  unfold inlet
  fun_prop

theorem response_contDiff (k : Real) : ContDiff Real 1 (response k) := by
  change ContDiff Real 1 (fun t => response k t)
  by_cases hk : k=1
  · subst k
    simp only [response, ite_true]
    fun_prop
  · simp only [response, ite_eq_right hk]
    fun_prop

theorem response_zero (k : Real) : response k 0=0 := by
  by_cases hk : k=1 <;> simp [response, hk]

theorem exp_negative_mul_deriv (k t : Real) :
    HasDerivAt (fun s : Real => Real.exp (-k*s))
      ((-k)*Real.exp (-k*t)) t := by
  simpa only [id_eq, mul_one, mul_comm] using
    (((hasDerivAt_id t).const_mul (-k)).exp)

theorem inlet_hasDerivAt (t : Real) : HasDerivAt inlet (-inlet t) t := by
  change HasDerivAt (fun s => inlet s) (-inlet t) t
  simpa only [inlet, one_mul, neg_one_mul] using exp_negative_mul_deriv 1 t

theorem response_hasDerivAt (k t : Real) :
    HasDerivAt (response k) (k*(inlet t-response k t)) t := by
  change HasDerivAt (fun s => response k s) (k*(inlet t-response k t)) t
  have h1 : HasDerivAt (fun s : Real => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using exp_negative_mul_deriv 1 t
  by_cases hk : k=1
  · subst k
    simp only [response, ite_true, inlet]
    convert (hasDerivAt_id t).mul h1 using 1
    · funext s
      rfl
    · simp only [id_eq]
      ring
  · have hn : k-1≠0 := sub_ne_zero.mpr hk
    simp only [response, ite_eq_right hk, inlet]
    have h := (h1.sub (exp_negative_mul_deriv k t)).const_mul (k/(k-1))
    change HasDerivAt (fun s => k/(k-1)*(Real.exp (-s)-Real.exp (-k*s)))
      (k/(k-1)*(-Real.exp (-t)-(-k)*Real.exp (-k*t))) t at h
    have he : k/(k-1)*(-Real.exp (-t)-(-k)*Real.exp (-k*t)) =
        k*(Real.exp (-t)-k/(k-1)*(Real.exp (-t)-Real.exp (-k*t))) := by
      field_simp [hn]
      <;> ring
    rw [he] at h
    exact h

theorem response_is_actual_C1_solution (k : Real) :
    ContDiff Real 1 (response k) ∧ response k 0=0 ∧
      ∀ t : Real, HasDerivAt (response k) (k*(inlet t-response k t)) t :=
  ⟨response_contDiff k, response_zero k, response_hasDerivAt k⟩

/-- Equivalently, the same initial state and zero additive forcing in a
two-node directed system; only the internal coefficient k changes. -/
theorem coupled_system_certificate (k : Real) :
    inlet 0 = 1 ∧ response k 0 = 0 ∧
    (∀ t : Real, HasDerivAt inlet (-inlet t) t) ∧
    (∀ t : Real, HasDerivAt (response k) (k*(inlet t-response k t)) t) := by
  refine ⟨?_, response_zero k, inlet_hasDerivAt, response_hasDerivAt k⟩
  simp [inlet]

theorem horizon_positive : 0<horizon := by
  exact Real.log_pos (by norm_num : (1 : Real)<4)

theorem exp_neg_horizon : Real.exp (-horizon)=(1/4 : Real) := by
  unfold horizon
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : Real)<4)]
  norm_num

theorem exp_neg_half_horizon : Real.exp (-(1/2 : Real)*horizon)=(1/2 : Real) := by
  have hlog : Real.log (4 : Real)=2*Real.log 2 := by
    rw [show (4 : Real)=2*2 by norm_num,
      Real.log_mul (by norm_num : (2 : Real)≠0) (by norm_num : (2 : Real)≠0)]
    ring
  unfold horizon
  rw [hlog, show -(1/2 : Real)*(2*Real.log 2) = -Real.log 2 by ring,
    Real.exp_neg, Real.exp_log (by norm_num : (0 : Real)<2)]
  norm_num

theorem exp_neg_two_horizon : Real.exp (-(2 : Real)*horizon)=(1/16 : Real) := by
  rw [show -(2 : Real)*horizon = -horizon + -horizon by ring,
    Real.exp_add, exp_neg_horizon]
  norm_num

theorem exp_neg_four_horizon : Real.exp (-(4 : Real)*horizon)=(1/256 : Real) := by
  rw [show -(4 : Real)*horizon = -(2 : Real)*horizon + -(2 : Real)*horizon by ring,
    Real.exp_add, exp_neg_two_horizon]
  norm_num

theorem response_half_at_horizon : response (1/2) horizon=(1/4 : Real) := by
  simp only [response, ite_eq_right (by norm_num : (1/2 : Real)≠1)]
  rw [exp_neg_horizon, exp_neg_half_horizon]
  norm_num

theorem response_two_at_horizon : response 2 horizon=(3/8 : Real) := by
  simp only [response, ite_eq_right (by norm_num : (2 : Real)≠1)]
  rw [exp_neg_horizon, exp_neg_two_horizon]
  norm_num

theorem response_four_at_horizon : response 4 horizon=(21/64 : Real) := by
  simp only [response, ite_eq_right (by norm_num : (4 : Real)≠1)]
  rw [exp_neg_horizon, exp_neg_four_horizon]
  norm_num

theorem interior_exceeds_both_endpoints :
    (2 : Real)∈Icc (1/2 : Real) 4 ∧
    response (1/2) horizon < response 2 horizon ∧
    response 4 horizon < response 2 horizon := by
  rw [response_half_at_horizon, response_two_at_horizon, response_four_at_horizon]
  norm_num

theorem interior_exceeds_endpoint_max_by :
    response 2 horizon-max (response (1/2) horizon) (response 4 horizon)=(3/64 : Real) := by
  rw [response_half_at_horizon, response_two_at_horizon, response_four_at_horizon]
  norm_num

theorem response_not_monotoneOn :
    ¬MonotoneOn (fun k : Real => response k horizon) (Icc (1/2 : Real) 4) := by
  intro h
  have he := h (by norm_num : (2 : Real)∈Icc (1/2 : Real) 4)
    (by norm_num : (4 : Real)∈Icc (1/2 : Real) 4) (by norm_num : (2 : Real)≤4)
  change response 2 horizon ≤ response 4 horizon at he
  rw [response_two_at_horizon, response_four_at_horizon] at he
  norm_num at he

theorem response_not_antitoneOn :
    ¬AntitoneOn (fun k : Real => response k horizon) (Icc (1/2 : Real) 4) := by
  intro h
  have he := h (by norm_num : (1/2 : Real)∈Icc (1/2 : Real) 4)
    (by norm_num : (2 : Real)∈Icc (1/2 : Real) 4) (by norm_num : (1/2 : Real)≤2)
  change response 2 horizon ≤ response (1/2) horizon at he
  rw [response_half_at_horizon, response_two_at_horizon] at he
  norm_num at he

end MathExploration.ParameterCounterexample

#print axioms MathExploration.ParameterCounterexample.inlet
#print axioms MathExploration.ParameterCounterexample.response
#print axioms MathExploration.ParameterCounterexample.horizon
#print axioms MathExploration.ParameterCounterexample.inlet_positive
#print axioms MathExploration.ParameterCounterexample.inlet_contDiff
#print axioms MathExploration.ParameterCounterexample.response_contDiff
#print axioms MathExploration.ParameterCounterexample.response_zero
#print axioms MathExploration.ParameterCounterexample.exp_negative_mul_deriv
#print axioms MathExploration.ParameterCounterexample.inlet_hasDerivAt
#print axioms MathExploration.ParameterCounterexample.response_hasDerivAt
#print axioms MathExploration.ParameterCounterexample.response_is_actual_C1_solution
#print axioms MathExploration.ParameterCounterexample.coupled_system_certificate
#print axioms MathExploration.ParameterCounterexample.horizon_positive
#print axioms MathExploration.ParameterCounterexample.exp_neg_horizon
#print axioms MathExploration.ParameterCounterexample.exp_neg_half_horizon
#print axioms MathExploration.ParameterCounterexample.exp_neg_two_horizon
#print axioms MathExploration.ParameterCounterexample.exp_neg_four_horizon
#print axioms MathExploration.ParameterCounterexample.response_half_at_horizon
#print axioms MathExploration.ParameterCounterexample.response_two_at_horizon
#print axioms MathExploration.ParameterCounterexample.response_four_at_horizon
#print axioms MathExploration.ParameterCounterexample.interior_exceeds_both_endpoints
#print axioms MathExploration.ParameterCounterexample.interior_exceeds_endpoint_max_by
#print axioms MathExploration.ParameterCounterexample.response_not_monotoneOn
#print axioms MathExploration.ParameterCounterexample.response_not_antitoneOn
