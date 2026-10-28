module
public import RobustTankCertificate
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.EndpointTank
open Set
open MathExploration.RobustNetworkBounds
open MathExploration.RobustTankCertificate

def c : Real := 21/20

def q (t : Real) : Real := Real.exp (-c*t)

def p (z : Real) : Real := 1-(7/3 : Real)*z+(3/2 : Real)*z^2-(1/6 : Real)*z^4

def endpointState (t : Real) : Fin 3 → Real := ![1-q t, (1-q t)^2, p (q t)]

theorem endpoint_admissible : admissible (21/20) (21/10) (21/20) (63/20) := by
  norm_num [admissible]

theorem q_hasDerivAt (t : Real) : HasDerivAt q (-c*q t) t := by
  exact MathExploration.ThreeTankCertificate.exp_negative_mul_deriv c t

theorem q_zero : q 0=1 := by simp [q]

theorem q_pos (t : Real) : 0 < q t := Real.exp_pos _

theorem q_nonneg (t : Real) : 0 ≤ q t := (q_pos t).le

theorem q_le_one (t : Real) (ht : 0≤t) : q t≤1 := by
  unfold q
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num [c]) ht

theorem endpointState_hasDerivAt (t : Real) (i : Fin 3) :
    HasDerivAt (fun s => endpointState s i)
      (linear (actualMatrix (21/20) (21/10) (21/20) (63/20)) (endpointState t) i+
        inlet (21/20) (fun _ => 1) t i) t := by
  have h := q_hasDerivAt t
  fin_cases i
  · change HasDerivAt (fun s => 1-q s) _ t
    convert (hasDerivAt_const t (1 : Real)).sub h using 1
    norm_num [linear,actualMatrix,endpointState,inlet,c,Fin.sum_univ_three]
    ring
  · change HasDerivAt (fun s => (1-q s)^2) _ t
    convert ((hasDerivAt_const t (1 : Real)).sub h).fun_pow 2 using 1
    norm_num [linear,actualMatrix,endpointState,inlet,c,Fin.sum_univ_three]
    ring
  · change HasDerivAt (fun s =>
      1-(7/3 : Real)*q s+(3/2 : Real)*(q s)^2-(1/6 : Real)*(q s)^4) _ t
    have hp := (((hasDerivAt_const t (1 : Real)).sub (h.const_mul (7/3))).add
      ((h.fun_pow 2).const_mul (3/2))).sub ((h.fun_pow 4).const_mul (1/6))
    convert hp using 1
    norm_num [linear,actualMatrix,endpointState,inlet,p,c,Fin.sum_univ_three]
    ring

theorem endpointState_zero (i : Fin 3) : endpointState 0 i=0 := by
  fin_cases i <;> norm_num [endpointState,q,p]

theorem endpointState_continuousOn (i : Fin 3) :
    ContinuousOn (fun t => endpointState t i) (Ici 0) :=
  (continuous_iff_continuousAt.mpr (fun t =>
    (endpointState_hasDerivAt t i).continuousAt)).continuousOn

theorem one_sub_endpoint_zero (t : Real) : 1-endpointState t 0=q t := by
  norm_num [endpointState]

theorem endpoint_zero_sub_one (t : Real) :
    endpointState t 0-endpointState t 1=q t*(1-q t) := by
  norm_num [endpointState]
  ring

theorem endpoint_one_sub_two (t : Real) :
    endpointState t 1-endpointState t 2=q t*(1-q t)^2*(q t+2)/6 := by
  norm_num [endpointState,p]
  ring

theorem endpoint_gaps_nonneg (t : Real) (ht : 0≤t) :
    0≤1-endpointState t 0 ∧
    0≤endpointState t 0-endpointState t 1 ∧
    0≤endpointState t 1-endpointState t 2 ∧
    0≤endpointState t 0-endpointState t 2 := by
  have hq0 := q_nonneg t
  have hq1 : 0≤1-q t := sub_nonneg.mpr (q_le_one t ht)
  have h0 : 0≤1-endpointState t 0 := by
    rw [one_sub_endpoint_zero]
    exact hq0
  have h01 : 0≤endpointState t 0-endpointState t 1 := by
    rw [endpoint_zero_sub_one]
    exact mul_nonneg hq0 hq1
  have h12 : 0≤endpointState t 1-endpointState t 2 := by
    rw [endpoint_one_sub_two]
    exact div_nonneg
      (mul_nonneg (mul_nonneg hq0 (sq_nonneg _)) (by linarith)) (by norm_num)
  exact ⟨h0,h01,h12,by linarith⟩

theorem endpoint_drift_domination (k0 k10 k20 k21 : Real)
    (hk : admissible k0 k10 k20 k21) (u : Real → Real)
    (t : Real) (ht : 0≤t) (hu : u t≤1) (i : Fin 3) :
    linear (actualMatrix k0 k10 k20 k21) (endpointState t) i+inlet k0 u t i ≤
      linear (actualMatrix (21/20) (21/10) (21/20) (63/20)) (endpointState t) i+
        inlet (21/20) (fun _ => 1) t i := by
  rcases hk with ⟨⟨h0a,h0b⟩,⟨h1a,h1b⟩,⟨h2a,h2b⟩,⟨h3a,h3b⟩⟩
  rcases endpoint_gaps_nonneg t ht with ⟨h0,h01,h12,h02⟩
  have hk0 : 0≤k0 := by linarith
  fin_cases i
  · have ha := mul_nonneg (sub_nonneg.mpr h0b) h0
    have hb := mul_nonneg hk0 (sub_nonneg.mpr hu)
    norm_num [linear,actualMatrix,inlet,Fin.sum_univ_three]
    nlinarith
  · have ha := mul_nonneg (sub_nonneg.mpr h1b) h01
    norm_num [linear,actualMatrix,inlet,Fin.sum_univ_three]
    nlinarith
  · have ha := mul_nonneg (sub_nonneg.mpr h2b) h02
    have hb := mul_nonneg (sub_nonneg.mpr h3b) h12
    norm_num [linear,actualMatrix,inlet,Fin.sum_univ_three]
    nlinarith

theorem solution_below_endpoint (k0 k10 k20 k21 : Real)
    (hk : admissible k0 k10 k20 k21) (x : Real → Fin 3 → Real) (u : Real → Real)
    (hc : ∀ i, ContinuousOn (fun t => x t i) (Ici 0))
    (hd : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun s => x s i)
        (linear (actualMatrix k0 k10 k20 k21) (x t) i+inlet k0 u t i) t)
    (hu : ∀ t : Real, 0<t → 0≤u t ∧ u t≤1) (hz : ∀ i, x 0 i=0)
    (t : Real) (ht : 0≤t) (i : Fin 3) : x t i≤endpointState t i := by
  apply differential_comparison (actualMatrix k0 k10 k20 k21) (actual_metzler _ _ _ _ hk)
    x endpointState
    (fun r j => linear (actualMatrix k0 k10 k20 k21) (x r) j+inlet k0 u r j)
    (fun r j => linear (actualMatrix (21/20) (21/10) (21/20) (63/20))
      (endpointState r) j+inlet (21/20) (fun _ => 1) r j)
    hc endpointState_continuousOn hd (fun r _ j => endpointState_hasDerivAt r j)
    _ _ t ht i
  · intro r hr j
    rw [linear_sub]
    have h := endpoint_drift_domination k0 k10 k20 k21 hk u r hr.le (hu r hr).2 j
    linarith
  · intro j
    rw [hz,endpointState_zero]

theorem endpointState_actual_solution :
    admissible (21/20) (21/10) (21/20) (63/20) ∧
    (∀ i, ContinuousOn (fun t => endpointState t i) (Ici 0)) ∧
    (∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun s => endpointState s i)
        (linear (actualMatrix (21/20) (21/10) (21/20) (63/20)) (endpointState t) i+
          inlet (21/20) (fun _ => 1) t i) t) ∧
    (∀ t : Real, 0<t → 0≤(1 : Real) ∧ (1 : Real)≤1) ∧
    (∀ i, endpointState 0 i=0) := by
  exact ⟨endpoint_admissible, endpointState_continuousOn,
    (fun t _ i => endpointState_hasDerivAt t i), (fun _ _ => by norm_num), endpointState_zero⟩

theorem endpointState_attainable (t : Real) (i : Fin 3) :
    ∃ x : Real → Fin 3 → Real,
      (∀ j, ContinuousOn (fun s => x s j) (Ici 0)) ∧
      (∀ s : Real, 0<s → ∀ j,
        HasDerivAt (fun r => x r j)
          (linear (actualMatrix (21/20) (21/10) (21/20) (63/20)) (x s) j+
            inlet (21/20) (fun _ => 1) s j) s) ∧
      (∀ j, x 0 j=0) ∧ x t i=endpointState t i := by
  exact ⟨endpointState,endpointState_continuousOn,
    (fun s _ j => endpointState_hasDerivAt s j),endpointState_zero,rfl⟩

end MathExploration.EndpointTank

#print axioms MathExploration.EndpointTank.c
#print axioms MathExploration.EndpointTank.q
#print axioms MathExploration.EndpointTank.p
#print axioms MathExploration.EndpointTank.endpointState
#print axioms MathExploration.EndpointTank.endpoint_admissible
#print axioms MathExploration.EndpointTank.q_hasDerivAt
#print axioms MathExploration.EndpointTank.q_zero
#print axioms MathExploration.EndpointTank.q_pos
#print axioms MathExploration.EndpointTank.q_nonneg
#print axioms MathExploration.EndpointTank.q_le_one
#print axioms MathExploration.EndpointTank.endpointState_hasDerivAt
#print axioms MathExploration.EndpointTank.endpointState_zero
#print axioms MathExploration.EndpointTank.endpointState_continuousOn
#print axioms MathExploration.EndpointTank.one_sub_endpoint_zero
#print axioms MathExploration.EndpointTank.endpoint_zero_sub_one
#print axioms MathExploration.EndpointTank.endpoint_one_sub_two
#print axioms MathExploration.EndpointTank.endpoint_gaps_nonneg
#print axioms MathExploration.EndpointTank.endpoint_drift_domination
#print axioms MathExploration.EndpointTank.solution_below_endpoint
#print axioms MathExploration.EndpointTank.endpointState_actual_solution
#print axioms MathExploration.EndpointTank.endpointState_attainable
