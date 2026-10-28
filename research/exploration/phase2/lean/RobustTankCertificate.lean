module
public import RobustNetworkBounds
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.RobustTankCertificate
open Set
open MathExploration.RobustNetworkBounds

/-! Fixed uncertain ODE coefficients, each within five percent of nominal.
This is not an independent five-percent uncertainty on both volumes and flows.
The upper matrix is an interval relaxation, not a realizable physical network.
-/
def admissible (k0 k10 k20 k21 : Real) : Prop :=
  ((19/20 : Real)≤k0 ∧ k0≤21/20) ∧ ((19/10 : Real)≤k10 ∧ k10≤21/10) ∧
  ((19/20 : Real)≤k20 ∧ k20≤21/20) ∧ ((57/20 : Real)≤k21 ∧ k21≤63/20)

def actualMatrix (k0 k10 k20 k21 : Real) : Fin 3 → Fin 3 → Real :=
  ![![-k0,0,0], ![k10,-k10,0], ![k20,k21,-(k20+k21)]]

def upperMatrix : Fin 3 → Fin 3 → Real :=
  ![![-19/20,0,0], ![21/10,-19/10,0], ![21/20,63/20,-19/5]]

def inlet (k0 : Real) (u : Real → Real) (t : Real) (i : Fin 3) : Real :=
  if i=0 then k0*u t else 0

def upperInlet (_ : Real) (i : Fin 3) : Real := if i=0 then 21/20 else 0
def r : Real := 19/20
def rho : Real := 21/19
def q (t : Real) : Real := Real.exp (-r*t)

def upperState (t : Real) : Fin 3 → Real :=
  ![rho*(1-q t), rho^2*(1-2*q t+(q t)^2),
    rho^2*((1/4 : Real)-q t/3+(q t)^4/12)+
    rho^3*((3/4 : Real)-2*q t+(3/2 : Real)*(q t)^2-(q t)^4/4)]

theorem actual_metzler (k0 k10 k20 k21 : Real) (h : admissible k0 k10 k20 k21) :
    Metzler (actualMatrix k0 k10 k20 k21) := by
  rcases h with ⟨⟨h0a,h0b⟩,⟨h1a,h1b⟩,⟨h2a,h2b⟩,⟨h3a,h3b⟩⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [actualMatrix] at * <;> linarith

theorem upper_metzler : Metzler upperMatrix := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [upperMatrix] at *

theorem actual_le_upper (k0 k10 k20 k21 : Real) (h : admissible k0 k10 k20 k21)
    (i j : Fin 3) : actualMatrix k0 k10 k20 k21 i j≤upperMatrix i j := by
  rcases h with ⟨⟨h0a,h0b⟩,⟨h1a,h1b⟩,⟨h2a,h2b⟩,⟨h3a,h3b⟩⟩
  fin_cases i <;> fin_cases j <;> norm_num [actualMatrix,upperMatrix] <;> linarith

theorem q_hasDerivAt (t : Real) : HasDerivAt q (-r*q t) t := by
  exact MathExploration.ThreeTankCertificate.exp_negative_mul_deriv r t

theorem upperState_hasDerivAt (t : Real) (i : Fin 3) :
    HasDerivAt (fun s => upperState s i)
      (linear upperMatrix (upperState t) i+upperInlet t i) t := by
  have h := q_hasDerivAt t
  fin_cases i
  · change HasDerivAt (fun s => rho*(1-q s)) _ t
    convert ((hasDerivAt_const t (1 : Real)).sub h).const_mul rho using 1
    norm_num [linear,upperMatrix,upperState,upperInlet,rho,r,q,Fin.sum_univ_three]; ring
  · change HasDerivAt (fun s => rho^2*(1-2*q s+(q s)^2)) _ t
    convert (((hasDerivAt_const t (1 : Real)).sub (h.const_mul 2)).add
      (h.fun_pow 2)).const_mul (rho^2) using 1
    norm_num [linear,upperMatrix,upperState,upperInlet,rho,r,q,Fin.sum_univ_three]; ring
  · change HasDerivAt (fun s => rho^2*((1/4 : Real)-q s/3+(q s)^4/12)+
      rho^3*((3/4 : Real)-2*q s+(3/2 : Real)*(q s)^2-(q s)^4/4)) _ t
    have hp := (((hasDerivAt_const t (1/4 : Real)).sub (h.div_const 3)).add
      ((h.fun_pow 4).div_const 12)).const_mul (rho^2)
    have hq := ((((hasDerivAt_const t (3/4 : Real)).sub (h.const_mul 2)).add
      ((h.fun_pow 2).const_mul (3/2))).sub ((h.fun_pow 4).div_const 4)).const_mul (rho^3)
    convert hp.add hq using 1
    norm_num [linear,upperMatrix,upperState,upperInlet,rho,r,q,Fin.sum_univ_three]; ring

theorem upperState_zero (i : Fin 3) : upperState 0 i=0 := by
  fin_cases i <;> norm_num [upperState,q]

theorem upperState_continuousOn (i : Fin 3) :
    ContinuousOn (fun t => upperState t i) (Ici 0) :=
  (continuous_iff_continuousAt.mpr (fun t => (upperState_hasDerivAt t i).continuousAt)).continuousOn

def checkTime : Real := (20/19 : Real)*Real.log 2

theorem checkTime_nonnegative : 0≤checkTime :=
  mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num : (1 : Real)≤2))

theorem upperState_at_checkTime : upperState checkTime 2=(28077/109744 : Real) := by
  have hq : q checkTime=(1/2 : Real) := by
    unfold q checkTime r
    rw [show (-(19/20 : Real))*((20/19 : Real)*Real.log 2) = -Real.log 2 by ring]
    rw [Real.exp_neg,Real.exp_log (by norm_num : (0 : Real)<2)]
    norm_num
  change rho^2*((1/4 : Real)-q checkTime/3+(q checkTime)^4/12)+
    rho^3*((3/4 : Real)-2*q checkTime+(3/2 : Real)*(q checkTime)^2-(q checkTime)^4/4) = _
  rw [hq]
  norm_num [rho]

/-- Uniform over all admissible fixed coefficients and all supplied classical
solutions with bounded nonnegative inlet. No parameter endpoint search. -/
theorem solution_below_upper (k0 k10 k20 k21 : Real)
    (hk : admissible k0 k10 k20 k21) (x : Real → Fin 3 → Real) (u : Real → Real)
    (hc : ∀ i, ContinuousOn (fun t => x t i) (Ici 0))
    (hd : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun s => x s i)
        (linear (actualMatrix k0 k10 k20 k21) (x t) i+inlet k0 u t i) t)
    (hu : ∀ t : Real, 0<t → 0≤u t ∧ u t≤1) (hz : ∀ i, x 0 i=0)
    (t : Real) (ht : 0≤t) (i : Fin 3) : x t i≤upperState t i := by
  have hk0 : 0≤k0 := by have h := hk.1.1; linarith
  apply interval_upper (actualMatrix k0 k10 k20 k21) upperMatrix
    (actual_metzler _ _ _ _ hk) upper_metzler (actual_le_upper _ _ _ _ hk)
    x upperState (inlet k0 u) upperInlet hc upperState_continuousOn hd
    (fun s _ j => upperState_hasDerivAt s j) _ _ _ _ t ht i
  · intro s hs j
    by_cases hj : j=0
    · simpa [inlet,hj] using mul_nonneg hk0 (hu s hs).1
    · simp [inlet,hj]
  · intro s hs j
    by_cases hj : j=0
    · have hmul : k0*u s≤k0 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hu s hs).2 hk0
      have h := hmul.trans hk.1.2
      simpa [inlet,upperInlet,hj] using h
    · simp [inlet,upperInlet,hj]
  · intro j
    rw [hz]
  · intro j
    rw [hz,upperState_zero]

theorem outlet_robust_bound (k0 k10 k20 k21 : Real)
    (hk : admissible k0 k10 k20 k21) (x : Real → Fin 3 → Real) (u : Real → Real)
    (hc : ∀ i, ContinuousOn (fun t => x t i) (Ici 0))
    (hd : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun s => x s i)
        (linear (actualMatrix k0 k10 k20 k21) (x t) i+inlet k0 u t i) t)
    (hu : ∀ t : Real, 0<t → 0≤u t ∧ u t≤1) (hz : ∀ i, x 0 i=0) :
    x checkTime 2≤(28077/109744 : Real) ∧ x checkTime 2<(13/50 : Real) := by
  have h := solution_below_upper k0 k10 k20 k21 hk x u hc hd hu hz checkTime checkTime_nonnegative 2
  rw [upperState_at_checkTime] at h
  exact ⟨h,h.trans_lt (by norm_num)⟩

end MathExploration.RobustTankCertificate

#print axioms MathExploration.RobustTankCertificate.admissible
#print axioms MathExploration.RobustTankCertificate.actualMatrix
#print axioms MathExploration.RobustTankCertificate.upperMatrix
#print axioms MathExploration.RobustTankCertificate.inlet
#print axioms MathExploration.RobustTankCertificate.upperInlet
#print axioms MathExploration.RobustTankCertificate.r
#print axioms MathExploration.RobustTankCertificate.rho
#print axioms MathExploration.RobustTankCertificate.q
#print axioms MathExploration.RobustTankCertificate.upperState
#print axioms MathExploration.RobustTankCertificate.actual_metzler
#print axioms MathExploration.RobustTankCertificate.upper_metzler
#print axioms MathExploration.RobustTankCertificate.actual_le_upper
#print axioms MathExploration.RobustTankCertificate.q_hasDerivAt
#print axioms MathExploration.RobustTankCertificate.upperState_hasDerivAt
#print axioms MathExploration.RobustTankCertificate.upperState_zero
#print axioms MathExploration.RobustTankCertificate.upperState_continuousOn
#print axioms MathExploration.RobustTankCertificate.checkTime
#print axioms MathExploration.RobustTankCertificate.checkTime_nonnegative
#print axioms MathExploration.RobustTankCertificate.upperState_at_checkTime
#print axioms MathExploration.RobustTankCertificate.solution_below_upper
#print axioms MathExploration.RobustTankCertificate.outlet_robust_bound
