module
public import RobustTankCertificate
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.ConstantInletCounterexample
open Set
open MathExploration.RobustNetworkBounds
open MathExploration.RobustTankCertificate

def r (t : Real) : Real := Real.exp (-(1/2 : Real)*t)

def lowState (t : Real) : Fin 3 → Real :=
  ![1-(r t)^2, (1-r t)^2, 1-(r t)^2-r t/2+(r t)^5/2]

def highState (t : Real) : Fin 3 → Real :=
  ![1-(r t)^2, (1-r t)^2,
    1-(r t)^2/2-(4/5 : Real)*r t+(3/10 : Real)*(r t)^6]

def checkTime : Real := 2*Real.log 2

theorem low_parameters_strictly_positive :
    0<(1 : Real) ∧ 0<(1/2 : Real) ∧ 0<(2 : Real) ∧ 0<(1/2 : Real) := by
  norm_num

theorem high_parameters_strictly_positive :
    0<(1 : Real) ∧ 0<(1/2 : Real) ∧ 0<(2 : Real) ∧ 0<(1 : Real) := by
  norm_num

theorem low_matrix_metzler : Metzler (actualMatrix 1 (1/2) 2 (1/2)) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [actualMatrix] at *

theorem high_matrix_metzler : Metzler (actualMatrix 1 (1/2) 2 1) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [actualMatrix] at *

theorem r_hasDerivAt (t : Real) : HasDerivAt r (-(1/2 : Real)*r t) t := by
  exact MathExploration.ThreeTankCertificate.exp_negative_mul_deriv (1/2) t

theorem r_zero : r 0=1 := by simp [r]

theorem same_upstream (t : Real) :
    lowState t 0=highState t 0 ∧ lowState t 1=highState t 1 := ⟨rfl,rfl⟩

theorem lowState_hasDerivAt (t : Real) (i : Fin 3) :
    HasDerivAt (fun s => lowState s i)
      (linear (actualMatrix 1 (1/2) 2 (1/2)) (lowState t) i+
        inlet 1 (fun _ => 1) t i) t := by
  have h := r_hasDerivAt t
  fin_cases i
  · change HasDerivAt (fun s => 1-(r s)^2) _ t
    convert (hasDerivAt_const t (1 : Real)).sub (h.fun_pow 2) using 1
    norm_num [linear,actualMatrix,lowState,inlet,Fin.sum_univ_three]
    ring
  · change HasDerivAt (fun s => (1-r s)^2) _ t
    convert ((hasDerivAt_const t (1 : Real)).sub h).fun_pow 2 using 1
    norm_num [linear,actualMatrix,lowState,inlet,Fin.sum_univ_three]
    ring
  · change HasDerivAt (fun s => 1-(r s)^2-r s/2+(r s)^5/2) _ t
    have hp := (((hasDerivAt_const t (1 : Real)).sub (h.fun_pow 2)).sub
      (h.div_const 2)).add ((h.fun_pow 5).div_const 2)
    convert hp using 1
    norm_num [linear,actualMatrix,lowState,inlet,Fin.sum_univ_three]
    ring

theorem highState_hasDerivAt (t : Real) (i : Fin 3) :
    HasDerivAt (fun s => highState s i)
      (linear (actualMatrix 1 (1/2) 2 1) (highState t) i+
        inlet 1 (fun _ => 1) t i) t := by
  have h := r_hasDerivAt t
  fin_cases i
  · change HasDerivAt (fun s => 1-(r s)^2) _ t
    convert (hasDerivAt_const t (1 : Real)).sub (h.fun_pow 2) using 1
    norm_num [linear,actualMatrix,highState,inlet,Fin.sum_univ_three]
    ring
  · change HasDerivAt (fun s => (1-r s)^2) _ t
    convert ((hasDerivAt_const t (1 : Real)).sub h).fun_pow 2 using 1
    norm_num [linear,actualMatrix,highState,inlet,Fin.sum_univ_three]
    ring
  · change HasDerivAt (fun s =>
      1-(r s)^2/2-(4/5 : Real)*r s+(3/10 : Real)*(r s)^6) _ t
    have hp := (((hasDerivAt_const t (1 : Real)).sub ((h.fun_pow 2).div_const 2)).sub
      (h.const_mul (4/5))).add ((h.fun_pow 6).const_mul (3/10))
    convert hp using 1
    norm_num [linear,actualMatrix,highState,inlet,Fin.sum_univ_three]
    ring

theorem lowState_zero (i : Fin 3) : lowState 0 i=0 := by
  fin_cases i <;> norm_num [lowState,r]

theorem highState_zero (i : Fin 3) : highState 0 i=0 := by
  fin_cases i <;> norm_num [highState,r]

theorem lowState_continuousOn (i : Fin 3) :
    ContinuousOn (fun t => lowState t i) (Ici 0) :=
  (continuous_iff_continuousAt.mpr (fun t =>
    (lowState_hasDerivAt t i).continuousAt)).continuousOn

theorem highState_continuousOn (i : Fin 3) :
    ContinuousOn (fun t => highState t i) (Ici 0) :=
  (continuous_iff_continuousAt.mpr (fun t =>
    (highState_hasDerivAt t i).continuousAt)).continuousOn

theorem checkTime_positive : 0 < checkTime :=
  mul_pos (by norm_num) (Real.log_pos (by norm_num : (1 : Real)<2))

theorem r_at_checkTime : r checkTime=(1/2 : Real) := by
  unfold r checkTime
  rw [show -(1/2 : Real)*(2*Real.log 2) = -Real.log 2 by ring,
    Real.exp_neg,Real.exp_log (by norm_num : (0 : Real)<2)]
  norm_num

theorem low_outlet_at_checkTime : lowState checkTime 2=(33/64 : Real) := by
  norm_num [lowState,r_at_checkTime]

theorem high_outlet_at_checkTime : highState checkTime 2=(307/640 : Real) := by
  norm_num [highState,r_at_checkTime]

theorem middle_at_checkTime :
    lowState checkTime 1=(1/4 : Real) ∧ highState checkTime 1=(1/4 : Real) := by
  norm_num [lowState,highState,r_at_checkTime]

theorem outlet_difference_at_checkTime :
    lowState checkTime 2-highState checkTime 2=(23/640 : Real) := by
  rw [low_outlet_at_checkTime,high_outlet_at_checkTime]
  norm_num

theorem larger_link_smaller_outlet :
    (1/2 : Real)<1 ∧ highState checkTime 2<lowState checkTime 2 := by
  rw [low_outlet_at_checkTime,high_outlet_at_checkTime]
  norm_num

theorem middle_cleaner_than_high_outlet : highState checkTime 1<highState checkTime 2 := by
  rw [middle_at_checkTime.2,high_outlet_at_checkTime]
  norm_num

theorem lowState_actual_solution :
    Metzler (actualMatrix 1 (1/2) 2 (1/2)) ∧
    (∀ i, ContinuousOn (fun t => lowState t i) (Ici 0)) ∧
    (∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun s => lowState s i)
        (linear (actualMatrix 1 (1/2) 2 (1/2)) (lowState t) i+
          inlet 1 (fun _ => 1) t i) t) ∧
    (∀ i, lowState 0 i=0) := by
  exact ⟨low_matrix_metzler,lowState_continuousOn,
    (fun t _ i => lowState_hasDerivAt t i),lowState_zero⟩

theorem highState_actual_solution :
    Metzler (actualMatrix 1 (1/2) 2 1) ∧
    (∀ i, ContinuousOn (fun t => highState t i) (Ici 0)) ∧
    (∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun s => highState s i)
        (linear (actualMatrix 1 (1/2) 2 1) (highState t) i+
          inlet 1 (fun _ => 1) t i) t) ∧
    (∀ i, highState 0 i=0) := by
  exact ⟨high_matrix_metzler,highState_continuousOn,
    (fun t _ i => highState_hasDerivAt t i),highState_zero⟩

end MathExploration.ConstantInletCounterexample

#print axioms MathExploration.ConstantInletCounterexample.r
#print axioms MathExploration.ConstantInletCounterexample.lowState
#print axioms MathExploration.ConstantInletCounterexample.highState
#print axioms MathExploration.ConstantInletCounterexample.checkTime
#print axioms MathExploration.ConstantInletCounterexample.low_parameters_strictly_positive
#print axioms MathExploration.ConstantInletCounterexample.high_parameters_strictly_positive
#print axioms MathExploration.ConstantInletCounterexample.low_matrix_metzler
#print axioms MathExploration.ConstantInletCounterexample.high_matrix_metzler
#print axioms MathExploration.ConstantInletCounterexample.r_hasDerivAt
#print axioms MathExploration.ConstantInletCounterexample.r_zero
#print axioms MathExploration.ConstantInletCounterexample.same_upstream
#print axioms MathExploration.ConstantInletCounterexample.lowState_hasDerivAt
#print axioms MathExploration.ConstantInletCounterexample.highState_hasDerivAt
#print axioms MathExploration.ConstantInletCounterexample.lowState_zero
#print axioms MathExploration.ConstantInletCounterexample.highState_zero
#print axioms MathExploration.ConstantInletCounterexample.lowState_continuousOn
#print axioms MathExploration.ConstantInletCounterexample.highState_continuousOn
#print axioms MathExploration.ConstantInletCounterexample.checkTime_positive
#print axioms MathExploration.ConstantInletCounterexample.r_at_checkTime
#print axioms MathExploration.ConstantInletCounterexample.low_outlet_at_checkTime
#print axioms MathExploration.ConstantInletCounterexample.high_outlet_at_checkTime
#print axioms MathExploration.ConstantInletCounterexample.middle_at_checkTime
#print axioms MathExploration.ConstantInletCounterexample.outlet_difference_at_checkTime
#print axioms MathExploration.ConstantInletCounterexample.larger_link_smaller_outlet
#print axioms MathExploration.ConstantInletCounterexample.middle_cleaner_than_high_outlet
#print axioms MathExploration.ConstantInletCounterexample.lowState_actual_solution
#print axioms MathExploration.ConstantInletCounterexample.highState_actual_solution
