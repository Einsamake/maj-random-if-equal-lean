module
public import EndpointTank
public import EndpointArithmetic
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.EndpointCertificate
open Set
open MathExploration.RobustNetworkBounds
open MathExploration.RobustTankCertificate

def outletValues (t : Real) : Set Real := {z | ∃ k0 k10 k20 k21 : Real,
  ∃ x : Real → Fin 3 → Real, ∃ u : Real → Real,
    admissible k0 k10 k20 k21 ∧
    (∀ i, ContinuousOn (fun s => x s i) (Ici 0)) ∧
    (∀ s : Real, 0<s → ∀ i,
      HasDerivAt (fun r => x r i)
        (linear (actualMatrix k0 k10 k20 k21) (x s) i+inlet k0 u s i) s) ∧
    (∀ s : Real, 0<s → 0≤u s ∧ u s≤1) ∧
    (∀ i, x 0 i=0) ∧ z=x t 2}

theorem greatest_outlet (t : Real) (ht : 0≤t) :
    IsGreatest (outletValues t) (EndpointTank.endpointState t 2) := by
  constructor
  · exact ⟨21/20,21/10,21/20,63/20,EndpointTank.endpointState,(fun _ => 1),
      EndpointTank.endpoint_admissible,EndpointTank.endpointState_continuousOn,
      (fun s _ i => EndpointTank.endpointState_hasDerivAt s i),
      (fun _ _ => by norm_num),EndpointTank.endpointState_zero,rfl⟩
  · rintro z ⟨k0,k10,k20,k21,x,u,hk,hc,hd,hu,hz,rfl⟩
    exact EndpointTank.solution_below_endpoint k0 k10 k20 k21 hk x u hc hd hu hz t ht 2

theorem q_at_checkTime : EndpointTank.q checkTime=EndpointArithmetic.checkDecay := by
  unfold EndpointTank.q EndpointTank.c checkTime EndpointArithmetic.checkDecay
  congr 1
  ring

theorem endpoint_at_checkTime : EndpointTank.endpointState checkTime 2=
    EndpointArithmetic.response EndpointArithmetic.checkDecay := by
  simp only [EndpointTank.endpointState,Matrix.cons_val_two]
  rw [q_at_checkTime]
  rfl

theorem exact_maximum_at_checkTime : IsGreatest (outletValues checkTime)
    (EndpointArithmetic.response EndpointArithmetic.checkDecay) := by
  rw [← endpoint_at_checkTime]
  exact greatest_outlet checkTime checkTime_nonnegative

theorem every_outlet_at_checkTime_bound (z : Real) (hz : z ∈ outletValues checkTime) :
    z ≤ (7425545410773/32000000000000 : Real) ∧
    z < (233/1000 : Real) ∧ z < (24/100 : Real) := by
  have he : z ≤ EndpointArithmetic.response EndpointArithmetic.checkDecay :=
    exact_maximum_at_checkTime.2 hz
  have hb := he.trans EndpointArithmetic.response_checkDecay_bound
  exact ⟨hb,hb.trans_lt (by norm_num),hb.trans_lt (by norm_num)⟩

end MathExploration.EndpointCertificate

#print axioms MathExploration.EndpointCertificate.outletValues
#print axioms MathExploration.EndpointCertificate.greatest_outlet
#print axioms MathExploration.EndpointCertificate.q_at_checkTime
#print axioms MathExploration.EndpointCertificate.endpoint_at_checkTime
#print axioms MathExploration.EndpointCertificate.exact_maximum_at_checkTime
#print axioms MathExploration.EndpointCertificate.every_outlet_at_checkTime_bound
