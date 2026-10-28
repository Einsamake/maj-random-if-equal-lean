module
public import EndpointTank
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.ScaledEndpointEnvelope
open Set
open MathExploration.RobustNetworkBounds
open MathExploration.RobustTankCertificate

def timeScale (C : Real) : Real := (20/21 : Real)*C

def scaledState (C t : Real) : Fin 3 → Real :=
  MathExploration.EndpointTank.endpointState (timeScale C*t)

def boundedRates (C a b e f : Real) : Prop :=
  (0≤a ∧ a≤C) ∧ (0≤b ∧ b≤2*C) ∧ (0≤e ∧ e≤C) ∧ (0≤f ∧ f≤3*C)

theorem timeScale_nonneg (C : Real) (hC : 0≤C) : 0≤timeScale C := by
  exact mul_nonneg (by norm_num : (0 : Real)≤20/21) hC

theorem timeScale_cancel (C : Real) :
    MathExploration.EndpointTank.c*timeScale C=C := by
  unfold MathExploration.EndpointTank.c timeScale
  ring

theorem actual_metzler_of_nonneg (a b e f : Real)
    (_ha : 0≤a) (hb : 0≤b) (he : 0≤e) (hf : 0≤f) :
    Metzler (actualMatrix a b e f) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [actualMatrix] at * <;> linarith

theorem bounded_actual_metzler (C a b e f : Real) (h : boundedRates C a b e f) :
    Metzler (actualMatrix a b e f) :=
  actual_metzler_of_nonneg a b e f h.1.1 h.2.1.1 h.2.2.1.1 h.2.2.2.1

theorem upper_rates_bounded (C : Real) (hC : 0≤C) :
    boundedRates C C (2*C) C (3*C) := by
  exact ⟨⟨hC,le_rfl⟩,⟨mul_nonneg (by norm_num) hC,le_rfl⟩,
    ⟨hC,le_rfl⟩,⟨mul_nonneg (by norm_num) hC,le_rfl⟩⟩

theorem endpoint_drift_scale (C : Real) (x : Fin 3 → Real) (t : Real) (i : Fin 3) :
    (linear (actualMatrix (21/20) (21/10) (21/20) (63/20)) x i+
      inlet (21/20) (fun _ => 1) (timeScale C*t) i)*timeScale C =
    linear (actualMatrix C (2*C) C (3*C)) x i+inlet C (fun _ => 1) t i := by
  fin_cases i <;> norm_num [linear,actualMatrix,inlet,timeScale,Fin.sum_univ_three] <;> ring

theorem scaledState_hasDerivAt (C t : Real) (i : Fin 3) :
    HasDerivAt (fun s => scaledState C s i)
      (linear (actualMatrix C (2*C) C (3*C)) (scaledState C t) i+
        inlet C (fun _ => 1) t i) t := by
  have hinner : HasDerivAt (fun s : Real => timeScale C*s) (timeScale C) t := by
    simpa only [id_eq,mul_one] using (hasDerivAt_id t).const_mul (timeScale C)
  have h := (MathExploration.EndpointTank.endpointState_hasDerivAt (timeScale C*t) i).comp t hinner
  change HasDerivAt (fun s => scaledState C s i)
    ((linear (actualMatrix (21/20) (21/10) (21/20) (63/20))
      (MathExploration.EndpointTank.endpointState (timeScale C*t)) i+
      inlet (21/20) (fun _ => 1) (timeScale C*t) i)*timeScale C) t at h
  rw [endpoint_drift_scale] at h
  exact h

theorem scaledState_zero (C : Real) (i : Fin 3) : scaledState C 0 i=0 := by
  simpa only [scaledState,mul_zero] using MathExploration.EndpointTank.endpointState_zero i

theorem scaledState_zero_cap (t : Real) (i : Fin 3) : scaledState 0 t i=0 := by
  simpa [scaledState,timeScale] using MathExploration.EndpointTank.endpointState_zero i

theorem scaledState_continuousOn (C : Real) (i : Fin 3) :
    ContinuousOn (fun t => scaledState C t i) (Ici 0) :=
  (continuous_iff_continuousAt.mpr (fun t =>
    (scaledState_hasDerivAt C t i).continuousAt)).continuousOn

theorem scaledState_gaps_nonneg (C : Real) (hC : 0≤C) (t : Real) (ht : 0≤t) :
    0≤1-scaledState C t 0 ∧
    0≤scaledState C t 0-scaledState C t 1 ∧
    0≤scaledState C t 1-scaledState C t 2 ∧
    0≤scaledState C t 0-scaledState C t 2 := by
  exact MathExploration.EndpointTank.endpoint_gaps_nonneg (timeScale C*t)
    (mul_nonneg (timeScale_nonneg C hC) ht)

theorem scaled_drift_domination (C : Real) (hC : 0≤C) (a b e f : Real)
    (hk : boundedRates C a b e f) (u : Real → Real)
    (t : Real) (ht : 0≤t) (hu : u t≤1) (i : Fin 3) :
    linear (actualMatrix a b e f) (scaledState C t) i+inlet a u t i ≤
      linear (actualMatrix C (2*C) C (3*C)) (scaledState C t) i+
        inlet C (fun _ => 1) t i := by
  rcases hk with ⟨⟨ha0,haC⟩,⟨hb0,hbC⟩,⟨he0,heC⟩,⟨hf0,hfC⟩⟩
  rcases scaledState_gaps_nonneg C hC t ht with ⟨h0,h01,h12,h02⟩
  fin_cases i
  · have h1 := mul_nonneg (sub_nonneg.mpr haC) h0
    have h2 := mul_nonneg ha0 (sub_nonneg.mpr hu)
    norm_num [linear,actualMatrix,inlet,Fin.sum_univ_three]
    nlinarith
  · have h1 := mul_nonneg (sub_nonneg.mpr hbC) h01
    norm_num [linear,actualMatrix,inlet,Fin.sum_univ_three]
    nlinarith
  · have h1 := mul_nonneg (sub_nonneg.mpr heC) h02
    have h2 := mul_nonneg (sub_nonneg.mpr hfC) h12
    norm_num [linear,actualMatrix,inlet,Fin.sum_univ_three]
    nlinarith

theorem solution_below_scaled (C : Real) (hC : 0≤C) (a b e f : Real)
    (hk : boundedRates C a b e f) (x : Real → Fin 3 → Real) (u : Real → Real)
    (hc : ∀ i, ContinuousOn (fun t => x t i) (Ici 0))
    (hd : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun s => x s i)
        (linear (actualMatrix a b e f) (x t) i+inlet a u t i) t)
    (hu : ∀ t : Real, 0<t → 0≤u t ∧ u t≤1) (hz : ∀ i, x 0 i=0)
    (t : Real) (ht : 0≤t) (i : Fin 3) : x t i≤scaledState C t i := by
  apply differential_comparison (actualMatrix a b e f) (bounded_actual_metzler C a b e f hk)
    x (scaledState C)
    (fun r j => linear (actualMatrix a b e f) (x r) j+inlet a u r j)
    (fun r j => linear (actualMatrix C (2*C) C (3*C)) (scaledState C r) j+
      inlet C (fun _ => 1) r j)
    hc (scaledState_continuousOn C) hd (fun r _ j => scaledState_hasDerivAt C r j)
    _ _ t ht i
  · intro r hr j
    rw [linear_sub]
    have h := scaled_drift_domination C hC a b e f hk u r hr.le (hu r hr).2 j
    linarith
  · intro j
    rw [hz,scaledState_zero]

theorem scaledState_actual_solution (C : Real) (hC : 0≤C) :
    boundedRates C C (2*C) C (3*C) ∧
    (∀ i, ContinuousOn (fun t => scaledState C t i) (Ici 0)) ∧
    (∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun s => scaledState C s i)
        (linear (actualMatrix C (2*C) C (3*C)) (scaledState C t) i+
          inlet C (fun _ => 1) t i) t) ∧
    (∀ t : Real, 0<t → 0≤(1 : Real) ∧ (1 : Real)≤1) ∧
    (∀ i, scaledState C 0 i=0) := by
  exact ⟨upper_rates_bounded C hC,scaledState_continuousOn C,
    (fun t _ i => scaledState_hasDerivAt C t i),(fun _ _ => by norm_num),scaledState_zero C⟩

theorem scaledState_attainable (C : Real) (hC : 0≤C) (t : Real) (i : Fin 3) :
    ∃ x : Real → Fin 3 → Real,
      boundedRates C C (2*C) C (3*C) ∧
      (∀ j, ContinuousOn (fun s => x s j) (Ici 0)) ∧
      (∀ s : Real, 0<s → ∀ j,
        HasDerivAt (fun r => x r j)
          (linear (actualMatrix C (2*C) C (3*C)) (x s) j+
            inlet C (fun _ => 1) s j) s) ∧
      (∀ j, x 0 j=0) ∧ x t i=scaledState C t i := by
  exact ⟨scaledState C,upper_rates_bounded C hC,scaledState_continuousOn C,
    (fun s _ j => scaledState_hasDerivAt C s j),scaledState_zero C,rfl⟩

end MathExploration.ScaledEndpointEnvelope

#print axioms MathExploration.ScaledEndpointEnvelope.timeScale
#print axioms MathExploration.ScaledEndpointEnvelope.scaledState
#print axioms MathExploration.ScaledEndpointEnvelope.boundedRates
#print axioms MathExploration.ScaledEndpointEnvelope.timeScale_nonneg
#print axioms MathExploration.ScaledEndpointEnvelope.timeScale_cancel
#print axioms MathExploration.ScaledEndpointEnvelope.actual_metzler_of_nonneg
#print axioms MathExploration.ScaledEndpointEnvelope.bounded_actual_metzler
#print axioms MathExploration.ScaledEndpointEnvelope.upper_rates_bounded
#print axioms MathExploration.ScaledEndpointEnvelope.endpoint_drift_scale
#print axioms MathExploration.ScaledEndpointEnvelope.scaledState_hasDerivAt
#print axioms MathExploration.ScaledEndpointEnvelope.scaledState_zero
#print axioms MathExploration.ScaledEndpointEnvelope.scaledState_zero_cap
#print axioms MathExploration.ScaledEndpointEnvelope.scaledState_continuousOn
#print axioms MathExploration.ScaledEndpointEnvelope.scaledState_gaps_nonneg
#print axioms MathExploration.ScaledEndpointEnvelope.scaled_drift_domination
#print axioms MathExploration.ScaledEndpointEnvelope.solution_below_scaled
#print axioms MathExploration.ScaledEndpointEnvelope.scaledState_actual_solution
#print axioms MathExploration.ScaledEndpointEnvelope.scaledState_attainable
