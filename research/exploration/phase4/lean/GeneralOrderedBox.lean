module
public import ScaledEndpointEnvelope
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathExploration.GeneralOrderedBox
open Set
open MathExploration.RobustNetworkBounds
open MathExploration.RobustTankCertificate

def orderedCaps (A B E F : Real) : Prop :=
  0≤A ∧ 0≤B ∧ 0≤E ∧ 0≤F ∧ E≤B

def boundedRates (A B E F a b e f : Real) : Prop :=
  (0≤a ∧ a≤A) ∧ (0≤b ∧ b≤B) ∧ (0≤e ∧ e≤E) ∧ (0≤f ∧ f≤F)

def gapState (Y : Real → Fin 3 → Real) (t : Real) : Fin 3 → Real :=
  ![1-Y t 0, Y t 0-Y t 1, Y t 1-Y t 2]

def gapMatrix (A B E F : Real) : Fin 3 → Fin 3 → Real :=
  ![![-A,0,0], ![A,-B,0], ![0,B-E,-(E+F)]]

theorem gap_matrix_metzler (A B E F : Real) (hA : 0≤A) (hEB : E≤B) :
    Metzler (gapMatrix A B E F) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [gapMatrix] at * <;> linarith

theorem actual_metzler_of_bounds (A B E F a b e f : Real)
    (h : boundedRates A B E F a b e f) : Metzler (actualMatrix a b e f) :=
  MathExploration.ScaledEndpointEnvelope.actual_metzler_of_nonneg a b e f
    h.1.1 h.2.1.1 h.2.2.1.1 h.2.2.2.1

theorem upper_rates_bounded (A B E F : Real) (h : orderedCaps A B E F) :
    boundedRates A B E F A B E F :=
  ⟨⟨h.1,le_rfl⟩,⟨h.2.1,le_rfl⟩,⟨h.2.2.1,le_rfl⟩,⟨h.2.2.2.1,le_rfl⟩⟩

theorem gapState_hasDerivAt (A B E F : Real) (Y : Real → Fin 3 → Real) (t : Real)
    (hY : ∀ i, HasDerivAt (fun s => Y s i)
      (linear (actualMatrix A B E F) (Y t) i+inlet A (fun _ => 1) t i) t)
    (i : Fin 3) :
    HasDerivAt (fun s => gapState Y s i) (linear (gapMatrix A B E F) (gapState Y t) i) t := by
  fin_cases i
  · change HasDerivAt (fun s => 1-Y s 0) _ t
    convert (hasDerivAt_const t (1 : Real)).sub (hY 0) using 1
    norm_num [linear,actualMatrix,inlet,gapMatrix,gapState,Fin.sum_univ_three]
    ring
  · change HasDerivAt (fun s => Y s 0-Y s 1) _ t
    convert (hY 0).sub (hY 1) using 1
    norm_num [linear,actualMatrix,inlet,gapMatrix,gapState,Fin.sum_univ_three]
    ring
  · change HasDerivAt (fun s => Y s 1-Y s 2) _ t
    convert (hY 1).sub (hY 2) using 1
    norm_num [linear,actualMatrix,inlet,gapMatrix,gapState,Fin.sum_univ_three]
    ring

theorem gapState_zero (Y : Real → Fin 3 → Real) (hY : ∀ i, Y 0 i=0) (i : Fin 3) :
    gapState Y 0 i=(![1,0,0] : Fin 3 → Real) i := by
  fin_cases i <;> norm_num [gapState,hY]

theorem gapState_continuousOn (Y : Real → Fin 3 → Real)
    (hY : ∀ i, ContinuousOn (fun t => Y t i) (Ici 0)) (i : Fin 3) :
    ContinuousOn (fun t => gapState Y t i) (Ici 0) := by
  fin_cases i
  · change ContinuousOn (fun t => 1-Y t 0) (Ici 0)
    exact continuousOn_const.sub (hY 0)
  · change ContinuousOn (fun t => Y t 0-Y t 1) (Ici 0)
    exact (hY 0).sub (hY 1)
  · change ContinuousOn (fun t => Y t 1-Y t 2) (Ici 0)
    exact (hY 1).sub (hY 2)

theorem upper_gaps_nonneg (A B E F : Real) (hCaps : orderedCaps A B E F)
    (Y : Real → Fin 3 → Real)
    (hc : ∀ i, ContinuousOn (fun t => Y t i) (Ici 0))
    (hd : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun s => Y s i)
        (linear (actualMatrix A B E F) (Y t) i+inlet A (fun _ => 1) t i) t)
    (hz : ∀ i, Y 0 i=0) (t : Real) (ht : 0≤t) (i : Fin 3) :
    0≤gapState Y t i := by
  apply positive_solution (gapMatrix A B E F)
    (gap_matrix_metzler A B E F hCaps.1 hCaps.2.2.2.2)
    (gapState Y) (fun _ _ => 0) (gapState_continuousOn Y hc) _ _ _ t ht i
  · intro s hs j
    simpa only [add_zero] using gapState_hasDerivAt A B E F Y s (hd s hs) j
  · intro s hs j
    exact le_rfl
  · intro j
    rw [gapState_zero Y hz j]
    fin_cases j <;> norm_num

theorem upper_order_gaps (A B E F : Real) (hCaps : orderedCaps A B E F)
    (Y : Real → Fin 3 → Real)
    (hc : ∀ i, ContinuousOn (fun t => Y t i) (Ici 0))
    (hd : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun s => Y s i)
        (linear (actualMatrix A B E F) (Y t) i+inlet A (fun _ => 1) t i) t)
    (hz : ∀ i, Y 0 i=0) (t : Real) (ht : 0≤t) :
    0≤1-Y t 0 ∧ 0≤Y t 0-Y t 1 ∧ 0≤Y t 1-Y t 2 ∧ 0≤Y t 0-Y t 2 := by
  have h0 := upper_gaps_nonneg A B E F hCaps Y hc hd hz t ht 0
  have h01 := upper_gaps_nonneg A B E F hCaps Y hc hd hz t ht 1
  have h12 := upper_gaps_nonneg A B E F hCaps Y hc hd hz t ht 2
  change 0≤1-Y t 0 at h0
  change 0≤Y t 0-Y t 1 at h01
  change 0≤Y t 1-Y t 2 at h12
  exact ⟨h0,h01,h12,by linarith⟩

theorem upper_drift_domination (A B E F : Real) (hCaps : orderedCaps A B E F)
    (a b e f : Real) (hk : boundedRates A B E F a b e f)
    (Y : Real → Fin 3 → Real)
    (hc : ∀ i, ContinuousOn (fun t => Y t i) (Ici 0))
    (hd : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun s => Y s i)
        (linear (actualMatrix A B E F) (Y t) i+inlet A (fun _ => 1) t i) t)
    (hz : ∀ i, Y 0 i=0) (u : Real → Real)
    (t : Real) (ht : 0≤t) (hu : u t≤1) (i : Fin 3) :
    linear (actualMatrix a b e f) (Y t) i+inlet a u t i ≤
      linear (actualMatrix A B E F) (Y t) i+inlet A (fun _ => 1) t i := by
  rcases hk with ⟨⟨ha0,haA⟩,⟨hb0,hbB⟩,⟨he0,heE⟩,⟨hf0,hfF⟩⟩
  rcases upper_order_gaps A B E F hCaps Y hc hd hz t ht with ⟨h0,h01,h12,h02⟩
  fin_cases i
  · have h1 := mul_nonneg (sub_nonneg.mpr haA) h0
    have h2 := mul_nonneg ha0 (sub_nonneg.mpr hu)
    norm_num [linear,actualMatrix,inlet,Fin.sum_univ_three]
    nlinarith
  · have h1 := mul_nonneg (sub_nonneg.mpr hbB) h01
    norm_num [linear,actualMatrix,inlet,Fin.sum_univ_three]
    nlinarith
  · have h1 := mul_nonneg (sub_nonneg.mpr heE) h02
    have h2 := mul_nonneg (sub_nonneg.mpr hfF) h12
    norm_num [linear,actualMatrix,inlet,Fin.sum_univ_three]
    nlinarith

theorem solution_below_upper_trajectory (A B E F : Real) (hCaps : orderedCaps A B E F)
    (a b e f : Real) (hk : boundedRates A B E F a b e f)
    (x Y : Real → Fin 3 → Real) (u : Real → Real)
    (hcx : ∀ i, ContinuousOn (fun t => x t i) (Ici 0))
    (hcY : ∀ i, ContinuousOn (fun t => Y t i) (Ici 0))
    (hdx : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun s => x s i)
        (linear (actualMatrix a b e f) (x t) i+inlet a u t i) t)
    (hdY : ∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun s => Y s i)
        (linear (actualMatrix A B E F) (Y t) i+inlet A (fun _ => 1) t i) t)
    (hu : ∀ t : Real, 0<t → 0≤u t ∧ u t≤1)
    (hzx : ∀ i, x 0 i=0) (hzY : ∀ i, Y 0 i=0)
    (t : Real) (ht : 0≤t) (i : Fin 3) : x t i≤Y t i := by
  apply differential_comparison (actualMatrix a b e f)
    (actual_metzler_of_bounds A B E F a b e f hk)
    x Y (fun r j => linear (actualMatrix a b e f) (x r) j+inlet a u r j)
    (fun r j => linear (actualMatrix A B E F) (Y r) j+inlet A (fun _ => 1) r j)
    hcx hcY hdx hdY _ _ t ht i
  · intro r hr j
    rw [linear_sub]
    have h := upper_drift_domination A B E F hCaps a b e f hk Y hcY hdY hzY
      u r hr.le (hu r hr).2 j
    linarith
  · intro j
    rw [hzx,hzY]

theorem scaled_caps_ordered (C : Real) (hC : 0≤C) : orderedCaps C (2*C) C (3*C) := by
  unfold orderedCaps
  constructor
  · exact hC
  constructor
  · exact mul_nonneg (by norm_num) hC
  constructor
  · exact hC
  exact ⟨mul_nonneg (by norm_num) hC,by linarith⟩

theorem scaled_upper_trajectory_instance (C : Real) (hC : 0≤C) :
    orderedCaps C (2*C) C (3*C) ∧
    (∀ i, ContinuousOn (fun t => MathExploration.ScaledEndpointEnvelope.scaledState C t i) (Ici 0)) ∧
    (∀ t : Real, 0<t → ∀ i,
      HasDerivAt (fun s => MathExploration.ScaledEndpointEnvelope.scaledState C s i)
        (linear (actualMatrix C (2*C) C (3*C))
          (MathExploration.ScaledEndpointEnvelope.scaledState C t) i+
          inlet C (fun _ => 1) t i) t) ∧
    (∀ i, MathExploration.ScaledEndpointEnvelope.scaledState C 0 i=0) := by
  exact ⟨scaled_caps_ordered C hC,MathExploration.ScaledEndpointEnvelope.scaledState_continuousOn C,
    (fun t _ i => MathExploration.ScaledEndpointEnvelope.scaledState_hasDerivAt C t i),
    MathExploration.ScaledEndpointEnvelope.scaledState_zero C⟩

end MathExploration.GeneralOrderedBox

#print axioms MathExploration.GeneralOrderedBox.orderedCaps
#print axioms MathExploration.GeneralOrderedBox.boundedRates
#print axioms MathExploration.GeneralOrderedBox.gapState
#print axioms MathExploration.GeneralOrderedBox.gapMatrix
#print axioms MathExploration.GeneralOrderedBox.gap_matrix_metzler
#print axioms MathExploration.GeneralOrderedBox.actual_metzler_of_bounds
#print axioms MathExploration.GeneralOrderedBox.upper_rates_bounded
#print axioms MathExploration.GeneralOrderedBox.gapState_hasDerivAt
#print axioms MathExploration.GeneralOrderedBox.gapState_zero
#print axioms MathExploration.GeneralOrderedBox.gapState_continuousOn
#print axioms MathExploration.GeneralOrderedBox.upper_gaps_nonneg
#print axioms MathExploration.GeneralOrderedBox.upper_order_gaps
#print axioms MathExploration.GeneralOrderedBox.upper_drift_domination
#print axioms MathExploration.GeneralOrderedBox.solution_below_upper_trajectory
#print axioms MathExploration.GeneralOrderedBox.scaled_caps_ordered
#print axioms MathExploration.GeneralOrderedBox.scaled_upper_trajectory_instance
