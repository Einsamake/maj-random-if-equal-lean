module

public import MathResearchAnalysis.UpperStoppingApprox
public import MathResearchAnalysis.ExtendedNextRing
public import MathResearchAnalysis.ArrivalFiltration

set_option autoImplicit false

/-!
# Upper-readiness approximation of actual next-ring waits

Once an upper approximation remains below the original strict next ring,
the least selected arrival index is unchanged. This selector fact needs no
right-continuity, absence of simultaneous rings, or waiting-time law. On finite
cofinal paths the rounded waits approach the actual wait from below, so their
strict survival events are eventually equal even at a threshold equal to the
actual waiting value. No atomlessness assumption is used.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace MathResearchAnalysis.ClockWaitingLimit

variable {Ω : Type*}

def waiting (arrival : Nat → Ω → ℝ) (R : Ω → WithTop ℝ) (ω : Ω) : ℝ :=
  max ((ExtendedNextRing.after arrival R ω).untopD 0 - (R ω).untopD 0) 0

/-- Raising readiness without crossing its original selected arrival preserves the selector.
This is a least-index argument and does not require monotone arrival values. -/
theorem after_eq_of_between (arrival : Nat → Ω → ℝ) (R S : Ω → WithTop ℝ)
    (ω : Ω) (hRS : R ω ≤ S ω)
    (hSC : S ω < ExtendedNextRing.after arrival R ω) :
    ExtendedNextRing.after arrival S ω = ExtendedNextRing.after arrival R ω := by
  classical
  by_cases hex : ∃ k, R ω < (arrival k ω : WithTop ℝ)
  · have hS : S ω < (arrival (Nat.find hex) ω : WithTop ℝ) := by
      simpa only [ExtendedNextRing.after_eq_coe arrival R ω hex] using hSC
    have hexS : ∃ k, S ω < (arrival k ω : WithTop ℝ) := ⟨Nat.find hex, hS⟩
    have hindex : Nat.find hexS = Nat.find hex := by
      apply Nat.le_antisymm
      · exact Nat.find_min' hexS hS
      · exact Nat.find_min' hex (hRS.trans_lt (Nat.find_spec hexS))
    rw [ExtendedNextRing.after_eq_coe arrival S ω hexS,
      ExtendedNextRing.after_eq_coe arrival R ω hex, hindex]
  · have hnoS : ¬ ∃ k, S ω < (arrival k ω : WithTop ℝ) := by
      rintro ⟨k, hk⟩
      exact hex ⟨k, hRS.trans_lt hk⟩
    rw [(ExtendedNextRing.after_eq_top_iff arrival R ω).mpr hex,
      (ExtendedNextRing.after_eq_top_iff arrival S ω).mpr hnoS]

theorem representative_lt_iff {a b : WithTop ℝ} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a < b ↔ a.untopD 0 < b.untopD 0 := by
  lift a to ℝ using ha
  lift b to ℝ using hb
  simp

theorem after_finite_of_cofinal (arrival : Nat → Ω → ℝ) (R : Ω → WithTop ℝ)
    (ω : Ω) (hR : R ω ≠ ⊤) (hcofinal : ∀ r : ℝ, ∃ k, r < arrival k ω) :
    ExtendedNextRing.after arrival R ω ≠ ⊤ :=
  (ExtendedNextRing.after_ne_top_iff arrival R ω).mpr
    (ExtendedNextRing.future_of_finite_cofinal arrival R ω hR hcofinal)

theorem waiting_eq_sub (arrival : Nat → Ω → ℝ) (R : Ω → WithTop ℝ)
    (ω : Ω) (hR : R ω ≠ ⊤) (hC : ExtendedNextRing.after arrival R ω ≠ ⊤) :
    waiting arrival R ω = (ExtendedNextRing.after arrival R ω).untopD 0 - (R ω).untopD 0 := by
  apply max_eq_left
  exact sub_nonneg.mpr ((representative_lt_iff hR hC).mp
    (ExtendedNextRing.ready_lt_after arrival R ω hR)).le

theorem waiting_positive (arrival : Nat → Ω → ℝ) (R : Ω → WithTop ℝ)
    (ω : Ω) (hR : R ω ≠ ⊤) (hcofinal : ∀ r : ℝ, ∃ k, r < arrival k ω) :
    0 < waiting arrival R ω := by
  have hC := after_finite_of_cofinal arrival R ω hR hcofinal
  rw [waiting_eq_sub arrival R ω hR hC]
  exact sub_pos.mpr ((representative_lt_iff hR hC).mp
    (ExtendedNextRing.ready_lt_after arrival R ω hR))

/-- An upper round smaller than the waiting gap still lies before the original next ring. -/
theorem after_approx_eq_of_mesh_lt (arrival : Nat → Ω → ℝ) (R : Ω → WithTop ℝ)
    (ω : Ω) {δ : ℝ} (hδ : 0 < δ) (hR : R ω ≠ ⊤) (hRpos : 0 ≤ R ω)
    (hcofinal : ∀ r : ℝ, ∃ k, r < arrival k ω) (hmesh : δ < waiting arrival R ω) :
    ExtendedNextRing.after arrival (UpperStoppingApprox.approx δ R) ω =
      ExtendedNextRing.after arrival R ω := by
  have hC := after_finite_of_cofinal arrival R ω hR hcofinal
  have hQ : UpperStoppingApprox.round δ (R ω) ≠ ⊤ :=
    (UpperStoppingApprox.round_ne_top_iff hδ (R ω)).mpr hR
  have herr := UpperStoppingApprox.representative_error hδ (R ω) hR hRpos
  have hsub := waiting_eq_sub arrival R ω hR hC
  apply after_eq_of_between arrival R (UpperStoppingApprox.approx δ R) ω
    (UpperStoppingApprox.le_round δ (R ω))
  apply (representative_lt_iff hQ hC).mpr
  linarith

/-- Once the ring selection is stable, the rounded wait differs only by the readiness error. -/
theorem waiting_approx_error_of_mesh_lt (arrival : Nat → Ω → ℝ) (R : Ω → WithTop ℝ)
    (ω : Ω) {δ : ℝ} (hδ : 0 < δ) (hR : R ω ≠ ⊤) (hRpos : 0 ≤ R ω)
    (hcofinal : ∀ r : ℝ, ∃ k, r < arrival k ω) (hmesh : δ < waiting arrival R ω) :
    0 ≤ waiting arrival R ω - waiting arrival (UpperStoppingApprox.approx δ R) ω ∧
      waiting arrival R ω - waiting arrival (UpperStoppingApprox.approx δ R) ω < δ := by
  have hC := after_finite_of_cofinal arrival R ω hR hcofinal
  have hQ : UpperStoppingApprox.approx δ R ω ≠ ⊤ :=
    (UpperStoppingApprox.round_ne_top_iff hδ (R ω)).mpr hR
  have hstable := after_approx_eq_of_mesh_lt arrival R ω hδ hR hRpos hcofinal hmesh
  have hCQ : ExtendedNextRing.after arrival (UpperStoppingApprox.approx δ R) ω ≠ ⊤ := by
    rw [hstable]
    exact hC
  rw [waiting_eq_sub arrival R ω hR hC,
    waiting_eq_sub arrival (UpperStoppingApprox.approx δ R) ω hQ hCQ, hstable]
  have herr := UpperStoppingApprox.representative_error hδ (R ω) hR hRpos
  simp only [UpperStoppingApprox.approx]
  constructor <;> linarith

theorem after_approx_eventually_eq (arrival : Nat → Ω → ℝ) (R : Ω → WithTop ℝ)
    (ω : Ω) (δ : Nat → ℝ) (hδpos : ∀ m, 0 < δ m)
    (hδlimit : Tendsto δ atTop (𝓝 0)) (hR : R ω ≠ ⊤) (hRpos : 0 ≤ R ω)
    (hcofinal : ∀ r : ℝ, ∃ k, r < arrival k ω) :
    ∀ᶠ m in atTop, ExtendedNextRing.after arrival (UpperStoppingApprox.approx (δ m) R) ω =
      ExtendedNextRing.after arrival R ω := by
  have hsmall := hδlimit.eventually_lt_const (waiting_positive arrival R ω hR hcofinal)
  exact hsmall.mono fun m hm =>
    after_approx_eq_of_mesh_lt arrival R ω (hδpos m) hR hRpos hcofinal hm

theorem waiting_approx_error_eventually (arrival : Nat → Ω → ℝ) (R : Ω → WithTop ℝ)
    (ω : Ω) (δ : Nat → ℝ) (hδpos : ∀ m, 0 < δ m)
    (hδlimit : Tendsto δ atTop (𝓝 0)) (hR : R ω ≠ ⊤) (hRpos : 0 ≤ R ω)
    (hcofinal : ∀ r : ℝ, ∃ k, r < arrival k ω) :
    ∀ᶠ m in atTop,
      0 ≤ waiting arrival R ω - waiting arrival (UpperStoppingApprox.approx (δ m) R) ω ∧
        waiting arrival R ω - waiting arrival (UpperStoppingApprox.approx (δ m) R) ω < δ m := by
  have hsmall := hδlimit.eventually_lt_const (waiting_positive arrival R ω hR hcofinal)
  exact hsmall.mono fun m hm =>
    waiting_approx_error_of_mesh_lt arrival R ω (hδpos m) hR hRpos hcofinal hm

/-- Strict survival events are eventually equal, including at the boundary `waiting = t`.
No atomlessness or distribution assumption is needed; the approximation is from below. -/
theorem waiting_survival_eventually_iff (arrival : Nat → Ω → ℝ) (R : Ω → WithTop ℝ)
    (ω : Ω) (δ : Nat → ℝ) (hδpos : ∀ m, 0 < δ m)
    (hδlimit : Tendsto δ atTop (𝓝 0)) (hR : R ω ≠ ⊤) (hRpos : 0 ≤ R ω)
    (hcofinal : ∀ r : ℝ, ∃ k, r < arrival k ω) (t : ℝ) :
    ∀ᶠ m in atTop, (t < waiting arrival (UpperStoppingApprox.approx (δ m) R) ω) ↔
      t < waiting arrival R ω := by
  have herr := waiting_approx_error_eventually arrival R ω δ hδpos hδlimit hR hRpos hcofinal
  by_cases ht : t < waiting arrival R ω
  · have hsmall := hδlimit.eventually_lt_const (sub_pos.mpr ht)
    filter_upwards [herr, hsmall] with m hm hs
    constructor
    · exact fun _ => ht
    · intro _
      linarith [hm.2]
  · filter_upwards [herr] with m hm
    constructor
    · intro h
      have hle : waiting arrival R ω ≤ t := le_of_not_gt ht
      linarith [hm.1]
    · exact fun h => (ht h).elim

def survivalIndicator (arrival : Nat → Ω → ℝ) (R : Ω → WithTop ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  if t < waiting arrival R ω then 1 else 0

theorem survivalIndicator_tendsto (arrival : Nat → Ω → ℝ) (R : Ω → WithTop ℝ)
    (ω : Ω) (δ : Nat → ℝ) (hδpos : ∀ m, 0 < δ m)
    (hδlimit : Tendsto δ atTop (𝓝 0)) (hR : R ω ≠ ⊤) (hRpos : 0 ≤ R ω)
    (hcofinal : ∀ r : ℝ, ∃ k, r < arrival k ω) (t : ℝ) :
    Tendsto (fun m => survivalIndicator arrival (UpperStoppingApprox.approx (δ m) R) t ω)
      atTop (𝓝 (survivalIndicator arrival R t ω)) := by
  have heq : (fun m => survivalIndicator arrival (UpperStoppingApprox.approx (δ m) R) t ω)
      =ᶠ[atTop] fun _ => survivalIndicator arrival R t ω := by
    filter_upwards [waiting_survival_eventually_iff arrival R ω δ hδpos hδlimit
      hR hRpos hcofinal t] with m hm
    simp only [survivalIndicator, hm]
  exact (tendsto_congr' heq).mpr tendsto_const_nhds

theorem survivalIndicator_tendsto_ae {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (arrival : Nat → Ω → ℝ) (R : Ω → WithTop ℝ)
    (δ : Nat → ℝ) (hδpos : ∀ m, 0 < δ m) (hδlimit : Tendsto δ atTop (𝓝 0))
    (hR : ∀ᵐ ω ∂μ, R ω ≠ ⊤) (hRpos : ∀ᵐ ω ∂μ, 0 ≤ R ω)
    (hcofinal : ∀ᵐ ω ∂μ, ∀ r : ℝ, ∃ k, r < arrival k ω) (t : ℝ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun m => survivalIndicator arrival (UpperStoppingApprox.approx (δ m) R) t ω)
      atTop (𝓝 (survivalIndicator arrival R t ω)) := by
  filter_upwards [hR, hRpos, hcofinal] with ω hr hp hc
  exact survivalIndicator_tendsto arrival R ω δ hδpos hδlimit hr hp hc t

theorem clock_survivalIndicator_tendsto_ae {V : Type*} [Countable V] (v : V)
    (R : ExponentialClocks.Sample V → WithTop ℝ)
    (δ : Nat → ℝ) (hδpos : ∀ m, 0 < δ m) (hδlimit : Tendsto δ atTop (𝓝 0))
    (hR : ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, R ω ≠ ⊤)
    (hRpos : ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, 0 ≤ R ω) (t : ℝ) :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, Tendsto
      (fun m => survivalIndicator (ArrivalFiltration.chronologicalArrival v)
        (UpperStoppingApprox.approx (δ m) R) t ω) atTop
      (𝓝 (survivalIndicator (ArrivalFiltration.chronologicalArrival v) R t ω)) := by
  apply survivalIndicator_tendsto_ae _ R δ hδpos hδlimit hR hRpos
  filter_upwards [ArrivalFiltration.chronologicalArrival_unbounded_ae (V := V)] with ω hω
  intro r
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_atTop.mp (hω v)) (r + 1))
  exact ⟨N, lt_of_lt_of_le (by linarith) (hN N le_rfl)⟩

end MathResearchAnalysis.ClockWaitingLimit
