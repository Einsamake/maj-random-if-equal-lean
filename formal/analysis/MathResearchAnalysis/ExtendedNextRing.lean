module

public import MathResearchAnalysis.NextRing

set_option autoImplicit false

/-!
# Strict next arrivals after possibly infinite readiness

This construction accepts `WithTop` readiness without substituting an arbitrary
real value on exceptional infinite paths. The earliest arrival strictly after
readiness is selected by `Nat.find`; when there is no such arrival, the result
is infinity. Its stopping-time property is deduced from those of readiness and
the individual arrivals. Almost-everywhere finite readiness and cofinal arrival
paths suffice to prove almost-everywhere finite completion.

The arrival sequence, its monotonicity, its individual stopping-time properties,
and its cofinality remain inputs. This module proves neither the construction
of actual Poisson clocks nor strong Markov or an exponential waiting-time law.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.ExtendedNextRing

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- First arrival strictly after extended readiness; infinity if none exists. -/
def after (arrival : Nat → Ω → ℝ) (ready : Ω → WithTop ℝ)
    (ω : Ω) : WithTop ℝ := by
  classical
  exact if hex : ∃ k, ready ω < (arrival k ω : WithTop ℝ) then
    (arrival (Nat.find hex) ω : WithTop ℝ)
  else ⊤

theorem after_eq_coe (arrival : Nat → Ω → ℝ) (ready : Ω → WithTop ℝ)
    (ω : Ω) (hex : ∃ k, ready ω < (arrival k ω : WithTop ℝ)) :
    after arrival ready ω = (arrival (Nat.find hex) ω : WithTop ℝ) := by
  simp only [after, dite_eq_left hex]

theorem after_eq_top_iff (arrival : Nat → Ω → ℝ) (ready : Ω → WithTop ℝ)
    (ω : Ω) : after arrival ready ω = ⊤ ↔
      ¬ ∃ k, ready ω < (arrival k ω : WithTop ℝ) := by
  classical
  by_cases hex : ∃ k, ready ω < (arrival k ω : WithTop ℝ) <;> simp [after, hex]

theorem after_ne_top_iff (arrival : Nat → Ω → ℝ) (ready : Ω → WithTop ℝ)
    (ω : Ω) : after arrival ready ω ≠ ⊤ ↔
      ∃ k, ready ω < (arrival k ω : WithTop ℝ) := by
  simp only [Ne, after_eq_top_iff, not_not]

theorem after_eq_top_of_ready_eq_top (arrival : Nat → Ω → ℝ)
    (ready : Ω → WithTop ℝ) (ω : Ω) (htop : ready ω = ⊤) :
    after arrival ready ω = ⊤ := by
  apply (after_eq_top_iff arrival ready ω).mpr
  simp only [htop, not_top_lt, exists_false, not_false_eq_true]

/-- Readiness is strictly earlier whenever it is finite, even if completion is infinite. -/
theorem ready_lt_after (arrival : Nat → Ω → ℝ) (ready : Ω → WithTop ℝ)
    (ω : Ω) (hfinite : ready ω ≠ ⊤) : ready ω < after arrival ready ω := by
  classical
  by_cases hex : ∃ k, ready ω < (arrival k ω : WithTop ℝ)
  · rw [after_eq_coe arrival ready ω hex]
    exact Nat.find_spec hex
  · simp only [after, dite_eq_right hex]
    exact WithTop.lt_top_iff_ne_top.mpr hfinite

theorem ready_le_after (arrival : Nat → Ω → ℝ) (ready : Ω → WithTop ℝ)
    (ω : Ω) : ready ω ≤ after arrival ready ω := by
  by_cases hfinite : ready ω ≠ ⊤
  · exact (ready_lt_after arrival ready ω hfinite).le
  · have htop : ready ω = ⊤ := not_not.mp hfinite
    rw [after_eq_top_of_ready_eq_top arrival ready ω htop, htop]

theorem after_nonneg (arrival : Nat → Ω → ℝ) (ready : Ω → WithTop ℝ)
    (ω : Ω) (hready : 0 ≤ ready ω) : 0 ≤ after arrival ready ω :=
  hready.trans (ready_le_after arrival ready ω)

theorem after_le_arrival (arrival : Nat → Ω → ℝ) (ready : Ω → WithTop ℝ)
    (hmono : ∀ ω, Monotone (fun k => arrival k ω)) (ω : Ω) (k : Nat)
    (hk : ready ω < (arrival k ω : WithTop ℝ)) :
    after arrival ready ω ≤ (arrival k ω : WithTop ℝ) := by
  have hex : ∃ k, ready ω < (arrival k ω : WithTop ℝ) := ⟨k, hk⟩
  rw [after_eq_coe arrival ready ω hex]
  exact WithTop.coe_le_coe.mpr (hmono ω (Nat.find_min' hex hk))

/-- Completion before `t` is a countable union of strict arrival comparisons. -/
theorem after_le_iff (arrival : Nat → Ω → ℝ) (ready : Ω → WithTop ℝ)
    (hmono : ∀ ω, Monotone (fun k => arrival k ω)) (ω : Ω) (t : ℝ) :
    after arrival ready ω ≤ (t : WithTop ℝ) ↔
      ∃ k, ready ω < (arrival k ω : WithTop ℝ) ∧ arrival k ω ≤ t := by
  classical
  by_cases hex : ∃ k, ready ω < (arrival k ω : WithTop ℝ)
  · rw [after_eq_coe arrival ready ω hex, WithTop.coe_le_coe]
    constructor
    · exact fun ht => ⟨Nat.find hex, Nat.find_spec hex, ht⟩
    · rintro ⟨k, hk, hkt⟩
      exact (hmono ω (Nat.find_min' hex hk)).trans hkt
  · simp only [after, dite_eq_right hex, WithTop.not_top_le_coe, false_iff]
    rintro ⟨k, hk, _⟩
    exact hex ⟨k, hk⟩

theorem measurableSet_ready_lt_arrival_le (clocks : Filtration ℝ mΩ)
    (ready : Ω → WithTop ℝ) (arrival : Ω → ℝ)
    (hr : IsStoppingTime clocks ready)
    (ha : IsStoppingTime clocks (fun ω => (arrival ω : WithTop ℝ))) (t : ℝ) :
    MeasurableSet[clocks t]
      {ω | ready ω < (arrival ω : WithTop ℝ) ∧ arrival ω ≤ t} := by
  have hs : MeasurableSet[ha.measurableSpace]
      {ω | ready ω < (arrival ω : WithTop ℝ)} := by
    convert (ha.measurableSet_le_stopping_time hr).compl using 1
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  have hi := ((ha.measurableSet _).mp hs).2 t
  convert hi using 1
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, WithTop.coe_le_coe]

/-- The completion stopping time is proved without any finiteness assumption. -/
theorem after_isStoppingTime (clocks : Filtration ℝ mΩ)
    (arrival : Nat → Ω → ℝ) (ready : Ω → WithTop ℝ)
    (hmono : ∀ ω, Monotone (fun k => arrival k ω))
    (hr : IsStoppingTime clocks ready)
    (ha : ∀ k, IsStoppingTime clocks (fun ω => (arrival k ω : WithTop ℝ))) :
    IsStoppingTime clocks (after arrival ready) := by
  intro t
  have heq : {ω | after arrival ready ω ≤ (t : WithTop ℝ)} =
      ⋃ k : Nat, {ω | ready ω < (arrival k ω : WithTop ℝ) ∧ arrival k ω ≤ t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact after_le_iff arrival ready hmono ω t
  rw [heq]
  exact MeasurableSet.iUnion fun k =>
    measurableSet_ready_lt_arrival_le clocks ready (arrival k) hr (ha k) t

theorem future_of_finite_cofinal (arrival : Nat → Ω → ℝ)
    (ready : Ω → WithTop ℝ) (ω : Ω) (hready : ready ω ≠ ⊤)
    (hcofinal : ∀ r : ℝ, ∃ k, r < arrival k ω) :
    ∃ k, ready ω < (arrival k ω : WithTop ℝ) := by
  lift ready ω to ℝ using hready with r hr
  obtain ⟨k, hk⟩ := hcofinal r
  exact ⟨k, WithTop.coe_lt_coe.mpr hk⟩

/-- The input is finite readiness, not finite completion; no finiteness is assumed
for the constructed `after` function. -/
theorem after_ae_finite {μ : Measure Ω} (arrival : Nat → Ω → ℝ)
    (ready : Ω → WithTop ℝ) (hready : ∀ᵐ ω ∂μ, ready ω ≠ ⊤)
    (hcofinal : ∀ᵐ ω ∂μ, ∀ r : ℝ, ∃ k, r < arrival k ω) :
    ∀ᵐ ω ∂μ, after arrival ready ω ≠ ⊤ := by
  filter_upwards [hready, hcofinal] with ω hr hc
  exact (after_ne_top_iff arrival ready ω).mpr
    (future_of_finite_cofinal arrival ready ω hr hc)

theorem measure_after_top_eq_zero {μ : Measure Ω} (arrival : Nat → Ω → ℝ)
    (ready : Ω → WithTop ℝ) (hready : ∀ᵐ ω ∂μ, ready ω ≠ ⊤)
    (hcofinal : ∀ᵐ ω ∂μ, ∀ r : ℝ, ∃ k, r < arrival k ω) :
    μ {ω | after arrival ready ω = ⊤} = 0 := by
  simpa only [not_not] using (ae_iff.mp (after_ae_finite arrival ready hready hcofinal))

theorem after_mono_readiness (arrival : Nat → Ω → ℝ)
    (ready₁ ready₂ : Ω → WithTop ℝ)
    (hmono : ∀ ω, Monotone (fun k => arrival k ω))
    (hready : ∀ ω, ready₁ ω ≤ ready₂ ω) (ω : Ω) :
    after arrival ready₁ ω ≤ after arrival ready₂ ω := by
  by_cases hfinite : after arrival ready₂ ω ≠ ⊤
  · obtain ⟨k, hk⟩ := (after_ne_top_iff arrival ready₂ ω).mp hfinite
    have hex : ∃ k, ready₂ ω < (arrival k ω : WithTop ℝ) := ⟨k, hk⟩
    rw [after_eq_coe arrival ready₂ ω hex]
    exact after_le_arrival arrival ready₁ hmono ω (Nat.find hex)
      ((hready ω).trans_lt (Nat.find_spec hex))
  · have htop : after arrival ready₂ ω = ⊤ := not_not.mp hfinite
    rw [htop]
    exact le_top

/-- The index is meaningful when `after` is finite; the default on other paths
does not replace the extended completion time. -/
def selectedIndex (arrival : Nat → Ω → ℝ) (ready : Ω → WithTop ℝ)
    (ω : Ω) : Nat := by
  classical
  exact if hex : ∃ k, ready ω < (arrival k ω : WithTop ℝ) then Nat.find hex else 0

theorem after_eq_selected_arrival (arrival : Nat → Ω → ℝ)
    (ready : Ω → WithTop ℝ) (ω : Ω) (hfinite : after arrival ready ω ≠ ⊤) :
    after arrival ready ω = (arrival (selectedIndex arrival ready ω) ω : WithTop ℝ) := by
  have hex := (after_ne_top_iff arrival ready ω).mp hfinite
  simp only [after, selectedIndex, dite_eq_left hex]

/-- Separated finite tasks select distinct, ordered indices on the same clock. -/
theorem selectedIndex_lt_of_after_le_ready (arrival : Nat → Ω → ℝ)
    (ready₁ ready₂ : Ω → WithTop ℝ)
    (hmono : ∀ ω, Monotone (fun k => arrival k ω)) (ω : Ω)
    (hsep : after arrival ready₁ ω ≤ ready₂ ω)
    (hfinite : after arrival ready₂ ω ≠ ⊤) :
    selectedIndex arrival ready₁ ω < selectedIndex arrival ready₂ ω := by
  have hr₂ : ready₂ ω ≠ ⊤ := ne_top_of_le_ne_top hfinite (ready_le_after arrival ready₂ ω)
  have hf₁ : after arrival ready₁ ω ≠ ⊤ := ne_top_of_le_ne_top hr₂ hsep
  have hlt := hsep.trans_lt (ready_lt_after arrival ready₂ ω hr₂)
  by_contra hnot
  have hle := hmono ω (Nat.le_of_not_gt hnot)
  have hle' : after arrival ready₂ ω ≤ after arrival ready₁ ω := by
    rw [after_eq_selected_arrival arrival ready₂ ω hfinite,
      after_eq_selected_arrival arrival ready₁ ω hf₁]
    exact WithTop.coe_le_coe.mpr hle
  exact (not_lt_of_ge hle') hlt

/-- On real readiness this construction agrees with the previous extended interface. -/
theorem after_eq_extendedNextRing (arrival : Nat → Ω → ℝ) (ready : Ω → ℝ)
    (ω : Ω) : after arrival (fun ω => (ready ω : WithTop ℝ)) ω =
      NextRing.extendedNextRing arrival ready ω := by
  classical
  by_cases hex : ∃ k, ready ω < arrival k ω
  · have hex' : ∃ k, (ready ω : WithTop ℝ) < (arrival k ω : WithTop ℝ) := by
      simpa only [WithTop.coe_lt_coe] using hex
    rw [after_eq_coe arrival (fun ω => (ready ω : WithTop ℝ)) ω hex',
      NextRing.extendedNextRing_eq_coe arrival ready ω hex]
    congr 2
    exact Nat.find_congr' WithTop.coe_lt_coe
  · have hex' : ¬ ∃ k, (ready ω : WithTop ℝ) < (arrival k ω : WithTop ℝ) := by
      simpa only [WithTop.coe_lt_coe] using hex
    rw [(after_eq_top_iff arrival (fun ω => (ready ω : WithTop ℝ)) ω).mpr hex',
      (NextRing.extendedNextRing_eq_top_iff arrival ready ω).mpr hex]

end MathResearchAnalysis.ExtendedNextRing
