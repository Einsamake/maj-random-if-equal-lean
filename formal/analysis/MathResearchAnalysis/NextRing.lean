module

public import Mathlib.Probability.Process.Stopping

set_option autoImplicit false

/-!
# A strict next ring constructed from arrival stopping times

An arrival sequence is an input, not an already constructed Poisson process.
The least arrival index strictly after readiness defines the next ring. Its
stopping-time property is proved from the stopping times of the individual
arrivals and readiness, rather than supplied as an assumption. Chronological
monotonicity of the arrival sequence suffices; strict monotonicity is not needed.

The extended construction returns infinity when no later arrival exists. An
almost-everywhere cofinality assumption then proves almost-everywhere finiteness.
Neither cofinality nor the arrival stopping times are established for actual
Poisson clocks here, and no strong Markov or waiting-time law is claimed.
-/

public noncomputable section

open MeasureTheory

namespace MathResearchAnalysis.NextRing

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Least index whose real-valued arrival is strictly after readiness. -/
def nextIndex (arrival : Nat → Ω → ℝ) (ready : Ω → ℝ)
    (hex : ∀ ω, ∃ k, ready ω < arrival k ω) (ω : Ω) : Nat :=
  Nat.find (hex ω)

/-- A real-valued next ring, when a future arrival exists on every sample path. -/
def nextRing (arrival : Nat → Ω → ℝ) (ready : Ω → ℝ)
    (hex : ∀ ω, ∃ k, ready ω < arrival k ω) (ω : Ω) : ℝ :=
  arrival (nextIndex arrival ready hex ω) ω

theorem ready_lt_nextRing (arrival : Nat → Ω → ℝ) (ready : Ω → ℝ)
    (hex : ∀ ω, ∃ k, ready ω < arrival k ω) (ω : Ω) :
    ready ω < nextRing arrival ready hex ω :=
  Nat.find_spec (hex ω)

theorem nextIndex_le (arrival : Nat → Ω → ℝ) (ready : Ω → ℝ)
    (hex : ∀ ω, ∃ k, ready ω < arrival k ω) (ω : Ω) (k : Nat)
    (hk : ready ω < arrival k ω) : nextIndex arrival ready hex ω ≤ k :=
  Nat.find_min' (hex ω) hk

theorem nextRing_le_arrival (arrival : Nat → Ω → ℝ) (ready : Ω → ℝ)
    (hex : ∀ ω, ∃ k, ready ω < arrival k ω)
    (hmono : ∀ ω, Monotone (fun k => arrival k ω)) (ω : Ω) (k : Nat)
    (hk : ready ω < arrival k ω) : nextRing arrival ready hex ω ≤ arrival k ω :=
  hmono ω (nextIndex_le arrival ready hex ω k hk)

/-- The event of a completed next ring is a countable union of arrival events. -/
theorem nextRing_le_iff (arrival : Nat → Ω → ℝ) (ready : Ω → ℝ)
    (hex : ∀ ω, ∃ k, ready ω < arrival k ω)
    (hmono : ∀ ω, Monotone (fun k => arrival k ω)) (ω : Ω) (t : ℝ) :
    nextRing arrival ready hex ω ≤ t ↔
      ∃ k, ready ω < arrival k ω ∧ arrival k ω ≤ t := by
  constructor
  · intro ht
    exact ⟨nextIndex arrival ready hex ω, ready_lt_nextRing arrival ready hex ω, ht⟩
  · rintro ⟨k, hk, hkt⟩
    exact (nextRing_le_arrival arrival ready hex hmono ω k hk).trans hkt

/-- Comparing two stopping times and restricting to an arrival before `t`
gives an event already measurable at deterministic time `t`. -/
theorem measurableSet_ready_lt_arrival_le (clocks : Filtration ℝ mΩ)
    (ready arrival : Ω → ℝ)
    (hr : IsStoppingTime clocks (fun ω => (ready ω : WithTop ℝ)))
    (ha : IsStoppingTime clocks (fun ω => (arrival ω : WithTop ℝ))) (t : ℝ) :
    MeasurableSet[clocks t] {ω | ready ω < arrival ω ∧ arrival ω ≤ t} := by
  have hs : MeasurableSet[ha.measurableSpace] {ω | ready ω < arrival ω} := by
    convert (ha.measurableSet_le_stopping_time hr).compl using 1
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, WithTop.coe_le_coe, not_le]
  have hi := ((ha.measurableSet _).mp hs).2 t
  convert hi using 1
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, WithTop.coe_le_coe]

/-- The constructed next ring is a stopping time in the common filtration. -/
theorem nextRing_isStoppingTime (clocks : Filtration ℝ mΩ)
    (arrival : Nat → Ω → ℝ) (ready : Ω → ℝ)
    (hex : ∀ ω, ∃ k, ready ω < arrival k ω)
    (hmono : ∀ ω, Monotone (fun k => arrival k ω))
    (hr : IsStoppingTime clocks (fun ω => (ready ω : WithTop ℝ)))
    (ha : ∀ k, IsStoppingTime clocks (fun ω => (arrival k ω : WithTop ℝ))) :
    IsStoppingTime clocks (fun ω => (nextRing arrival ready hex ω : WithTop ℝ)) := by
  intro t
  have heq : {ω | (nextRing arrival ready hex ω : WithTop ℝ) ≤ t} =
      ⋃ k : Nat, {ω | ready ω < arrival k ω ∧ arrival k ω ≤ t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe, Set.mem_iUnion]
    exact nextRing_le_iff arrival ready hex hmono ω t
  rw [heq]
  exact MeasurableSet.iUnion fun k =>
    measurableSet_ready_lt_arrival_le clocks ready (arrival k) hr (ha k) t

theorem nextRing_ne_top (arrival : Nat → Ω → ℝ) (ready : Ω → ℝ)
    (hex : ∀ ω, ∃ k, ready ω < arrival k ω) (ω : Ω) :
    (nextRing arrival ready hex ω : WithTop ℝ) ≠ ⊤ :=
  WithTop.coe_ne_top

/-- Pointwise unbounded arrival paths supply existence for any real readiness. -/
theorem future_arrival_of_cofinal (arrival : Nat → Ω → ℝ) (ready : Ω → ℝ)
    (hcofinal : ∀ ω r, ∃ k, r < arrival k ω) :
    ∀ ω, ∃ k, ready ω < arrival k ω :=
  fun ω => hcofinal ω (ready ω)

/-- Increasing readiness cannot move the selected chronological arrival earlier. -/
theorem nextRing_mono_readiness (arrival : Nat → Ω → ℝ) (ready₁ ready₂ : Ω → ℝ)
    (hex₁ : ∀ ω, ∃ k, ready₁ ω < arrival k ω)
    (hex₂ : ∀ ω, ∃ k, ready₂ ω < arrival k ω)
    (hmono : ∀ ω, Monotone (fun k => arrival k ω))
    (hready : ∀ ω, ready₁ ω ≤ ready₂ ω) (ω : Ω) :
    nextRing arrival ready₁ hex₁ ω ≤ nextRing arrival ready₂ hex₂ ω := by
  exact nextRing_le_arrival arrival ready₁ hex₁ hmono ω
    (nextIndex arrival ready₂ hex₂ ω)
    ((hready ω).trans_lt (ready_lt_nextRing arrival ready₂ hex₂ ω))

/-- A later readiness after a selected arrival forces a distinct selected index. -/
theorem nextIndex_lt_of_nextRing_le_ready (arrival : Nat → Ω → ℝ)
    (ready₁ ready₂ : Ω → ℝ)
    (hex₁ : ∀ ω, ∃ k, ready₁ ω < arrival k ω)
    (hex₂ : ∀ ω, ∃ k, ready₂ ω < arrival k ω)
    (hmono : ∀ ω, Monotone (fun k => arrival k ω)) (ω : Ω)
    (hsep : nextRing arrival ready₁ hex₁ ω ≤ ready₂ ω) :
    nextIndex arrival ready₁ hex₁ ω < nextIndex arrival ready₂ hex₂ ω := by
  by_contra hnot
  have hle := hmono ω (Nat.le_of_not_gt hnot)
  exact (not_lt_of_ge (hle.trans hsep)) (ready_lt_nextRing arrival ready₂ hex₂ ω)

/-- The total extended next ring retains infinity on paths without future arrivals. -/
def extendedNextRing (arrival : Nat → Ω → ℝ) (ready : Ω → ℝ)
    (ω : Ω) : WithTop ℝ := by
  classical
  exact if hex : ∃ k, ready ω < arrival k ω then
    (arrival (Nat.find hex) ω : WithTop ℝ)
  else ⊤

theorem extendedNextRing_eq_coe (arrival : Nat → Ω → ℝ) (ready : Ω → ℝ)
    (ω : Ω) (hex : ∃ k, ready ω < arrival k ω) :
    extendedNextRing arrival ready ω = (arrival (Nat.find hex) ω : WithTop ℝ) := by
  simp only [extendedNextRing, dite_eq_left hex]

theorem extendedNextRing_eq_nextRing (arrival : Nat → Ω → ℝ) (ready : Ω → ℝ)
    (hex : ∀ ω, ∃ k, ready ω < arrival k ω) (ω : Ω) :
    extendedNextRing arrival ready ω = (nextRing arrival ready hex ω : WithTop ℝ) :=
  extendedNextRing_eq_coe arrival ready ω (hex ω)

theorem extendedNextRing_eq_top_iff (arrival : Nat → Ω → ℝ) (ready : Ω → ℝ)
    (ω : Ω) : extendedNextRing arrival ready ω = ⊤ ↔
      ¬ ∃ k, ready ω < arrival k ω := by
  classical
  by_cases hex : ∃ k, ready ω < arrival k ω <;> simp [extendedNextRing, hex]

theorem ready_lt_extendedNextRing (arrival : Nat → Ω → ℝ) (ready : Ω → ℝ)
    (ω : Ω) : (ready ω : WithTop ℝ) < extendedNextRing arrival ready ω := by
  classical
  by_cases hex : ∃ k, ready ω < arrival k ω
  · rw [extendedNextRing_eq_coe arrival ready ω hex]
    exact WithTop.coe_lt_coe.mpr (Nat.find_spec hex)
  · simp only [extendedNextRing, dite_eq_right hex]
    exact WithTop.coe_lt_top _

theorem extendedNextRing_le_iff (arrival : Nat → Ω → ℝ) (ready : Ω → ℝ)
    (hmono : ∀ ω, Monotone (fun k => arrival k ω)) (ω : Ω) (t : ℝ) :
    extendedNextRing arrival ready ω ≤ (t : WithTop ℝ) ↔
      ∃ k, ready ω < arrival k ω ∧ arrival k ω ≤ t := by
  classical
  by_cases hex : ∃ k, ready ω < arrival k ω
  · rw [extendedNextRing_eq_coe arrival ready ω hex, WithTop.coe_le_coe]
    constructor
    · exact fun ht => ⟨Nat.find hex, Nat.find_spec hex, ht⟩
    · rintro ⟨k, hk, hkt⟩
      exact (hmono ω (Nat.find_min' hex hk)).trans hkt
  · simp only [extendedNextRing, dite_eq_right hex, WithTop.not_top_le_coe, false_iff]
    rintro ⟨k, hk, _⟩
    exact hex ⟨k, hk⟩

/-- No pointwise finiteness assumption is needed for this stopping-time theorem. -/
theorem extendedNextRing_isStoppingTime (clocks : Filtration ℝ mΩ)
    (arrival : Nat → Ω → ℝ) (ready : Ω → ℝ)
    (hmono : ∀ ω, Monotone (fun k => arrival k ω))
    (hr : IsStoppingTime clocks (fun ω => (ready ω : WithTop ℝ)))
    (ha : ∀ k, IsStoppingTime clocks (fun ω => (arrival k ω : WithTop ℝ))) :
    IsStoppingTime clocks (extendedNextRing arrival ready) := by
  intro t
  have heq : {ω | extendedNextRing arrival ready ω ≤ (t : WithTop ℝ)} =
      ⋃ k : Nat, {ω | ready ω < arrival k ω ∧ arrival k ω ≤ t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact extendedNextRing_le_iff arrival ready hmono ω t
  rw [heq]
  exact MeasurableSet.iUnion fun k =>
    measurableSet_ready_lt_arrival_le clocks ready (arrival k) hr (ha k) t

theorem extendedNextRing_ne_top_iff (arrival : Nat → Ω → ℝ) (ready : Ω → ℝ)
    (ω : Ω) : extendedNextRing arrival ready ω ≠ ⊤ ↔
      ∃ k, ready ω < arrival k ω := by
  simp only [Ne, extendedNextRing_eq_top_iff, not_not]

/-- Almost-everywhere future arrivals prove almost-everywhere finiteness.
No finiteness of the next ring is assumed in this result. -/
theorem extendedNextRing_ae_ne_top {μ : Measure Ω} (arrival : Nat → Ω → ℝ)
    (ready : Ω → ℝ) (hfuture : ∀ᵐ ω ∂μ, ∃ k, ready ω < arrival k ω) :
    ∀ᵐ ω ∂μ, extendedNextRing arrival ready ω ≠ ⊤ :=
  hfuture.mono fun ω h => (extendedNextRing_ne_top_iff arrival ready ω).mpr h

theorem extendedNextRing_ae_finite_of_cofinal {μ : Measure Ω}
    (arrival : Nat → Ω → ℝ) (ready : Ω → ℝ)
    (hcofinal : ∀ᵐ ω ∂μ, ∀ r : ℝ, ∃ k, r < arrival k ω) :
    ∀ᵐ ω ∂μ, extendedNextRing arrival ready ω ≠ ⊤ :=
  extendedNextRing_ae_ne_top arrival ready (hcofinal.mono fun ω h => h (ready ω))

theorem measure_extendedNextRing_top_eq_zero {μ : Measure Ω}
    (arrival : Nat → Ω → ℝ) (ready : Ω → ℝ)
    (hfuture : ∀ᵐ ω ∂μ, ∃ k, ready ω < arrival k ω) :
    μ {ω | extendedNextRing arrival ready ω = ⊤} = 0 := by
  simpa only [not_not] using
    (ae_iff.mp (extendedNextRing_ae_ne_top arrival ready hfuture))

end MathResearchAnalysis.NextRing
