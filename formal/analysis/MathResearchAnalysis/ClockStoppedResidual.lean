module

public import MathResearchAnalysis.CountableClockSurvival
public import MathResearchAnalysis.EventMeasureLimit
public import MathResearchAnalysis.ClockReadiness
public import MathResearchAnalysis.TaskClockBridge
public import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

/-!
# Genuine exponential residual waiting at actual stopping times

Countable upper stopping approximations have the true joint survival law.
Their strict survival events eventually agree on finite cofinal clock paths,
including at the threshold boundary. Dominated convergence by one passes the
law to the original stopping time. No right-continuity, independent-increment
or stopped-residual-law assumption is used.
-/

public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace MathResearchAnalysis.ClockStoppedResidual

variable {V : Type*} [Countable V]

@[expose] def mesh (m : Nat) : ℝ := (1 / 2 : ℝ) ^ m

theorem mesh_positive (m : Nat) : 0 < mesh m := pow_pos (by norm_num) m

theorem mesh_tendsto : Tendsto mesh atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The actual shared-history survival law, for every nonnegative a.s. finite stopping time. -/
theorem clock_wait_jointSurvival (v : V)
    (R : ExponentialClocks.Sample V → WithTop ℝ)
    (hR : IsStoppingTime (ArrivalFiltration.clockHistory V) R)
    (hpos : ∀ ω, 0 ≤ R ω)
    (hfinite : ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, R ω ≠ ⊤) :
    @SurvivalLaw.JointSurvival (ExponentialClocks.Sample V) inferInstance
      (ClockWaitingLimit.waiting (ArrivalFiltration.chronologicalArrival v) R)
      hR.measurableSpace (ExponentialClocks.clockMeasure V) := by
  classical
  intro t ht E hE
  let Q : Nat → ExponentialClocks.Sample V → WithTop ℝ :=
    fun m => UpperStoppingApprox.approx (mesh m) R
  have hQ : ∀ m, IsStoppingTime (ArrivalFiltration.clockHistory V) (Q m) :=
    fun m => UpperStoppingApprox.approx_isStoppingTime _ (mesh_positive m).le R hR
  have hQfinite : ∀ m, ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, Q m ω ≠ ⊤ :=
    fun m => hfinite.mono fun ω hω =>
      (UpperStoppingApprox.round_ne_top_iff (mesh_positive m) (R ω)).mpr hω
  have hQE : ∀ m, MeasurableSet[(hQ m).measurableSpace] E := fun m =>
    (hR.measurableSpace_mono (hQ m) (fun ω => UpperStoppingApprox.le_round (mesh m) (R ω))) E hE
  have hEambient : MeasurableSet E := hR.measurableSpace_le E hE
  let events : Nat → Set (ExponentialClocks.Sample V) := fun m => E ∩
    {ω | t < ClockWaitingLimit.waiting (ArrivalFiltration.chronologicalArrival v) (Q m) ω}
  let target : Set (ExponentialClocks.Sample V) := E ∩
    {ω | t < ClockWaitingLimit.waiting (ArrivalFiltration.chronologicalArrival v) R ω}
  have hmeas : ∀ m, MeasurableSet (events m) := fun m => hEambient.inter
    (measurableSet_lt measurable_const
      (CountableClockSurvival.clock_waiting_measurable v (Q m) (hQ m)))
  have htarget : MeasurableSet target := hEambient.inter
    (measurableSet_lt measurable_const (CountableClockSurvival.clock_waiting_measurable v R hR))
  have hevent : ∀ᵐ ω ∂ExponentialClocks.clockMeasure V,
      ∀ᶠ m in atTop, (ω ∈ events m ↔ ω ∈ target) := by
    filter_upwards [hfinite, ClockReadiness.arrival_cofinal_ae v] with ω hr hc
    have h := ClockWaitingLimit.waiting_survival_eventually_iff
      (ArrivalFiltration.chronologicalArrival v) R ω mesh mesh_positive mesh_tendsto
      hr (hpos ω) hc t
    exact h.mono fun m hm => by
      simpa only [events, target, Set.mem_inter_iff, Set.mem_ofPred_eq] using
        (and_congr_right (fun _ => hm) : (ω ∈ E ∧ _) ↔ (ω ∈ E ∧ _))
  have hlimit := EventMeasureLimit.event_measure_tendsto events target hmeas htarget hevent
  have hvalue : ∀ m, ExponentialClocks.clockMeasure V (events m) =
      ENNReal.ofReal (Real.exp (-t)) * ExponentialClocks.clockMeasure V E := by
    intro m
    exact CountableClockSurvival.countable_clock_jointSurvival v (Q m) (hQ m)
      (UpperStoppingApprox.approx_countable_range (mesh m) R)
      (fun ω => UpperStoppingApprox.round_nonnegative (mesh_positive m).le (R ω))
      (hQfinite m) t ht E (hQE m)
  have hconstant : Tendsto (fun m => ExponentialClocks.clockMeasure V (events m)) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (-t)) * ExponentialClocks.clockMeasure V E)) := by
    simpa only [hvalue] using (tendsto_const_nhds : Tendsto
      (fun _ : Nat => ENNReal.ofReal (Real.exp (-t)) * ExponentialClocks.clockMeasure V E)
      atTop (𝓝 _))
  exact tendsto_nhds_unique hlimit hconstant

theorem clock_wait_hasLaw (v : V)
    (R : ExponentialClocks.Sample V → WithTop ℝ)
    (hR : IsStoppingTime (ArrivalFiltration.clockHistory V) R)
    (hpos : ∀ ω, 0 ≤ R ω)
    (hfinite : ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, R ω ≠ ⊤) :
    HasLaw (ClockWaitingLimit.waiting (ArrivalFiltration.chronologicalArrival v) R)
      (expMeasure 1) (ExponentialClocks.clockMeasure V) :=
  SurvivalLaw.hasLaw_of_jointSurvival (CountableClockSurvival.clock_waiting_measurable v R hR)
    (fun _ => le_max_right _ _) hR.measurableSpace_le
    (clock_wait_jointSurvival v R hR hpos hfinite)

theorem clock_wait_indep (v : V)
    (R : ExponentialClocks.Sample V → WithTop ℝ)
    (hR : IsStoppingTime (ArrivalFiltration.clockHistory V) R)
    (hpos : ∀ ω, 0 ≤ R ω)
    (hfinite : ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, R ω ≠ ⊤) :
    Indep ((borel ℝ).comap (ClockWaitingLimit.waiting
      (ArrivalFiltration.chronologicalArrival v) R)) hR.measurableSpace
      (ExponentialClocks.clockMeasure V) :=
  SurvivalLaw.indep_of_jointSurvival (CountableClockSurvival.clock_waiting_measurable v R hR)
    (fun _ => le_max_right _ _) hR.measurableSpace_le
    (clock_wait_jointSurvival v R hR hpos hfinite)

section ActualTasks

variable [DecidableEq V]

omit [Countable V] in
theorem task_delay_eq (M : TaskPaths.System V) (k : Nat) (v : V) :
    TaskClockBridge.delay M k v = ClockWaitingLimit.waiting
      (ArrivalFiltration.chronologicalArrival v) (ClockReadiness.ready M k v) := by
  funext ω
  rfl

theorem task_delay_hasLaw (M : TaskPaths.System V) (k : Nat) (v : V) :
    HasLaw (TaskClockBridge.delay M k v) (expMeasure 1) (ExponentialClocks.clockMeasure V) := by
  rw [task_delay_eq]
  exact clock_wait_hasLaw v (ClockReadiness.ready M k v)
    (ClockReadiness.ready_isStoppingTime M k v) (ClockReadiness.ready_nonnegative M k v)
    ((ClockReadiness.ready_finite_ae M).mono fun ω hω => hω k v)

theorem task_delay_indep (M : TaskPaths.System V) (k : Nat) (v : V) :
    Indep ((borel ℝ).comap (TaskClockBridge.delay M k v))
      (ClockReadiness.ready_isStoppingTime M k v).measurableSpace
        (ExponentialClocks.clockMeasure V) := by
  rw [task_delay_eq]
  exact clock_wait_indep v (ClockReadiness.ready M k v)
    (ClockReadiness.ready_isStoppingTime M k v) (ClockReadiness.ready_nonnegative M k v)
    ((ClockReadiness.ready_finite_ae M).mono fun ω hω => hω k v)

end ActualTasks

end MathResearchAnalysis.ClockStoppedResidual
