module

public import MathResearchAnalysis.ArrivalFiltration
public import Mathlib.MeasureTheory.MeasurableSpace.NCard

set_option autoImplicit false

/-!
# Actual counting of the exponential arrival model

The count is the extended cardinality of the set of rings observed by time
`t`. Infinite counts remain infinity on exceptional sample paths. Actual
nonexplosion subsequently proves finite counts almost everywhere; it is not
assumed or hidden by a natural cardinality's default value.

The exact count-threshold events and adaptation to the common physical
history are proved. Neither Poisson count laws, independent increments,
nor strong Markov are asserted here.
-/

public noncomputable section

open MeasureTheory Set Filter

namespace MathResearchAnalysis.ClockCounting

variable {Ω V : Type*} {mΩ : MeasurableSpace Ω}

/-- Count all observed rings, retaining infinity if infinitely many are observed. -/
@[expose] def count (A : Nat → Ω → ℝ) (t : ℝ) (ω : Ω) : ℕ∞ :=
  {n : Nat | A n ω ≤ t}.encard

theorem count_monotone_time (A : Nat → Ω → ℝ) (ω : Ω) :
    Monotone (fun t => count A t ω) := by
  intro s t hst
  apply Set.encard_le_encard
  exact fun _ hn => hn.trans hst

/-- For any chronological stream, the `(q+1)`-count event is the `q`-th arrival event.
This includes paths with infinite counts and requires no finiteness premise. -/
theorem count_succ_le_iff (A : Nat → Ω → ℝ) (ω : Ω)
    (hmono : Monotone (fun n => A n ω)) (t : ℝ) (q : Nat) :
    ((q + 1 : Nat) : ℕ∞) ≤ count A t ω ↔ A q ω ≤ t := by
  constructor
  · intro hc
    by_contra hlate
    have hsub : {n : Nat | A n ω ≤ t} ⊆ {n : Nat | n < q} := by
      intro n hn
      by_contra hnq
      have hqn : q ≤ n := Nat.le_of_not_gt hnq
      exact hlate ((hmono hqn).trans hn)
    have hbound := Set.encard_le_encard hsub
    rw [Set.Nat.encard_range] at hbound
    have h := hc.trans hbound
    exact (Nat.not_succ_le_self q) (by exact_mod_cast h)
  · intro ha
    have hsub : {n : Nat | n < q + 1} ⊆ {n : Nat | A n ω ≤ t} := by
      intro n hn
      exact (hmono (Nat.le_of_lt_succ hn)).trans ha
    simpa only [count, Set.Nat.encard_range] using Set.encard_le_encard hsub

theorem count_lt_succ_iff (A : Nat → Ω → ℝ) (ω : Ω)
    (hmono : Monotone (fun n => A n ω)) (t : ℝ) (q : Nat) :
    count A t ω < ((q + 1 : Nat) : ℕ∞) ↔ t < A q ω := by
  rw [← not_le, count_succ_le_iff A ω hmono, not_le]

/-- Infinite count means every arrival has already occurred, for a chronological stream. -/
theorem count_eq_top_iff (A : Nat → Ω → ℝ) (ω : Ω)
    (hmono : Monotone (fun n => A n ω)) (t : ℝ) :
    count A t ω = ⊤ ↔ ∀ q, A q ω ≤ t := by
  constructor
  · intro h q
    apply (count_succ_le_iff A ω hmono t q).mp
    rw [h]
    exact le_top
  · intro h
    have heq : {n : Nat | A n ω ≤ t} = Set.univ := by
      ext n
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact h n
    unfold count
    rw [heq, Set.encard_univ]
    simp

/-- Counting is measurable whenever all of its individual arrival events are measurable. -/
theorem count_measurable_of_events (A : Nat → Ω → ℝ) (t : ℝ)
    (hA : ∀ n, MeasurableSet {ω | A n ω ≤ t}) :
    Measurable (count A t) := by
  apply measurable_encard.comp
  apply Measurable.of_mem
  intro n
  exact measurableSet_setOfPred.mp (hA n)

theorem count_measurable (A : Nat → Ω → ℝ) (hA : ∀ n, Measurable (A n)) (t : ℝ) :
    Measurable (count A t) :=
  count_measurable_of_events A t (fun n => measurableSet_le (hA n) measurable_const)

/-- The actual ring count of the constructed chronological exponential stream. -/
@[expose] def clockCount (v : V) (t : ℝ) : ExponentialClocks.Sample V → ℕ∞ :=
  count (ArrivalFiltration.chronologicalArrival v) t

/-- The count is known in the common physical history at its observation time. -/
theorem clockCount_adapted (v : V) (t : ℝ) :
    Measurable[ArrivalFiltration.clockHistory V t] (clockCount v t) := by
  apply count_measurable_of_events
  exact fun n => ArrivalFiltration.arrival_event_measurable
    ArrivalFiltration.chronologicalArrival ArrivalFiltration.chronologicalArrival_measurable
    v n (le_refl t)

theorem clockCount_measurable (v : V) (t : ℝ) : Measurable (clockCount v t) :=
  count_measurable (ArrivalFiltration.chronologicalArrival v)
    (ArrivalFiltration.chronologicalArrival_measurable v) t

/-- The threshold event is exact on all paths, including exceptional infinite-count paths. -/
theorem clockCount_succ_le_iff (v : V) (t : ℝ) (ω : ExponentialClocks.Sample V) (q : Nat) :
    ((q + 1 : Nat) : ℕ∞) ≤ clockCount v t ω ↔
      ArrivalFiltration.chronologicalArrival v q ω ≤ t :=
  count_succ_le_iff _ ω (ArrivalFiltration.chronologicalArrival_monotone v ω) t q

theorem clockCount_lt_succ_iff (v : V) (t : ℝ) (ω : ExponentialClocks.Sample V) (q : Nat) :
    clockCount v t ω < ((q + 1 : Nat) : ℕ∞) ↔
      t < ArrivalFiltration.chronologicalArrival v q ω :=
  count_lt_succ_iff _ ω (ArrivalFiltration.chronologicalArrival_monotone v ω) t q

/-- No rings have occurred precisely when the first arrival lies after observation time. -/
theorem clockCount_eq_zero_iff (v : V) (t : ℝ) (ω : ExponentialClocks.Sample V) :
    clockCount v t ω = 0 ↔ t < ArrivalFiltration.chronologicalArrival v 0 ω := by
  simpa only [Nat.zero_add, Nat.cast_one, Order.lt_one_iff] using
    clockCount_lt_succ_iff v t ω 0

/-- For nonnegative observation time this event depends on the genuine first exponential gap. -/
theorem clockCount_eq_zero_iff_gap (v : V) {t : ℝ} (ht : 0 ≤ t)
    (ω : ExponentialClocks.Sample V) :
    clockCount v t ω = 0 ↔ t < ExponentialClocks.gap v 0 ω := by
  rw [clockCount_eq_zero_iff]
  simp only [ArrivalFiltration.chronologicalArrival, Nat.zero_add,
    Finset.range_one, Finset.sum_singleton, lt_max_iff, not_lt.mpr ht, or_false]

/-- The zero-count probability is computed from the actual exponential law.
This is one marginal probability, not a proof of the full Poisson count law. -/
theorem clockCount_zero_probability (v : V) {t : ℝ} (ht : 0 ≤ t) :
    (ExponentialClocks.clockMeasure V).real {ω | clockCount v t ω = 0} = Real.exp (-t) := by
  have heq : {ω | clockCount v t ω = 0} = {ω | t < ExponentialClocks.gap v 0 ω} := by
    ext ω
    exact clockCount_eq_zero_iff_gap v ht ω
  rw [heq, (ExponentialClocks.gap_hasLaw v 0).measureReal_eq (p := fun x => t < x)
    (measurableSet_lt measurable_const measurable_id)]
  have hcompl : {x : ℝ | t < x} = (Iic t)ᶜ := by ext x; simp
  rw [hcompl, probReal_compl_eq_one_sub measurableSet_Iic,
    ← ProbabilityTheory.cdf_eq_real,
    ProbabilityTheory.cdf_expMeasure_eq (by norm_num)]
  simp only [ite_eq_left ht, one_mul]
  ring

/-- The count is finite on every locally finite sample path. -/
theorem clockCount_finite (v : V) (t : ℝ) (ω : ExponentialClocks.Sample V)
    (hfinite : Set.Finite {n : Nat | ArrivalFiltration.chronologicalArrival v n ω ≤ t}) :
    clockCount v t ω < ⊤ := hfinite.encard_lt_top

/-- Actual exponential nonexplosion supplies finiteness, rather than a count hypothesis. -/
theorem clockCount_finite_ae [Countable V] :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ v t, clockCount v t ω < ⊤ := by
  filter_upwards [ArrivalFiltration.clock_locally_finite_ae (V := V)] with ω hω
  exact fun v t => clockCount_finite v t ω (hω v t)

/-- The exact threshold event also agrees with the raw exponential sum almost surely. -/
theorem clockCount_raw_threshold_ae [Countable V] :
    ∀ᵐ ω ∂ExponentialClocks.clockMeasure V, ∀ v t q,
      (((q + 1 : Nat) : ℕ∞) ≤ clockCount v t ω ↔
        ExponentialClocks.arrival v q ω ≤ t) := by
  filter_upwards [ArrivalFiltration.chronologicalArrival_eq_raw_ae (V := V)] with ω hω
  intro v t q
  simpa only [hω v q] using clockCount_succ_le_iff v t ω q

/-- The probability of an infinite count is zero, as a consequence of the model. -/
theorem clockCount_infinite_measure_zero [Countable V] (v : V) (t : ℝ) :
    ExponentialClocks.clockMeasure V {ω | clockCount v t ω = ⊤} = 0 := by
  have h := (clockCount_finite_ae (V := V)).mono (fun ω hω => (hω v t).ne)
  simpa only [not_not] using ae_iff.mp h

/-- The entire interarrival streams at distinct sites are actually independent. -/
theorem site_streams_independent {v w : V} (hvw : v ≠ w) :
    ProbabilityTheory.IndepFun
      (fun ω : ExponentialClocks.Sample V => fun k => ExponentialClocks.gap v k ω)
      (fun ω : ExponentialClocks.Sample V => fun k => ExponentialClocks.gap w k ω)
      (ExponentialClocks.clockMeasure V) := by
  let S : V → Set (V × Nat) := fun v => {i | i.1 = v}
  have hd : Disjoint (S v) (S w) := by
    apply Set.disjoint_left.mpr
    intro i hi hj
    exact hvw (hi.symm.trans hj)
  have hi := (ExponentialClocks.gaps_independent (V := V)).indepFun_set (S v) (S w) hd
    (fun i => measurable_pi_apply i)
  have hv : Measurable (fun f : S v → ℝ => fun k : Nat =>
      f ⟨(v, k), rfl⟩) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  have hw : Measurable (fun f : S w → ℝ => fun k : Nat =>
      f ⟨(w, k), rfl⟩) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  exact hi.comp hv hw

/-- Counts at different sites are independent at arbitrary deterministic observation times.
No claim about increments at different times of the same stream is made. -/
theorem clockCounts_independent {v w : V} (hvw : v ≠ w) (s t : ℝ) :
    ProbabilityTheory.IndepFun (clockCount v s) (clockCount w t)
      (ExponentialClocks.clockMeasure V) := by
  have hcount : ∀ t : ℝ, Measurable
      (count (fun n (g : Nat → ℝ) =>
        ∑ k ∈ Finset.range (n + 1), max (g k) 0) t) := by
    intro t
    apply count_measurable
    intro n
    exact Finset.measurable_sum _ (fun k _ =>
      (measurable_pi_apply k).max measurable_const)
  exact (site_streams_independent hvw).comp (hcount s) (hcount t)

end MathResearchAnalysis.ClockCounting
