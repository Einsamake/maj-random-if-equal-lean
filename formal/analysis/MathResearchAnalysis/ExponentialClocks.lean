module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.StrongLaw
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Tactic

set_option autoImplicit false

/-!
# Independent exponential arrival streams

The sample space and measure are actually constructed as an infinite product
of rate-one exponential measures. Arrivals are cumulative interarrival sums.
This is not yet a Poisson counting-process characterization or strong Markov.
-/

public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace MathResearchAnalysis.ExponentialClocks

abbrev Sample (V : Type*) := (V × Nat) → ℝ

instance rateOne_probability : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

@[expose] def clockMeasure (V : Type*) : Measure (Sample V) :=
  Measure.infinitePi (fun _ : V × Nat => expMeasure 1)

instance clockMeasure_probability (V : Type*) : IsProbabilityMeasure (clockMeasure V) := by
  unfold clockMeasure
  infer_instance

variable {V : Type*}

@[expose] def gap (v : V) (k : Nat) (ω : Sample V) : ℝ := ω (v, k)

theorem gap_measurable (v : V) (k : Nat) : Measurable (gap v k) :=
  measurable_pi_apply (v, k)

theorem gap_hasLaw (v : V) (k : Nat) :
    HasLaw (gap v k) (expMeasure 1) (clockMeasure V) where
  aemeasurable := (gap_measurable v k).aemeasurable
  map_eq := Measure.infinitePi_map_eval _ (v, k)

theorem gaps_independent :
    iIndepFun (fun i : V × Nat => fun ω : Sample V => ω i) (clockMeasure V) := by
  exact iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)

theorem gap_stream_independent (v : V) :
    iIndepFun (gap v) (clockMeasure V) := by
  change iIndepFun (fun (k : Nat) (ω : Sample V) => ω (v, k)) (clockMeasure V)
  exact iIndepFun.precomp (g := fun k : Nat => (v, k))
    (fun i j h => congrArg Prod.snd h) (gaps_independent (V := V))

@[expose] def stream (v : V) (ω : Sample V) : Nat → ℝ := fun k => gap v k ω

theorem stream_measurable (v : V) : Measurable (stream v) := by
  exact measurable_pi_iff.mpr (fun k => gap_measurable v k)

theorem stream_map (v : V) :
    (clockMeasure V).map (stream v) = Measure.infinitePi (fun _ : Nat => expMeasure 1) := by
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : V × Nat => expMeasure 1) (f := fun k : Nat => (v, k))
    (fun i j h => congrArg Prod.snd h)

/-- Grouping by site gives the genuine joint product law of whole clock streams. -/
theorem streams_joint_map :
    (clockMeasure V).map (fun ω v => stream v ω) =
      Measure.infinitePi (fun _ : V => Measure.infinitePi (fun _ : Nat => expMeasure 1)) := by
  exact Measure.infinitePi_map_curry (fun _ : V => fun _ : Nat => expMeasure 1)

theorem streams_independent : iIndepFun stream (clockMeasure V) := by
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map stream_measurable).mpr
  rw [streams_joint_map]
  simp only [stream_map]

theorem gap_positive_ae (v : V) (k : Nat) :
    ∀ᵐ ω ∂clockMeasure V, 0 < gap v k ω := by
  have hzero : expMeasure 1 (Iic (0 : ℝ)) = 0 := by
    rw [← ofReal_cdf, cdf_expMeasure_eq (by norm_num)]
    norm_num
  rw [ae_iff]
  have hlaw := (gap_hasLaw v k).measure_eq (p := fun x : ℝ => x ≤ 0)
    (measurableSet_le measurable_id measurable_const)
  simpa only [not_lt, Iic, ← hlaw] using hzero

theorem all_gaps_positive_ae [Countable V] :
    ∀ᵐ ω ∂clockMeasure V, ∀ v k, 0 < gap v k ω := by
  rw [ae_all_iff]
  intro v
  rw [ae_all_iff]
  exact gap_positive_ae v

/-- Arrival zero is the first ring, not an initialization ring at time zero. -/
@[expose] def arrival (v : V) (n : Nat) (ω : Sample V) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), gap v k ω

theorem arrival_measurable (v : V) (n : Nat) : Measurable (arrival v n) := by
  unfold arrival
  exact Finset.measurable_sum _ (fun k _ => gap_measurable v k)

theorem arrival_succ (v : V) (n : Nat) (ω : Sample V) :
    arrival v (n + 1) ω = arrival v n ω + gap v (n + 1) ω := by
  exact Finset.sum_range_succ _ (n + 1)

theorem arrival_strictMono (v : V) (ω : Sample V)
    (positive : ∀ k, 0 < gap v k ω) : StrictMono (fun n => arrival v n ω) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [arrival_succ]
  exact lt_add_of_pos_right _ (positive (n + 1))

theorem arrival_strictMono_ae [Countable V] :
    ∀ᵐ ω ∂clockMeasure V, ∀ v, StrictMono (fun n => arrival v n ω) := by
  filter_upwards [all_gaps_positive_ae] with ω hω
  exact fun v => arrival_strictMono v ω (hω v)

@[expose] def large (x : ℝ) : ℝ := if 1 < x then 1 else 0

theorem large_measurable : Measurable large := by
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    measurable_const measurable_const

theorem large_nonnegative (x : ℝ) : 0 ≤ large x := by
  unfold large
  split <;> norm_num

theorem large_le_one (x : ℝ) : large x ≤ 1 := by
  unfold large
  split <;> norm_num

theorem large_integrable : Integrable large (expMeasure 1) := by
  exact (integrable_const (1 : ℝ)).mono_nonneg large_measurable.aestronglyMeasurable
    (ae_of_all _ large_nonnegative) (ae_of_all _ large_le_one)

theorem large_integral : (∫ x, large x ∂expMeasure 1) = Real.exp (-1) := by
  have hlarge : large = (Ioi (1 : ℝ)).indicator (fun _ => (1 : ℝ)) := by
    funext x
    simp only [large, Set.indicator, mem_Ioi]
  rw [hlarge, integral_indicator_const (1 : ℝ) measurableSet_Ioi]
  simp only [smul_eq_mul, mul_one]
  have hc : Ioi (1 : ℝ) = (Iic (1 : ℝ))ᶜ := by ext x; simp
  rw [hc, probReal_compl_eq_one_sub measurableSet_Iic,
    ← cdf_eq_real, cdf_expMeasure_eq (by norm_num)]
  norm_num

theorem large_gap_integrable (v : V) (n : Nat) :
    Integrable (fun ω => large (gap v n ω)) (clockMeasure V) :=
  (gap_hasLaw v n).integrable_fun_comp large_integrable

theorem large_gap_integral (v : V) (n : Nat) :
    (∫ ω, large (gap v n ω) ∂clockMeasure V) = Real.exp (-1) := by
  exact ((gap_hasLaw v n).integral_comp large_measurable.aestronglyMeasurable).trans
    large_integral

/-- A bounded Bernoulli transform suffices to prove nonexplosion; the mean of
the unbounded exponential variable need not be used here. -/
theorem large_gap_strongLaw (v : V) :
    ∀ᵐ ω ∂clockMeasure V, Tendsto
      (fun n : Nat => (∑ i ∈ Finset.range n, large (gap v i ω)) / n)
        atTop (𝓝 (Real.exp (-1))) := by
  have h := strong_law_ae_real (fun n ω => large (gap v n ω))
    (large_gap_integrable v 0)
    (fun i j hij => ((gap_stream_independent v).indepFun hij).comp
      large_measurable large_measurable)
    (fun i => ((gap_hasLaw v i).identDistrib (gap_hasLaw v 0)).comp large_measurable)
  simpa only [large_gap_integral] using h

theorem large_sum_le_arrival (v : V) (ω : Sample V)
    (positive : ∀ i, 0 < gap v i ω) (n : Nat) :
    (∑ i ∈ Finset.range n, large (gap v i ω)) ≤ arrival v n ω := by
  have hsum : (∑ i ∈ Finset.range n, large (gap v i ω)) ≤
      ∑ i ∈ Finset.range n, gap v i ω := by
    apply Finset.sum_le_sum
    intro i _
    unfold large
    split
    · next h => exact h.le
    · exact (positive i).le
  apply hsum.trans
  unfold arrival
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (positive n).le

theorem arrival_tendsto_atTop (v : V) (ω : Sample V)
    (positive : ∀ i, 0 < gap v i ω)
    (law : Tendsto (fun n : Nat => (∑ i ∈ Finset.range n, large (gap v i ω)) / n)
      atTop (𝓝 (Real.exp (-1)))) :
    Tendsto (fun n => arrival v n ω) atTop atTop := by
  have hp : 0 < Real.exp (-1) / 2 := by positivity
  have hratio : ∀ᶠ n : Nat in atTop,
      Real.exp (-1) / 2 < (∑ i ∈ Finset.range n, large (gap v i ω)) / n :=
    law.eventually (Ioi_mem_nhds (by linarith [Real.exp_pos (-1)]))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hratio
  apply tendsto_atTop.mpr
  intro t
  obtain ⟨M, hM⟩ := exists_nat_ge (t / (Real.exp (-1) / 2))
  apply eventually_atTop.mpr
  refine ⟨max N (max M 1), fun n hn => ?_⟩
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnM : M ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn1 : 1 ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
  have hcount := (lt_div_iff₀ hnpos).mp (hN n hnN)
  have ht : t ≤ (M : ℝ) * (Real.exp (-1) / 2) := (div_le_iff₀ hp).mp hM
  have hmn : (M : ℝ) ≤ n := Nat.cast_le.mpr hnM
  have hsum := large_sum_le_arrival v ω positive n
  nlinarith

/-- Every site has arbitrarily late rings almost surely. -/
theorem arrival_unbounded_ae [Countable V] :
    ∀ᵐ ω ∂clockMeasure V, ∀ v, Tendsto (fun n => arrival v n ω) atTop atTop := by
  have hall : ∀ᵐ ω ∂clockMeasure V, ∀ v, Tendsto
      (fun n : Nat => (∑ i ∈ Finset.range n, large (gap v i ω)) / n)
        atTop (𝓝 (Real.exp (-1))) := by
    rw [ae_all_iff]
    exact large_gap_strongLaw
  filter_upwards [all_gaps_positive_ae, hall] with ω hpositive hlaw
  exact fun v => arrival_tendsto_atTop v ω (hpositive v) (hlaw v)

end MathResearchAnalysis.ExponentialClocks
