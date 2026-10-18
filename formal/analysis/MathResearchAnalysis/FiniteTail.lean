module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false

/-!
Integral Markov bounds and a finite-path exponential union bound.

The individual exponential-moment estimates are explicit inputs.  No final
union-tail bound is assumed.  The proof makes no independence assumption
between paths, which may overlap and share random variables.
-/

public section

namespace MathResearchAnalysis.FiniteTail

open MeasureTheory Set
open scoped BigOperators

universe u v w

variable {Ω : Type u} {Index : Type v} {Vertex : Type w}
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The event that at least one selected random variable exceeds a threshold. -/
@[expose] def finiteExceeds (paths : Finset Index) (value : Index → Ω → ℝ) (threshold : ℝ) :
    Set Ω :=
  {ω | ∃ path ∈ paths, threshold < value path ω}

omit [MeasurableSpace Ω] in
theorem finiteExceeds_eq_union (paths : Finset Index) (value : Index → Ω → ℝ)
    (threshold : ℝ) :
    finiteExceeds paths value threshold =
      ⋃ path ∈ paths, {ω | threshold < value path ω} := by
  ext ω
  simp only [finiteExceeds, mem_ofPred_eq, mem_iUnion, exists_prop]

/-- Measurability is proved from the individually measurable variables. -/
theorem finiteExceeds_measurable (paths : Finset Index) (value : Index → Ω → ℝ)
    (threshold : ℝ) (measurable : ∀ path ∈ paths, Measurable (value path)) :
    MeasurableSet (finiteExceeds paths value threshold) := by
  rw [finiteExceeds_eq_union]
  exact Finset.measurableSet_biUnion paths
    (fun path member => measurableSet_lt measurable_const (measurable path member))

/-- Direct application of the actual integral form of Markov's inequality. -/
theorem nonnegative_single_tail
    (value : Ω → ℝ) (integrable : Integrable value μ)
    (nonnegative : 0 ≤ᵐ[μ] value) {threshold bound : ℝ}
    (threshold_positive : 0 < threshold)
    (moment_bound : (∫ ω, value ω ∂μ) ≤ bound) :
    μ.real {ω | threshold < value ω} ≤ bound / threshold := by
  calc
    μ.real {ω | threshold < value ω} ≤ μ.real {ω | threshold ≤ value ω} := by
      refine measureReal_mono ?_ (measure_ne_top μ _)
      intro ω member
      simp only [mem_ofPred_eq] at member ⊢
      exact member.le
    _ ≤ (∫ ω, value ω ∂μ) / threshold := by
      apply (le_div_iff₀ threshold_positive).mpr
      simpa only [mul_comm] using
        mul_meas_ge_le_integral_of_nonneg nonnegative integrable threshold
    _ ≤ bound / threshold :=
      div_le_div_of_nonneg_right moment_bound threshold_positive.le

/-- Finite union bound, assembled from individual Markov estimates. -/
theorem finite_nonnegative_tail
    (paths : Finset Index) (value : Index → Ω → ℝ) {threshold bound : ℝ}
    (threshold_positive : 0 < threshold)
    (integrable : ∀ path ∈ paths, Integrable (value path) μ)
    (nonnegative : ∀ path ∈ paths, 0 ≤ᵐ[μ] value path)
    (moment_bound : ∀ path ∈ paths, (∫ ω, value path ω ∂μ) ≤ bound) :
    μ.real (finiteExceeds paths value threshold) ≤
      (paths.card : ℝ) * bound / threshold := by
  classical
  rw [finiteExceeds_eq_union]
  calc
    μ.real (⋃ path ∈ paths, {ω | threshold < value path ω}) ≤
        ∑ path ∈ paths, μ.real {ω | threshold < value path ω} :=
      measureReal_biUnion_finset_le paths _
    _ ≤ ∑ _path ∈ paths, bound / threshold := by
      apply Finset.sum_le_sum
      intro path member
      exact nonnegative_single_tail (value path) (integrable path member)
        (nonnegative path member) threshold_positive (moment_bound path member)
    _ = (paths.card : ℝ) * bound / threshold := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_div_assoc]

/-- The measurable-event version lists both measurability and integrability. -/
theorem finite_nonnegative_tail_with_measurability
    (paths : Finset Index) (value : Index → Ω → ℝ) {threshold bound : ℝ}
    (threshold_positive : 0 < threshold)
    (measurable : ∀ path ∈ paths, Measurable (value path))
    (integrable : ∀ path ∈ paths, Integrable (value path) μ)
    (nonnegative : ∀ path ∈ paths, 0 ≤ᵐ[μ] value path)
    (moment_bound : ∀ path ∈ paths, (∫ ω, value path ω ∂μ) ≤ bound) :
    MeasurableSet (finiteExceeds paths value threshold) ∧
      μ.real (finiteExceeds paths value threshold) ≤
        (paths.card : ℝ) * bound / threshold :=
  ⟨finiteExceeds_measurable paths value threshold measurable,
    finite_nonnegative_tail paths value threshold_positive integrable nonnegative moment_bound⟩

omit [MeasurableSpace Ω] in
/-- Applying exp to the threshold gives the same finite exceedance event. -/
theorem finiteExceeds_eq_exponential (paths : Finset Index)
    (value : Index → Ω → ℝ) {theta : ℝ} (theta_positive : 0 < theta)
    (threshold : ℝ) :
    finiteExceeds paths value threshold =
      finiteExceeds paths (fun path ω => Real.exp (theta * value path ω))
        (Real.exp (theta * threshold)) := by
  ext ω
  simp only [finiteExceeds, mem_ofPred_eq, Real.exp_lt_exp,
    mul_lt_mul_iff_of_pos_left theta_positive]

/-- Finite Chernoff union bound from the explicitly supplied MGF estimates. -/
theorem finite_exponential_tail
    (paths : Finset Index) (value : Index → Ω → ℝ) {theta bound : ℝ}
    (theta_positive : 0 < theta) (threshold : ℝ)
    (exp_integrable : ∀ path ∈ paths,
      Integrable (fun ω => Real.exp (theta * value path ω)) μ)
    (mgf_bound : ∀ path ∈ paths,
      (∫ ω, Real.exp (theta * value path ω) ∂μ) ≤ bound) :
    μ.real (finiteExceeds paths value threshold) ≤
      (paths.card : ℝ) * bound * Real.exp (-theta * threshold) := by
  rw [finiteExceeds_eq_exponential paths value theta_positive threshold]
  have markov_bound := finite_nonnegative_tail paths
    (fun path ω => Real.exp (theta * value path ω))
    (Real.exp_pos (theta * threshold)) exp_integrable
    (fun _ _ => ae_of_all μ (fun _ => (Real.exp_pos _).le)) mgf_bound
  simpa only [div_eq_mul_inv, neg_mul, Real.exp_neg] using markov_bound

/-- Fully measurable finite exponential tail interface. -/
theorem finite_exponential_tail_with_measurability
    (paths : Finset Index) (value : Index → Ω → ℝ) {theta bound : ℝ}
    (theta_positive : 0 < theta) (threshold : ℝ)
    (measurable : ∀ path ∈ paths, Measurable (value path))
    (exp_integrable : ∀ path ∈ paths,
      Integrable (fun ω => Real.exp (theta * value path ω)) μ)
    (mgf_bound : ∀ path ∈ paths,
      (∫ ω, Real.exp (theta * value path ω) ∂μ) ≤ bound) :
    MeasurableSet (finiteExceeds paths value threshold) ∧
      μ.real (finiteExceeds paths value threshold) ≤
        (paths.card : ℝ) * bound * Real.exp (-theta * threshold) :=
  ⟨finiteExceeds_measurable paths value threshold measurable,
    finite_exponential_tail paths value theta_positive threshold exp_integrable mgf_bound⟩

/-- Actual maximum of a nonempty finite family of real random variables. -/
noncomputable def finiteMaximum (paths : Finset Index) (nonempty : paths.Nonempty)
    (value : Index → Ω → ℝ) (ω : Ω) : ℝ :=
  paths.sup' nonempty (fun path => value path ω)

omit [MeasurableSpace Ω] in
theorem maximum_exceeds_eq (paths : Finset Index) (nonempty : paths.Nonempty)
    (value : Index → Ω → ℝ) (threshold : ℝ) :
    {ω | threshold < finiteMaximum paths nonempty value ω} =
      finiteExceeds paths value threshold := by
  ext ω
  simp only [mem_ofPred_eq, finiteMaximum, finiteExceeds]
  exact Finset.lt_sup'_iff nonempty

/-- The maximum-path tail is proved through the finite exceedance event. -/
theorem finite_maximum_exponential_tail
    (paths : Finset Index) (nonempty : paths.Nonempty)
    (value : Index → Ω → ℝ) {theta bound : ℝ}
    (theta_positive : 0 < theta) (threshold : ℝ)
    (measurable : ∀ path ∈ paths, Measurable (value path))
    (exp_integrable : ∀ path ∈ paths,
      Integrable (fun ω => Real.exp (theta * value path ω)) μ)
    (mgf_bound : ∀ path ∈ paths,
      (∫ ω, Real.exp (theta * value path ω) ∂μ) ≤ bound) :
    MeasurableSet {ω | threshold < finiteMaximum paths nonempty value ω} ∧
      μ.real {ω | threshold < finiteMaximum paths nonempty value ω} ≤
        (paths.card : ℝ) * bound * Real.exp (-theta * threshold) := by
  rw [maximum_exceeds_eq]
  exact finite_exponential_tail_with_measurability paths value theta_positive threshold
    measurable exp_integrable mgf_bound

/-! Explicit finite path sums, including paths with repeated vertices. -/

def pathSum (path : List Vertex) (delay : Vertex → Ω → ℝ) (ω : Ω) : ℝ :=
  (path.map (fun vertex => delay vertex ω)).sum

theorem pathSum_measurable (path : List Vertex) (delay : Vertex → Ω → ℝ)
    (measurable : ∀ vertex, Measurable (delay vertex)) :
    Measurable (pathSum path delay) := by
  induction path with
  | nil => exact measurable_const
  | cons vertex rest ih =>
      exact (measurable vertex).add ih

/-- Maximum of a finite path-sum family from its real integral MGF bounds. -/
theorem finite_path_sum_tail
    (paths : Finset Index) (nonempty : paths.Nonempty)
    (path : Index → List Vertex) (delay : Vertex → Ω → ℝ) {theta bound : ℝ}
    (theta_positive : 0 < theta) (threshold : ℝ)
    (measurable : ∀ vertex, Measurable (delay vertex))
    (exp_integrable : ∀ label ∈ paths,
      Integrable (fun ω => Real.exp (theta * pathSum (path label) delay ω)) μ)
    (mgf_bound : ∀ label ∈ paths,
      (∫ ω, Real.exp (theta * pathSum (path label) delay ω) ∂μ) ≤ bound) :
    MeasurableSet {ω | threshold <
      finiteMaximum paths nonempty (fun label => pathSum (path label) delay) ω} ∧
      μ.real {ω | threshold <
        finiteMaximum paths nonempty (fun label => pathSum (path label) delay) ω} ≤
        (paths.card : ℝ) * bound * Real.exp (-theta * threshold) :=
  finite_maximum_exponential_tail paths nonempty
    (fun label => pathSum (path label) delay) theta_positive threshold
    (fun label _ => pathSum_measurable (path label) delay measurable)
    exp_integrable mgf_bound

end MathResearchAnalysis.FiniteTail
