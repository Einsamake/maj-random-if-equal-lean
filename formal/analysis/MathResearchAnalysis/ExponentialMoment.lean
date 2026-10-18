module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import MathResearchAnalysis.NonnegativeMoment

set_option autoImplicit false

/-!
# Actual rate-one exponential moments

These proofs use the density of mathlib's `expMeasure 1`, rather than an
assumed moment formula or integrability assumption. The conditional result
uses actual independence of the waiting variable's generated sigma-algebra
and the conditioning sigma-algebra. It does not assert that a waiting time
after a Poisson stopping time has this law or this independence: that still
requires the construction and strong Markov theorem for the clock process.
-/

public noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter

namespace MathResearchAnalysis.ExponentialMoment

/-- The real weighted exponential density is an integrable half-line exponential. -/
theorem weighted_density_eq (θ : ℝ) :
    (fun x : ℝ => (exponentialPDF 1 x).toReal * exp (θ * x)) =
      (Ici 0).indicator (fun x => exp ((θ - 1) * x)) := by
  funext x
  by_cases hx : 0 ≤ x
  · simp only [exponentialPDF_of_nonneg hx, one_mul,
      ENNReal.toReal_ofReal (exp_pos _).le,
      indicator_of_mem (show x ∈ Ici 0 from hx)]
    rw [← exp_add]
    congr 1
    ring
  · simp [exponentialPDF_of_neg (lt_of_not_ge hx),
      indicator_of_notMem (show x ∉ Ici 0 from hx)]

/-- No assumed moment bound is needed to obtain exponential integrability. -/
theorem integrable_expMeasure_one {θ : ℝ} (hθ : θ < 1) :
    Integrable (fun x : ℝ => exp (θ * x)) (expMeasure 1) := by
  change Integrable _ (volume.withDensity (exponentialPDF 1))
  rw [integrable_withDensity_iff_integrable_smul' (f := exponentialPDF 1)
    (by exact (measurable_exponentialPDFReal 1).ennreal_ofReal)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul]
  rw [weighted_density_eq]
  rw [integrable_indicator_iff measurableSet_Ici]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_exp_mul_Ioi (sub_neg.mpr hθ) 0

/-- The MGF is derived by integrating the actual exponential density. -/
theorem integral_expMeasure_one {θ : ℝ} (hθ : θ < 1) :
    (∫ x : ℝ, exp (θ * x) ∂expMeasure 1) = (1 - θ)⁻¹ := by
  change (∫ x : ℝ, exp (θ * x) ∂volume.withDensity (exponentialPDF 1)) = _
  rw [integral_withDensity_eq_integral_toReal_smul (f := exponentialPDF 1)
    (by exact (measurable_exponentialPDFReal 1).ennreal_ofReal)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul]
  rw [weighted_density_eq, integral_indicator measurableSet_Ici,
    integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (sub_neg.mpr hθ) 0]
  simp only [mul_zero, exp_zero, neg_div, one_div]
  rw [show θ - 1 = -(1 - θ) by ring, inv_neg, neg_neg]

/-- The concrete parameter used in the task-path tail bound. -/
theorem integral_expMeasure_one_half :
    (∫ x : ℝ, exp ((1 / 2 : ℝ) * x) ∂expMeasure 1) = 2 := by
  rw [integral_expMeasure_one (by norm_num : (1 / 2 : ℝ) < 1)]
  norm_num

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {D : Ω → ℝ}

/-- A genuine exponential law transfers the proved integrability to any probability space. -/
theorem integrable_of_hasLaw {θ : ℝ} (hθ : θ < 1)
    (hD : HasLaw D (expMeasure 1) μ) :
    Integrable (fun ω => exp (θ * D ω)) μ :=
  hD.integrable_fun_comp (integrable_expMeasure_one hθ)

/-- The actual law, rather than a prescribed moment, determines this expectation. -/
theorem integral_of_hasLaw {θ : ℝ} (hθ : θ < 1)
    (hD : HasLaw D (expMeasure 1) μ) :
    (∫ ω, exp (θ * D ω) ∂μ) = (1 - θ)⁻¹ := by
  calc
    _ = ∫ x : ℝ, exp (θ * x) ∂expMeasure 1 :=
      hD.integral_comp (by fun_prop)
    _ = _ := integral_expMeasure_one hθ

/-- Independent rate-one waiting times have the stated genuine conditional expectation. -/
theorem condExp_of_hasLaw_indep {θ : ℝ} (hθ : θ < 1)
    (hD : HasLaw D (expMeasure 1) μ) (hDmeas : Measurable D)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hindep : Indep ((borel ℝ).comap D) m μ) :
    μ[(fun ω => exp (θ * D ω)) | m] =ᵐ[μ] fun _ => (1 - θ)⁻¹ := by
  have : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have : IsProbabilityMeasure μ := hD.isProbabilityMeasure
  have hmeas : StronglyMeasurable[(borel ℝ).comap D]
      (fun ω => exp (θ * D ω)) :=
    ((comap_measurable D).const_mul θ).exp.stronglyMeasurable
  have hc := condExp_indep_eq hDmeas.comap_le hm hmeas hindep
  simpa only [integral_of_hasLaw hθ hD] using hc

/-- Conditioning on an independent random history is an instance of the sigma-algebra result. -/
theorem condExp_of_hasLaw_indepFun {θ : ℝ} (hθ : θ < 1)
    (hD : HasLaw D (expMeasure 1) μ) (hDmeas : Measurable D)
    {H : Type*} [mH : MeasurableSpace H] (history : Ω → H)
    (hHistory : Measurable history) (hindep : IndepFun D history μ) :
    μ[(fun ω => exp (θ * D ω)) | mH.comap history] =ᵐ[μ]
      fun _ => (1 - θ)⁻¹ := by
  apply condExp_of_hasLaw_indep hθ hD hDmeas hHistory.comap_le
  exact (IndepFun_iff_Indep D history μ).mp hindep

/-- The exact conditional value used in the path analysis at `θ = 1/2`. -/
theorem condExp_half_of_hasLaw_indep
    (hD : HasLaw D (expMeasure 1) μ) (hDmeas : Measurable D)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hindep : Indep ((borel ℝ).comap D) m μ) :
    μ[(fun ω => exp ((1 / 2 : ℝ) * D ω)) | m] =ᵐ[μ] fun _ => 2 := by
  have h := condExp_of_hasLaw_indep (by norm_num : (1 / 2 : ℝ) < 1)
    hD hDmeas hm hindep
  norm_num at h ⊢
  exact h

/-- Real exponential laws and independence discharge both single-step analytic inputs. -/
theorem fixed_path_integrable_of_hasLaw_indep [IsProbabilityMeasure μ]
    (ℱ : Filtration Nat mΩ) {θ : ℝ} (hθ : θ < 1)
    (wait : Nat → Ω → ℝ) (length : Nat)
    (hknown : ∀ i < length, StronglyMeasurable[ℱ (i + 1)] (wait i))
    (hlaw : ∀ i < length, HasLaw (wait i) (expMeasure 1) μ)
    (hindep : ∀ i < length, Indep ((borel ℝ).comap (wait i)) (ℱ i) μ) :
    Integrable (ConditionalMoment.pathExp θ wait length) μ := by
  apply NonnegativeMoment.fixed_path_exponential_integrable ℱ θ ((1 - θ)⁻¹)
    wait length hknown
  · exact fun i hi => integrable_of_hasLaw hθ (hlaw i hi)
  · intro i hi
    exact condExp_of_hasLaw_indep hθ (hlaw i hi)
      ((hknown i hi).mono (ℱ.le (i + 1))).measurable (ℱ.le i) (hindep i hi)

/-- The fixed-path MGF from actual law and independence, with no MGF hypotheses. -/
theorem fixed_path_moment_of_hasLaw_indep [IsProbabilityMeasure μ]
    (ℱ : Filtration Nat mΩ) {θ : ℝ} (hθ : θ < 1)
    (wait : Nat → Ω → ℝ) (length : Nat)
    (hknown : ∀ i < length, StronglyMeasurable[ℱ (i + 1)] (wait i))
    (hlaw : ∀ i < length, HasLaw (wait i) (expMeasure 1) μ)
    (hindep : ∀ i < length, Indep ((borel ℝ).comap (wait i)) (ℱ i) μ) :
    (∫ ω, exp (θ * ConditionalMoment.prefixSum wait length ω) ∂μ) =
      ((1 - θ)⁻¹) ^ length := by
  apply NonnegativeMoment.fixed_path_rate_one_moment ℱ θ wait length hknown
  · exact fun i hi => integrable_of_hasLaw hθ (hlaw i hi)
  · intro i hi
    exact condExp_of_hasLaw_indep hθ (hlaw i hi)
      ((hknown i hi).mono (ℱ.le (i + 1))).measurable (ℱ.le i) (hindep i hi)

end MathResearchAnalysis.ExponentialMoment
