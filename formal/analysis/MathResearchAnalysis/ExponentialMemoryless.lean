module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.HasLaw
public import MathResearchAnalysis.ExponentialMoment

set_option autoImplicit false

/-!
# Distribution-level memorylessness of the actual exponential measure

The residual law after deterministic conditioning is proved from the real
CDF of mathlib's rate-one exponential measure. This is not a strong Markov
theorem at random readiness times or at stopping times of clock histories.
-/

public noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace MathResearchAnalysis.ExponentialMemoryless

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

/-- Actual probability of exceeding a nonnegative deterministic threshold. -/
theorem tail_real {s : ℝ} (hs : 0 ≤ s) :
    (expMeasure 1).real (Ioi s) = exp (-s) := by
  have hcompl : Ioi s = (Iic s)ᶜ := by ext x; simp
  rw [hcompl, probReal_compl_eq_one_sub measurableSet_Iic,
    ← cdf_eq_real, cdf_expMeasure_eq (by norm_num)]
  simp only [ite_eq_left hs, one_mul]
  ring

theorem tail_measure {s : ℝ} (hs : 0 ≤ s) :
    expMeasure 1 (Ioi s) = ENNReal.ofReal (exp (-s)) := by
  rw [← ofReal_measureReal, tail_real hs]

/-- The interval mass used to identify the shifted restricted measure. -/
theorem interval_real {s x : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) :
    (expMeasure 1).real (Ioc s (s + x)) = exp (-s) * (1 - exp (-x)) := by
  rw [← Iic_sdiff_Iic,
    measureReal_sdiff (Iic_subset_Iic.mpr (by linarith)) measurableSet_Iic,
    ← cdf_eq_real, ← cdf_eq_real,
    cdf_expMeasure_eq (by norm_num), cdf_expMeasure_eq (by norm_num)]
  simp only [ite_eq_left hs, ite_eq_left (show 0 ≤ s + x by linarith), one_mul,
    neg_add_rev, exp_add]
  ring

theorem interval_measure {s x : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) :
    expMeasure 1 (Ioc s (s + x)) =
      ENNReal.ofReal (exp (-s) * (1 - exp (-x))) := by
  rw [← ofReal_measureReal, interval_real hs hx]

/-- The full unnormalized residual law, proved as an equality of finite measures. -/
theorem shifted_restricted_measure {s : ℝ} (hs : 0 ≤ s) :
    ((expMeasure 1).restrict (Ioi s)).map (fun x => x - s) =
      ENNReal.ofReal (exp (-s)) • expMeasure 1 := by
  apply Measure.ext_of_Iic
  intro x
  have hshift : Measurable (fun y : ℝ => y - s) := measurable_id.sub_const s
  rw [Measure.map_apply hshift measurableSet_Iic,
    Measure.restrict_apply (measurableSet_Iic.preimage hshift), Measure.smul_apply]
  have hevent : (fun y : ℝ => y - s) ⁻¹' Iic x ∩ Ioi s = Ioc s (s + x) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, mem_Iic, mem_Ioi, mem_Ioc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [hevent]
  by_cases hx : 0 ≤ x
  · rw [interval_measure hs hx, ← ofReal_cdf, cdf_expMeasure_eq (by norm_num)]
    simp only [ite_eq_left hx, one_mul, smul_eq_mul]
    rw [ENNReal.ofReal_mul (exp_pos _).le]
  · rw [Ioc_eq_empty_of_le (by linarith), measure_empty,
      ← ofReal_cdf, cdf_expMeasure_eq (by norm_num)]
    simp only [ite_eq_right hx, ENNReal.ofReal_zero, smul_eq_mul, mul_zero]

/-- The conditioning measure on original waiting times after survival to `s`.
Its mass is one when `s ≥ 0`, as proved by the residual-law result below. -/
@[expose] def survivalMeasure (s : ℝ) : Measure ℝ :=
  ENNReal.ofReal (exp s) • (expMeasure 1).restrict (Ioi s)

/-- Deterministic survival conditioning leaves an exact rate-one residual distribution. -/
theorem normalized_residual_measure {s : ℝ} (hs : 0 ≤ s) :
    (survivalMeasure s).map (fun x => x - s) = expMeasure 1 := by
  unfold survivalMeasure
  have hshift : Measurable (fun x : ℝ => x - s) := measurable_id.sub_const s
  rw [Measure.map_smul _ hshift.aemeasurable,
    shifted_restricted_measure hs, smul_smul,
    ← ENNReal.ofReal_mul (exp_pos s).le, ← exp_add]
  simp only [add_neg_cancel, exp_zero, ENNReal.ofReal_one, one_smul]

/-- A genuine `HasLaw` statement for the residual under the constructed conditioning measure. -/
theorem residual_hasLaw {s : ℝ} (hs : 0 ≤ s) :
    HasLaw (fun x : ℝ => x - s) (expMeasure 1) (survivalMeasure s) where
  aemeasurable := (measurable_id.sub_const s).aemeasurable
  map_eq := normalized_residual_measure hs

theorem survivalMeasure_probability {s : ℝ} (hs : 0 ≤ s) :
    IsProbabilityMeasure (survivalMeasure s) := (residual_hasLaw hs).isProbabilityMeasure

/-- The corresponding conditional tail ratio follows from actual nonzero survival probabilities. -/
theorem tail_ratio {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (expMeasure 1).real (Ioi (s + t)) / (expMeasure 1).real (Ioi s) = exp (-t) := by
  rw [tail_real (by linarith), tail_real hs, neg_add_rev, exp_add]
  exact mul_div_cancel_right₀ _ (ne_of_gt (exp_pos _))

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {D : Ω → ℝ}

/-- Explicit survival conditioning for an exponential variable on an arbitrary sample space. -/
@[expose] def survivalOf (D : Ω → ℝ) (μ : Measure Ω) (s : ℝ) : Measure Ω :=
  ENNReal.ofReal (exp s) • μ.restrict {ω | s < D ω}

/-- The actual law is preserved when restricting and normalizing the original sample space. -/
theorem survival_hasLaw (hD : HasLaw D (expMeasure 1) μ) (hDmeas : Measurable D) (s : ℝ) :
    HasLaw D (survivalMeasure s) (survivalOf D μ s) where
  aemeasurable := hDmeas.aemeasurable
  map_eq := by
    unfold survivalOf survivalMeasure
    rw [Measure.map_smul _ hDmeas.aemeasurable]
    have hevent : {ω | s < D ω} = D ⁻¹' Ioi s := rfl
    rw [hevent, ← Measure.restrict_map hDmeas measurableSet_Ioi, hD.map_eq]

/-- Distribution-level memorylessness transferred to a genuine exponential random variable. -/
theorem residualOf_hasLaw {s : ℝ} (hs : 0 ≤ s)
    (hD : HasLaw D (expMeasure 1) μ) (hDmeas : Measurable D) :
    HasLaw (fun ω => D ω - s) (expMeasure 1) (survivalOf D μ s) :=
  (residual_hasLaw hs).fun_comp (survival_hasLaw hD hDmeas s)

theorem survivalOf_probability {s : ℝ} (hs : 0 ≤ s)
    (hD : HasLaw D (expMeasure 1) μ) (hDmeas : Measurable D) :
    IsProbabilityMeasure (survivalOf D μ s) :=
  (residualOf_hasLaw hs hD hDmeas).isProbabilityMeasure

/-- The exponential moment is integrable under actual deterministic survival conditioning. -/
theorem residualOf_exp_integrable {s θ : ℝ} (hs : 0 ≤ s) (hθ : θ < 1)
    (hD : HasLaw D (expMeasure 1) μ) (hDmeas : Measurable D) :
    Integrable (fun ω => exp (θ * (D ω - s))) (survivalOf D μ s) :=
  ExponentialMoment.integrable_of_hasLaw hθ (residualOf_hasLaw hs hD hDmeas)

/-- The actual residual MGF follows from the proved law, with no conditional-MGF premise. -/
theorem residualOf_exp_integral {s θ : ℝ} (hs : 0 ≤ s) (hθ : θ < 1)
    (hD : HasLaw D (expMeasure 1) μ) (hDmeas : Measurable D) :
    (∫ ω, exp (θ * (D ω - s)) ∂survivalOf D μ s) = (1 - θ)⁻¹ :=
  ExponentialMoment.integral_of_hasLaw hθ (residualOf_hasLaw hs hD hDmeas)

end MathResearchAnalysis.ExponentialMemoryless
