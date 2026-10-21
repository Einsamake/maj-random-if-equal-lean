module
public import MathResearchAnalysis.ExponentialMemoryless
public import Mathlib.MeasureTheory.Integral.Layercake
set_option autoImplicit false
/-! Exact first moment of a deterministically capped exponential waiting time.
The proof uses the actual exponential tail and the layer-cake formula. It is
not a Poisson count, compensator, or random-cutoff independence theorem. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.TruncatedExponential
open MeasureTheory ProbabilityTheory Real Set

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

/-- A cap that is defined and nonnegative even on exceptional negative inputs. -/
def cap (a x : Real) : Real := min (max x 0) a

theorem cap_nonneg {a : Real} (ha : 0 ≤ a) (x : Real) : 0 ≤ cap a x :=
  le_min (le_max_right _ _) ha

theorem cap_le (a x : Real) : cap a x ≤ a := min_le_right _ _

theorem cap_zero (x : Real) : cap 0 x = 0 :=
  min_eq_right (le_max_right _ _)

theorem cap_eq_min {x : Real} (hx : 0 ≤ x) (a : Real) :
    cap a x = min x a := by simp only [cap, max_eq_left hx]

theorem cap_measurable (a : Real) : Measurable (cap a) :=
  (measurable_id.max measurable_const).min measurable_const

theorem cap_integrable {a : Real} (ha : 0 ≤ a) :
    Integrable (cap a) (expMeasure 1) := by
  apply (integrable_const a).mono' (cap_measurable a).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (cap_nonneg ha x)]
    exact cap_le a x)

/-- For a nonnegative tail level below the cap, clipping leaves the exact
exponential survival event unchanged, including on all negative inputs. -/
theorem cap_superlevel {a t : Real} (ht : 0 ≤ t) (hta : t < a) :
    {x : Real | t < cap a x} = Ioi t := by
  ext x
  simp only [Set.mem_ofPred_eq, cap, lt_min_iff, lt_max_iff, mem_Ioi]
  constructor
  · rintro ⟨hx | hx, _⟩
    · exact hx
    · exact False.elim ((not_lt.mpr ht) hx)
  · intro hx
    exact ⟨Or.inl hx, hta⟩

theorem cap_superlevel_empty {a t : Real} (hta : a ≤ t) :
    {x : Real | t < cap a x} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact (not_lt.mpr ((cap_le a x).trans hta)) hx

theorem cap_tail_real {a t : Real} (ht : 0 ≤ t) (hta : t < a) :
    (expMeasure 1).real {x : Real | t < cap a x} = exp (-t) := by
  rw [cap_superlevel ht hta]
  exact ExponentialMemoryless.tail_real ht

/-- Evaluate the bounded tail integral from two actual half-line integrals. -/
theorem integral_exp_neg_Ioo {a : Real} (ha : 0 ≤ a) :
    (∫ t : Real in Ioo 0 a, exp (-t)) = 1 - exp (-a) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha,
    ← intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_exp_neg_Ioi 0) ha,
    integral_exp_neg_Ioi_zero, integral_exp_neg_Ioi]

/-- The exact capped mean, proved by integrating the actual exponential tails. -/
theorem cap_integral {a : Real} (ha : 0 ≤ a) :
    (∫ x : Real, cap a x ∂expMeasure 1) = 1 - exp (-a) := by
  rw [(cap_integrable ha).integral_eq_integral_meas_lt
    (ae_of_all _ (cap_nonneg ha))]
  calc
    (∫ t : Real in Ioi 0, (expMeasure 1).real {x : Real | t < cap a x}) =
        ∫ t : Real in Ioi 0, (Iio a).indicator (fun s : Real => exp (-s)) t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change (expMeasure 1).real {x : Real | t < cap a x} =
        (Iio a).indicator (fun s : Real => exp (-s)) t
      by_cases hta : t < a
      · rw [cap_tail_real ht.le hta]
        simp only [Set.indicator, mem_Iio, ite_eq_left hta]
      · rw [cap_superlevel_empty (le_of_not_gt hta), measureReal_empty]
        simp only [Set.indicator, mem_Iio, ite_eq_right hta]
    _ = ∫ t : Real in Ioo 0 a, exp (-t) := by
      rw [setIntegral_indicator measurableSet_Iio]
      congr 1
    _ = 1 - exp (-a) := integral_exp_neg_Ioo ha

theorem cdf_real {a : Real} (ha : 0 ≤ a) :
    (expMeasure 1).real (Iic a) = 1 - exp (-a) := by
  rw [← cdf_eq_real, cdf_expMeasure_eq (by norm_num)]
  simp only [ite_eq_left ha, one_mul]

/-- Unit-rate exponentials satisfy E[min(X,a)] = P(X ≤ a), for a ≥ 0. -/
theorem cap_integral_eq_probability {a : Real} (ha : 0 ≤ a) :
    (∫ x : Real, cap a x ∂expMeasure 1) = (expMeasure 1).real (Iic a) := by
  rw [cap_integral ha, cdf_real ha]

theorem cap_lintegral {a : Real} (ha : 0 ≤ a) :
    (∫⁻ x : Real, ENNReal.ofReal (cap a x) ∂expMeasure 1) =
      ENNReal.ofReal (1 - exp (-a)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (cap_integrable ha)
    (ae_of_all _ (cap_nonneg ha)), cap_integral ha]

theorem cdf_measure {a : Real} (ha : 0 ≤ a) :
    expMeasure 1 (Iic a) = ENNReal.ofReal (1 - exp (-a)) := by
  rw [← ofReal_measureReal, cdf_real ha]

theorem cap_lintegral_eq_probability {a : Real} (ha : 0 ≤ a) :
    (∫⁻ x : Real, ENNReal.ofReal (cap a x) ∂expMeasure 1) =
      expMeasure 1 (Iic a) := by
  rw [cap_lintegral ha, cdf_measure ha]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → Real}

theorem cap_integrable_of_hasLaw (hX : HasLaw X (expMeasure 1) μ)
    {a : Real} (ha : 0 ≤ a) : Integrable (fun ω => cap a (X ω)) μ :=
  hX.integrable_fun_comp (cap_integrable ha)

theorem cap_integral_of_hasLaw (hX : HasLaw X (expMeasure 1) μ)
    {a : Real} (ha : 0 ≤ a) :
    (∫ ω, cap a (X ω) ∂μ) = 1 - exp (-a) := by
  exact (hX.integral_comp (cap_measurable a).aestronglyMeasurable).trans (cap_integral ha)

theorem cdf_real_of_hasLaw (hX : HasLaw X (expMeasure 1) μ)
    {a : Real} (ha : 0 ≤ a) : μ.real {ω | X ω ≤ a} = 1 - exp (-a) :=
  (hX.measureReal_eq (p := fun x : Real => x ≤ a) measurableSet_Iic).trans (cdf_real ha)

theorem cap_integral_eq_probability_of_hasLaw (hX : HasLaw X (expMeasure 1) μ)
    {a : Real} (ha : 0 ≤ a) :
    (∫ ω, cap a (X ω) ∂μ) = μ.real {ω | X ω ≤ a} := by
  rw [cap_integral_of_hasLaw hX ha, cdf_real_of_hasLaw hX ha]

theorem cap_lintegral_of_hasLaw (hX : HasLaw X (expMeasure 1) μ)
    {a : Real} (ha : 0 ≤ a) :
    (∫⁻ ω, ENNReal.ofReal (cap a (X ω)) ∂μ) =
      ENNReal.ofReal (1 - exp (-a)) := by
  exact (hX.lintegral_comp (cap_measurable a).ennreal_ofReal.aemeasurable).trans
    (cap_lintegral ha)

theorem cdf_measure_of_hasLaw (hX : HasLaw X (expMeasure 1) μ)
    {a : Real} (ha : 0 ≤ a) : μ {ω | X ω ≤ a} = ENNReal.ofReal (1 - exp (-a)) :=
  (hX.measure_eq (p := fun x : Real => x ≤ a) measurableSet_Iic).trans (cdf_measure ha)

theorem cap_lintegral_eq_probability_of_hasLaw (hX : HasLaw X (expMeasure 1) μ)
    {a : Real} (ha : 0 ≤ a) :
    (∫⁻ ω, ENNReal.ofReal (cap a (X ω)) ∂μ) = μ {ω | X ω ≤ a} := by
  rw [cap_lintegral_of_hasLaw hX ha, cdf_measure_of_hasLaw hX ha]

end MathResearchAnalysis.TruncatedExponential
