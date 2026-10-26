module
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Tactic
set_option autoImplicit false
/-! A lower-tail estimate from actual finite variance, without independence.
The numerical inputs will be discharged by the mixed clock process separately. -/
@[expose] public noncomputable section
namespace MathResearchAnalysis.CountLowerTail
open MeasureTheory ProbabilityTheory

theorem lower_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → Real) (hX : MemLp X 2 μ)
    (M N : Real) (hM : 0<M) (hN : N≤M/8)
    (hmean : M/4≤∫ z, X z ∂μ) (hvar : variance X μ≤M/4) :
    μ {z | X z<N} ≤ ENNReal.ofReal (16/M) := by
  have hsub : {z | X z<N} ⊆ {z | M/8≤|X z-∫ w, X w ∂μ|} := by
    intro z hz
    have hg : M/8 ≤ (∫ w, X w ∂μ)-X z := by
      change X z<N at hz
      linarith
    change M/8≤|X z-∫ w, X w ∂μ|
    rw [abs_sub_comm]
    exact hg.trans (le_abs_self _)
  calc
    _ ≤ μ {z | M/8≤|X z-∫ w, X w ∂μ|} := measure_mono hsub
    _ ≤ ENNReal.ofReal (variance X μ/(M/8)^2) :=
      meas_ge_le_variance_div_sq hX (by positivity)
    _ ≤ ENNReal.ofReal ((M/4)/(M/8)^2) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hvar (sq_nonneg _))
    _ = _ := by congr 1; field_simp; ring

theorem lower_tail_quarter {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → Real) (hX : MemLp X 2 μ)
    (M N : Real) (hM : 64≤M) (hN : N≤M/8)
    (hmean : M/4≤∫ z, X z ∂μ) (hvar : variance X μ≤M/4) :
    μ {z | X z<N} ≤ ENNReal.ofReal (1/4 : Real) := by
  have hp : 0<M := by linarith
  apply (lower_tail μ X hX M N hp hN hmean hvar).trans
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ hp).mpr
  linarith
end MathResearchAnalysis.CountLowerTail
