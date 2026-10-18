module

public import MathResearchAnalysis.ConditionalMoment
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

set_option autoImplicit false

/-!
# Nonnegative conditional moments without prefix-integrability assumptions

The product of a past-measurable nonnegative integrable factor with a current
nonnegative integrable factor is proved integrable from its constant conditional
expectation. The proof clips the past factor at each natural number, applies the
real conditional-expectation pull-out theorem only to these bounded products,
and then applies nonnegative monotone convergence to prove finiteness of the
unclipped product's Lebesgue integral. No product-integrability or prefix moment
value is supplied as an input.

The fixed-path wrappers still require the individual conditional moment and
individual-factor integrability. They do not assert a Poisson or strong-Markov
model.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace MathResearchAnalysis.NonnegativeMoment

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Nonnegative conditional pull-out, including the previously missing product integrability. -/
theorem integrable_mul_of_nonneg_condExp_const [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (f g : Ω → ℝ) (constant : ℝ)
    (hf : StronglyMeasurable[m] f) (hfInt : Integrable f μ) (hgInt : Integrable g μ)
    (hfNonneg : ∀ ω, 0 ≤ f ω) (hgNonneg : ∀ ω, 0 ≤ g ω)
    (hconditional : μ[g | m] =ᵐ[μ] fun _ => constant) :
    Integrable (fun ω => f ω * g ω) μ := by
  let clipped : ℕ → Ω → ℝ := fun n ω => min (f ω) (n : ℝ)
  have hcNonneg : 0 ≤ constant := by
    have hgc : (∫ ω, g ω ∂μ) = constant := by
      calc
        (∫ ω, g ω ∂μ) = ∫ ω, (μ[g | m]) ω ∂μ := (integral_condExp hm).symm
        _ = ∫ _ : Ω, constant ∂μ := integral_congr_ae hconditional
        _ = constant := by simp
    rw [← hgc]
    exact integral_nonneg hgNonneg
  have hclipMeas : ∀ n, StronglyMeasurable[m] (clipped n) := by
    intro n
    exact (hf.measurable.min measurable_const).stronglyMeasurable
  have hclipNonneg : ∀ n ω, 0 ≤ clipped n ω := by
    intro n ω
    exact le_min (hfNonneg ω) (Nat.cast_nonneg n)
  have hclipInt : ∀ n, Integrable (clipped n) μ := by
    intro n
    exact hfInt.mono_nonneg ((hclipMeas n).mono hm).aestronglyMeasurable
      (ae_of_all _ (hclipNonneg n)) (ae_of_all _ fun ω => min_le_left _ _)
  have hprodInt : ∀ n, Integrable (fun ω => clipped n ω * g ω) μ := by
    intro n
    apply hgInt.bdd_mul ((hclipMeas n).mono hm).aestronglyMeasurable
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hclipNonneg n ω)]
    exact min_le_right _ _
  have hclipMoment : ∀ n,
      (∫ ω, clipped n ω * g ω ∂μ) = (∫ ω, clipped n ω ∂μ) * constant := by
    intro n
    exact ConditionalMoment.integral_mul_of_condExp_const hm (clipped n) g constant
      (hclipMeas n) (hprodInt n) hgInt hconditional
  have hlinBound : ∀ n,
      (∫⁻ ω, ENNReal.ofReal (clipped n ω * g ω) ∂μ) ≤
        ENNReal.ofReal ((∫ ω, f ω ∂μ) * constant) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hprodInt n)
      (ae_of_all _ fun ω => mul_nonneg (hclipNonneg n ω) (hgNonneg ω)), hclipMoment n]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (integral_mono (hclipInt n) hfInt fun ω => min_le_left _ _) hcNonneg
  have hlinTendsto : Tendsto
      (fun n => ∫⁻ ω, ENNReal.ofReal (clipped n ω * g ω) ∂μ) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (f ω * g ω) ∂μ)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · intro n
      exact (hprodInt n).aemeasurable.ennreal_ofReal
    · apply ae_of_all
      intro ω n k hnk
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (hgNonneg ω)
      exact min_le_min_left _ (Nat.cast_le.mpr hnk)
    · apply ae_of_all
      intro ω
      obtain ⟨n, hn⟩ := exists_nat_ge (f ω)
      apply tendsto_congr' ?_ |>.mpr tendsto_const_nhds
      apply eventually_atTop.mpr
      refine ⟨n, fun k hnk => ?_⟩
      simp only [clipped, min_eq_left (hn.trans (Nat.cast_le.mpr hnk))]
  have hlinFinite : (∫⁻ ω, ENNReal.ofReal (f ω * g ω) ∂μ) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_of_tendsto' hlinTendsto hlinBound)
  exact (lintegral_ofReal_ne_top_iff_integrable
    ((hf.mono hm).aestronglyMeasurable.mul hgInt.aestronglyMeasurable)
    (ae_of_all _ fun ω => mul_nonneg (hfNonneg ω) (hgNonneg ω))).mp hlinFinite

/-- The real integral identity now requires no product-integrability hypothesis. -/
theorem integral_mul_of_nonneg_condExp_const [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (f g : Ω → ℝ) (constant : ℝ)
    (hf : StronglyMeasurable[m] f) (hfInt : Integrable f μ) (hgInt : Integrable g μ)
    (hfNonneg : ∀ ω, 0 ≤ f ω) (hgNonneg : ∀ ω, 0 ≤ g ω)
    (hconditional : μ[g | m] =ᵐ[μ] fun _ => constant) :
    (∫ ω, f ω * g ω ∂μ) = (∫ ω, f ω ∂μ) * constant := by
  exact ConditionalMoment.integral_mul_of_condExp_const hm f g constant hf
    (integrable_mul_of_nonneg_condExp_const hm f g constant hf hfInt hgInt
      hfNonneg hgNonneg hconditional) hgInt hconditional

/-- Every exponential prefix is integrable from the individual conditional moments alone. -/
theorem pathExp_prefix_integrable [IsProbabilityMeasure μ]
    (ℱ : Filtration Nat mΩ) (θ constant : ℝ)
    (wait : Nat → Ω → ℝ) (length : Nat)
    (hknown : ∀ i < length, StronglyMeasurable[ℱ (i + 1)] (wait i))
    (hwaitInt : ∀ i < length, Integrable (fun ω => Real.exp (θ * wait i ω)) μ)
    (hconditional : ∀ i < length,
      μ[(fun ω => Real.exp (θ * wait i ω)) | ℱ i] =ᵐ[μ] fun _ => constant) :
    ∀ n ≤ length, Integrable (ConditionalMoment.pathExp θ wait n) μ := by
  intro n
  induction n with
  | zero =>
      intro _
      unfold ConditionalMoment.pathExp
      change Integrable (fun _ : Ω => Real.exp (θ * 0)) μ
      exact integrable_const _
  | succ n ih =>
      intro hn
      have hlt : n < length := Nat.lt_of_succ_le hn
      have hle : n ≤ length := (Nat.le_succ n).trans hn
      have hpmeas := ConditionalMoment.pathExp_stronglyMeasurable
        ℱ θ wait length hknown hle
      have hprod : Integrable
          (fun ω => ConditionalMoment.pathExp θ wait n ω * Real.exp (θ * wait n ω)) μ :=
        integrable_mul_of_nonneg_condExp_const (ℱ.le n)
          (ConditionalMoment.pathExp θ wait n) (fun ω => Real.exp (θ * wait n ω))
          constant hpmeas (ih hle) (hwaitInt n hlt)
          (fun ω => (Real.exp_pos _).le) (fun ω => (Real.exp_pos _).le)
          (hconditional n hlt)
      simpa only [ConditionalMoment.pathExp_succ, Pi.mul_def] using hprod

/-- Fixed-path exponential integrability without the old `hprefixInt` input. -/
theorem fixed_path_exponential_integrable [IsProbabilityMeasure μ]
    (ℱ : Filtration Nat mΩ) (θ constant : ℝ)
    (wait : Nat → Ω → ℝ) (length : Nat)
    (hknown : ∀ i < length, StronglyMeasurable[ℱ (i + 1)] (wait i))
    (hwaitInt : ∀ i < length, Integrable (fun ω => Real.exp (θ * wait i ω)) μ)
    (hconditional : ∀ i < length,
      μ[(fun ω => Real.exp (θ * wait i ω)) | ℱ i] =ᵐ[μ] fun _ => constant) :
    Integrable (ConditionalMoment.pathExp θ wait length) μ :=
  pathExp_prefix_integrable ℱ θ constant wait length hknown hwaitInt hconditional length le_rfl

/-- Fixed-path exponential moment without the old `hprefixInt` input. -/
theorem fixed_path_exponential_moment [IsProbabilityMeasure μ]
    (ℱ : Filtration Nat mΩ) (θ constant : ℝ)
    (wait : Nat → Ω → ℝ) (length : Nat)
    (hknown : ∀ i < length, StronglyMeasurable[ℱ (i + 1)] (wait i))
    (hwaitInt : ∀ i < length, Integrable (fun ω => Real.exp (θ * wait i ω)) μ)
    (hconditional : ∀ i < length,
      μ[(fun ω => Real.exp (θ * wait i ω)) | ℱ i] =ᵐ[μ] fun _ => constant) :
    (∫ ω, Real.exp (θ * ConditionalMoment.prefixSum wait length ω) ∂μ) =
      constant ^ length :=
  ConditionalMoment.fixed_path_exponential_moment ℱ θ constant wait length hknown hwaitInt
    (pathExp_prefix_integrable ℱ θ constant wait length hknown hwaitInt hconditional) hconditional

/-- Rate-one conditional exponential moment, still explicitly conditional on its one-step input. -/
theorem fixed_path_rate_one_moment [IsProbabilityMeasure μ]
    (ℱ : Filtration Nat mΩ) (θ : ℝ) (wait : Nat → Ω → ℝ) (length : Nat)
    (hknown : ∀ i < length, StronglyMeasurable[ℱ (i + 1)] (wait i))
    (hwaitInt : ∀ i < length, Integrable (fun ω => Real.exp (θ * wait i ω)) μ)
    (hconditional : ∀ i < length,
      μ[(fun ω => Real.exp (θ * wait i ω)) | ℱ i] =ᵐ[μ]
        fun _ => (1 - θ)⁻¹) :
    (∫ ω, Real.exp (θ * ConditionalMoment.prefixSum wait length ω) ∂μ) =
      ((1 - θ)⁻¹) ^ length :=
  fixed_path_exponential_moment ℱ θ ((1 - θ)⁻¹) wait length hknown hwaitInt hconditional

end MathResearchAnalysis.NonnegativeMoment
