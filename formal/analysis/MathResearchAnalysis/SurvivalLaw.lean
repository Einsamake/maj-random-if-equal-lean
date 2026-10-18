module

public import MathResearchAnalysis.ExponentialMoment
public import MathResearchAnalysis.ExponentialMemoryless

set_option autoImplicit false

/-!
# From joint survival probabilities to exponential law and independence

This module is a measure-theoretic conversion theorem. Its joint survival
premise must be proved for a concrete waiting variable before the results
can be applied. No stopped-clock law or strong Markov property is assumed
to have been established by this conversion alone.
-/

public noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace MathResearchAnalysis.SurvivalLaw

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {D : Ω → ℝ}

/-- Every event in the specified history has the same exponential survival factor. -/
@[expose] def JointSurvival (D : Ω → ℝ) (m : MeasurableSpace Ω)
    (μ : @Measure Ω mΩ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ E : Set Ω, MeasurableSet[m] E →
    μ (E ∩ {ω | t < D ω}) = ENNReal.ofReal (exp (-t)) * μ E

variable [IsProbabilityMeasure μ]



/-- Joint survival determines the full finite measure on any history event. -/
theorem restricted_map_eq
    (hD : Measurable D) (hnonnegative : ∀ ω, 0 ≤ D ω)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (hsurvival : @JointSurvival Ω mΩ D m μ)
    (E : Set Ω) (hE : MeasurableSet[m] E) :
    @Measure.map Ω ℝ mΩ _ D (μ.restrict E) = μ E • expMeasure 1 := by
  let : MeasurableSpace Ω := mΩ
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply hD measurableSet_Iic,
    Measure.restrict_apply (measurableSet_Iic.preimage hD), Measure.smul_apply]
  by_cases ht : 0 ≤ t
  · have htail : μ.real (E ∩ {ω | t < D ω}) = exp (-t) * μ.real E := by
      change (μ (E ∩ {ω | t < D ω})).toReal = _
      rw [hsurvival t ht E hE, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (exp_pos _).le]
      rfl
    have hsets : D ⁻¹' Iic t ∩ E = E \ (E ∩ {ω | t < D ω}) := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_sdiff, mem_ofPred_eq]
      simp only [not_and, not_lt]
      tauto
    have hcdf : μ.real (D ⁻¹' Iic t ∩ E) = μ.real E * (1 - exp (-t)) := by
      rw [hsets, measureReal_sdiff inter_subset_left
        ((hm _ hE).inter (measurableSet_lt measurable_const hD)), htail]
      ring
    rw [← ofReal_measureReal, hcdf, ← ofReal_cdf,
      cdf_expMeasure_eq (by norm_num)]
    simp only [ite_eq_left ht, one_mul, smul_eq_mul]
    rw [ENNReal.ofReal_mul measureReal_nonneg, ofReal_measureReal]
  · have hevent : D ⁻¹' Iic t ∩ E = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have hle : D ω ≤ t := hω.1
      exact ht (le_trans (hnonnegative ω) hle)
    rw [hevent, measure_empty, ← ofReal_cdf, cdf_expMeasure_eq (by norm_num)]
    simp only [ite_eq_right ht, ENNReal.ofReal_zero, smul_eq_mul, mul_zero]

/-- The unconditional exponential law is the special case of the whole history event. -/
theorem hasLaw_of_jointSurvival
    (hD : Measurable D) (hnonnegative : ∀ ω, 0 ≤ D ω)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (hsurvival : @JointSurvival Ω mΩ D m μ) :
    HasLaw D (expMeasure 1) μ := by
  let : MeasurableSpace Ω := mΩ
  refine ⟨hD.aemeasurable, ?_⟩
  have h := restricted_map_eq hD hnonnegative hm hsurvival Set.univ MeasurableSet.univ
  simpa only [Measure.restrict_univ, measure_univ, one_smul] using h

/-- Equality of the restricted laws gives independence for every Borel event. -/
theorem indep_of_jointSurvival
    (hD : Measurable D) (hnonnegative : ∀ ω, 0 ≤ D ω)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (hsurvival : @JointSurvival Ω mΩ D m μ) :
    Indep ((borel ℝ).comap D) m μ := by
  let : MeasurableSpace Ω := mΩ
  rw [Indep_iff]
  intro A E hA hE
  rcases (MeasurableSpace.measurableSet_comap.mp hA) with ⟨B, hB, rfl⟩
  have hlaw := hasLaw_of_jointSurvival hD hnonnegative hm hsurvival
  have h := congrArg (fun ν : Measure ℝ => ν B)
    (restricted_map_eq hD hnonnegative hm hsurvival E hE)
  rw [Measure.map_apply hD hB, Measure.restrict_apply (hB.preimage hD),
    Measure.smul_apply] at h
  have hmarginal : μ (D ⁻¹' B) = expMeasure 1 B := by
    rw [← hlaw.map_eq, Measure.map_apply hD hB]
  simpa only [hmarginal, smul_eq_mul, mul_comm] using h

/-- The proved law and history independence supply the genuine conditional MGF. -/
theorem condExp_of_jointSurvival {θ : ℝ} (hθ : θ < 1)
    (hD : Measurable D) (hnonnegative : ∀ ω, 0 ≤ D ω)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (hsurvival : @JointSurvival Ω mΩ D m μ) :
    μ[(fun ω => exp (θ * D ω)) | m] =ᵐ[μ] fun _ => (1 - θ)⁻¹ := by
  let : MeasurableSpace Ω := mΩ
  exact ExponentialMoment.condExp_of_hasLaw_indep hθ
    (hasLaw_of_jointSurvival hD hnonnegative hm hsurvival) hD hm
    (indep_of_jointSurvival hD hnonnegative hm hsurvival)

/-- The integrability required by path bounds follows from the identified law. -/
theorem integrable_of_jointSurvival {θ : ℝ} (hθ : θ < 1)
    (hD : Measurable D) (hnonnegative : ∀ ω, 0 ≤ D ω)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (hsurvival : @JointSurvival Ω mΩ D m μ) :
    Integrable (fun ω => exp (θ * D ω)) μ := by
  let : MeasurableSpace Ω := mΩ
  exact ExponentialMoment.integrable_of_hasLaw hθ
    (hasLaw_of_jointSurvival hD hnonnegative hm hsurvival)

omit [IsProbabilityMeasure μ] in
/-- Changing a variable on a null event preserves every joint survival probability. -/
theorem jointSurvival_congr {D' : Ω → ℝ} (hDD' : D' =ᵐ[μ] D)
    {m : MeasurableSpace Ω} (hsurvival : @JointSurvival Ω mΩ D m μ) :
    @JointSurvival Ω mΩ D' m μ := by
  let : MeasurableSpace Ω := mΩ
  intro t ht E hE
  calc
    μ (E ∩ {ω | t < D' ω}) = μ (E ∩ {ω | t < D ω}) := by
      apply measure_congr
      filter_upwards [hDD'] with ω hω
      simp only [mem_inter_iff, mem_ofPred_eq, hω]
    _ = _ := hsurvival t ht E hE

/-- The restricted-law identity only needs almost-everywhere nonnegativity. -/
theorem restricted_map_eq_ae
    (hD : Measurable D) (hnonnegative : ∀ᵐ ω ∂μ, 0 ≤ D ω)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hsurvival : @JointSurvival Ω mΩ D m μ)
    (E : Set Ω) (hE : MeasurableSet[m] E) :
    @Measure.map Ω ℝ mΩ _ D (μ.restrict E) = μ E • expMeasure 1 := by
  let : MeasurableSpace Ω := mΩ
  have heq : (fun ω => max (D ω) 0) =ᵐ[μ] D := by
    filter_upwards [hnonnegative] with ω hω
    exact max_eq_left hω
  calc
    (μ.restrict E).map D = (μ.restrict E).map (fun ω => max (D ω) 0) :=
      Measure.map_congr (ae_restrict_of_ae heq.symm)
    _ = _ := restricted_map_eq (hD.max measurable_const)
      (fun ω => le_max_right (D ω) 0) hm (jointSurvival_congr heq hsurvival) E hE

/-- The full exponential law under almost-everywhere nonnegativity. -/
theorem hasLaw_of_jointSurvival_ae
    (hD : Measurable D) (hnonnegative : ∀ᵐ ω ∂μ, 0 ≤ D ω)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hsurvival : @JointSurvival Ω mΩ D m μ) :
    HasLaw D (expMeasure 1) μ := by
  let : MeasurableSpace Ω := mΩ
  refine ⟨hD.aemeasurable, ?_⟩
  have h := restricted_map_eq_ae hD hnonnegative hm hsurvival Set.univ MeasurableSet.univ
  simpa only [Measure.restrict_univ, measure_univ, one_smul] using h

/-- Independence is unchanged by null exceptional paths of a nonnegative waiting variable. -/
theorem indep_of_jointSurvival_ae
    (hD : Measurable D) (hnonnegative : ∀ᵐ ω ∂μ, 0 ≤ D ω)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hsurvival : @JointSurvival Ω mΩ D m μ) :
    Indep ((borel ℝ).comap D) m μ := by
  let : MeasurableSpace Ω := mΩ
  rw [Indep_iff]
  intro A E hA hE
  rcases (MeasurableSpace.measurableSet_comap.mp hA) with ⟨B, hB, rfl⟩
  have hlaw := hasLaw_of_jointSurvival_ae hD hnonnegative hm hsurvival
  have h := congrArg (fun ν : Measure ℝ => ν B)
    (restricted_map_eq_ae hD hnonnegative hm hsurvival E hE)
  rw [Measure.map_apply hD hB, Measure.restrict_apply (hB.preimage hD),
    Measure.smul_apply] at h
  have hmarginal : μ (D ⁻¹' B) = expMeasure 1 B := by
    rw [← hlaw.map_eq, Measure.map_apply hD hB]
  simpa only [hmarginal, smul_eq_mul, mul_comm] using h

/-- Genuine conditional exponential moments, allowing null exceptional paths. -/
theorem condExp_of_jointSurvival_ae {θ : ℝ} (hθ : θ < 1)
    (hD : Measurable D) (hnonnegative : ∀ᵐ ω ∂μ, 0 ≤ D ω)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hsurvival : @JointSurvival Ω mΩ D m μ) :
    μ[(fun ω => exp (θ * D ω)) | m] =ᵐ[μ] fun _ => (1 - θ)⁻¹ := by
  let : MeasurableSpace Ω := mΩ
  exact ExponentialMoment.condExp_of_hasLaw_indep hθ
    (hasLaw_of_jointSurvival_ae hD hnonnegative hm hsurvival) hD hm
    (indep_of_jointSurvival_ae hD hnonnegative hm hsurvival)

/-- Exponential integrability under the same almost-everywhere hypotheses. -/
theorem integrable_of_jointSurvival_ae {θ : ℝ} (hθ : θ < 1)
    (hD : Measurable D) (hnonnegative : ∀ᵐ ω ∂μ, 0 ≤ D ω)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hsurvival : @JointSurvival Ω mΩ D m μ) :
    Integrable (fun ω => exp (θ * D ω)) μ := by
  let : MeasurableSpace Ω := mΩ
  exact ExponentialMoment.integrable_of_hasLaw hθ
    (hasLaw_of_jointSurvival_ae hD hnonnegative hm hsurvival)

end MathResearchAnalysis.SurvivalLaw



