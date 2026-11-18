module
public import MathResearchAnalysis.OriginalQuadraticLower
set_option autoImplicit false
@[expose] public noncomputable section
namespace MathResearchLower
open MathResearchAnalysis MeasureTheory
open PerturbationSymmetry (squareConfig)
open scoped ENNReal

/-- A site whose radius-t neighbourhood started occupied survives round t. -/
theorem interior_survives (N : ℕ) (marks : InfiniteGridModel.Marks) (t : ℕ)
    (v : InfiniteGridModel.Site) (hx : (t : ℤ) ≤ v.1) (hx' : v.1 + t < (N : ℤ))
    (hy : (t : ℤ) ≤ v.2) (hy' : v.2 + t < (N : ℤ)) :
    InfiniteGridModel.synchronous marks (squareConfig N) t v = true := by
  induction t generalizing v with
  | zero =>
    apply decide_eq_true
    simpa [InfiniteGridModel.Inside] using And.intro hx (And.intro hx' (And.intro hy hy'))
  | succ t ih =>
    rw [InfiniteGridModel.synchronous_succ]
    change InfiniteGridModel.majority4 _ _ _ _ _ = true
    rw [ih (InfiniteGridModel.north v) (by dsimp [InfiniteGridModel.north]; omega)
        (by dsimp [InfiniteGridModel.north]; omega) (by dsimp [InfiniteGridModel.north]; omega) (by dsimp [InfiniteGridModel.north]; omega),
      ih (InfiniteGridModel.east v) (by dsimp [InfiniteGridModel.east]; omega)
        (by dsimp [InfiniteGridModel.east]; omega) (by dsimp [InfiniteGridModel.east]; omega) (by dsimp [InfiniteGridModel.east]; omega),
      ih (InfiniteGridModel.south v) (by dsimp [InfiniteGridModel.south]; omega)
        (by dsimp [InfiniteGridModel.south]; omega) (by dsimp [InfiniteGridModel.south]; omega) (by dsimp [InfiniteGridModel.south]; omega),
      ih (InfiniteGridModel.west v) (by dsimp [InfiniteGridModel.west]; omega)
        (by dsimp [InfiniteGridModel.west]; omega) (by dsimp [InfiniteGridModel.west]; omega) (by dsimp [InfiniteGridModel.west]; omega)]
    rfl

theorem pathwise_survival {N k : ℕ} (hk : 2*k < N) (η : InfiniteGridRandomDynamics.Sample) :
    (k : ℕ∞) < HomogeneousRecoveryTime.synchronous (squareConfig N) η := by
  rw [HomogeneousRecoveryTime.synchronous_eq_zero_background N _
    (OriginalQuadraticLower.square_supported_mono (le_refl N)), InfiniteGridRecoveryTime.synchronous_tail_iff]
  intro he
  have h := congrFun he ((k : ℤ),(k : ℤ))
  have hs := interior_survives N (InfiniteGridRandomDynamics.marks η) k
    ((k : ℤ),(k : ℤ)) le_rfl (by dsimp; omega) le_rfl (by dsimp; omega)
  change InfiniteGridModel.synchronous _ _ k _ = false at h
  rw [hs] at h
  contradiction

theorem square_expected_ge_half (N : ℕ) :
    ENNReal.ofReal ((N : ℝ)/2) ≤ OriginalRecoveryProfile.expectedRecovery (squareConfig N) := by
  by_cases hn : N = 0
  · simp [hn]
  let k := (N-1)/2
  have hhalf : N ≤ 2*(k+1) := by dsimp [k]; omega
  have hr : (N : ℝ) ≤ 2*((k+1 : ℕ) : ℝ) := by exact_mod_cast hhalf
  have hreal : ENNReal.ofReal ((N : ℝ)/2) ≤ (↑(k+1 : ℕ) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast]; apply ENNReal.ofReal_le_ofReal; linarith
  apply hreal.trans
  calc
    _ = ∫⁻ _η, (↑(k+1 : ℕ) : ℝ≥0∞) ∂InfiniteGridRandomDynamics.measure := by simp
    _ ≤ OriginalRecoveryProfile.expectedRecovery (squareConfig N) := by
      apply lintegral_mono
      intro η
      have h := pathwise_survival (N := N) (k := k) (by dsimp [k]; omega) η
      have hb : ((k+1 : ℕ) : ℕ∞) ≤ HomogeneousRecoveryTime.synchronous (squareConfig N) η := by
        cases he : HomogeneousRecoveryTime.synchronous (squareConfig N) η using ENat.recTopCoe with
        | top => exact le_top
        | coe n => rw [he] at h; exact_mod_cast (show k+1 ≤ n from Nat.succ_le_of_lt (ENat.natCast_lt_natCast.mp h))
      exact ENat.toENNReal_mono hb

/-- The contribution of the first K survival probabilities, also if the time can be infinite. -/
theorem finite_tail_sum_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → ℕ∞) (hT : Measurable T) (K : ℕ) :
    ENNReal.ofReal (∑ k ∈ Finset.range K, μ.real {ω | (k : ℕ∞) < T ω}) ≤
      ExtendedRecoveryExpectation.expectation μ T := by
  classical
  let A (k : ℕ) := {ω | (k : ℕ∞) < T ω}
  have hm (k : ℕ) : MeasurableSet (A k) := by
    simpa only [A,Nat.one_mul] using ExtendedBlockTail.measurableSet_blockTail T hT k 1
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => measureReal_nonneg)]
  calc
    _ = ∑ k ∈ Finset.range K, ∫⁻ ω, (A k).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [lintegral_indicator_const (hm k),one_mul,ofReal_measureReal (measure_ne_top μ _)]
    _ = ∫⁻ ω, ∑ k ∈ Finset.range K, (A k).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
      rw [lintegral_finsetSum _ (fun k _ => measurable_const.indicator (hm k))]
    _ ≤ _ := by
      apply lintegral_mono
      intro ω
      cases he : T ω using ENat.recTopCoe with
      | top => simp [he]
      | coe n =>
        change _ ≤ (T ω).toENNReal
        simp only [Set.indicator_apply, A, Set.mem_ofPred_eq, he, ENat.natCast_lt_natCast, ENat.toENNReal_coe]
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast (Finset.card_le_card (show (Finset.range K).filter (· < n) ⊆ Finset.range n from
          fun k hk => Finset.mem_range.mpr (Finset.mem_filter.mp hk).2)).trans_eq (Finset.card_range n)

end MathResearchLower
