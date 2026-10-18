module

public import MathResearchAnalysis.SquareGridEmbedding
public import MathResearchAnalysis.InfiniteGridRecoveryTime
public import MathResearchAnalysis.RecoveryTimeTransport
public import MathResearchAnalysis.SquareRecoveryTime
public import MathResearchAnalysis.SquareRandomRestart
public import MathResearchAnalysis.InfiniteGridTranslationLaw

set_option autoImplicit false

/-!
# Exact random-process and extended-recovery laws under square embedding

Restriction transports the entire infinite fair mark field, not only a finite
prefix. Full configuration identities imply equality of genuine first-hit
times even at infinity, and hence their laws and recovery tails. The side is
explicitly n+2. Translation, background complementation and original diameter
parameters are separate later connections.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace MathResearchAnalysis.SquareGridLaw

abbrev GridSample := InfiniteGridRandomDynamics.Sample
abbrev GridConfig := InfiniteGridModel.Config

def eventEmbedding (n : Nat) (e : SquareSpin.Event n) : InfiniteGridRandomDynamics.Event :=
  (SquareGridEmbedding.embed n e.1, e.2)

theorem eventEmbedding_injective (n : Nat) : Function.Injective (eventEmbedding n) := by
  intro a b h
  exact Prod.ext ((SquareGridEmbedding.embed_injective n)
    (congrArg (fun e : InfiniteGridRandomDynamics.Event => e.1) h))
    (congrArg (fun e : InfiniteGridRandomDynamics.Event => e.2) h)

def restrictSample (n : Nat) : GridSample → SquareRandomDynamics.Sample n :=
  FairMarksTransport.pullback (eventEmbedding n)

theorem restrictSample_measurable (n : Nat) : Measurable (restrictSample n) :=
  FairMarksTransport.pullback_measurable (eventEmbedding n)

theorem restrictSample_map_measure (n : Nat) :
    Measure.map (restrictSample n) InfiniteGridRandomDynamics.measure =
      SquareRandomDynamics.measure n :=
  FairMarksTransport.map_pullback (eventEmbedding n) (eventEmbedding_injective n)

theorem restrictSample_hasLaw (n : Nat) :
    HasLaw (restrictSample n) (SquareRandomDynamics.measure n)
      InfiniteGridRandomDynamics.measure where
  aemeasurable := (restrictSample_measurable n).aemeasurable
  map_eq := restrictSample_map_measure n

theorem restrictSample_measure_preimage (n : Nat) (E : Set (SquareRandomDynamics.Sample n))
    (hE : MeasurableSet E) :
    InfiniteGridRandomDynamics.measure ((restrictSample n) ⁻¹' E) =
      SquareRandomDynamics.measure n E := by
  rw [← restrictSample_map_measure, Measure.map_apply (restrictSample_measurable n) hE]

theorem restrictSample_real_preimage (n : Nat) (E : Set (SquareRandomDynamics.Sample n))
    (hE : MeasurableSet E) :
    InfiniteGridRandomDynamics.measure.real ((restrictSample n) ⁻¹' E) =
      (SquareRandomDynamics.measure n).real E := by
  exact congrArg ENNReal.toReal (restrictSample_measure_preimage n E hE)

theorem marks_restrictSample (n : Nat) (η : GridSample) :
    SquareRandomDynamics.marks (restrictSample n η) =
      SquareGridEmbedding.restrictMarks n (InfiniteGridRandomDynamics.marks η) := rfl

theorem synchronous_extend (n : Nat) (g : SquareSpin.Config n) (t : Nat) (η : GridSample) :
    InfiniteGridRandomDynamics.synchronous (SquareGridEmbedding.extend n g) t η =
      SquareGridEmbedding.extend n
        (SquareRandomDynamics.synchronous n g t (restrictSample n η)) :=
  SquareGridEmbedding.synchronous_extend n (InfiniteGridRandomDynamics.marks η) g t

theorem alternating_extend (n : Nat) (g : SquareSpin.Config n) (phase : Bool)
    (t : Nat) (η : GridSample) :
    InfiniteGridRandomDynamics.alternating (SquareGridEmbedding.extend n g) phase t η =
      SquareGridEmbedding.extend n
        (SquareRandomDynamics.alternating n g phase t (restrictSample n η)) :=
  SquareGridEmbedding.alternating_extend n (InfiniteGridRandomDynamics.marks η) g phase t

theorem synchronous_recovery_eq (n : Nat) (g : SquareSpin.Config n) (η : GridSample) :
    InfiniteGridRecoveryTime.synchronous (SquareGridEmbedding.extend n g) η =
      SquareRecoveryTime.synchronous n g (restrictSample n η) := by
  apply RecoveryTimeTransport.time_eq_of_zero_iff
  intro t
  rw [synchronous_extend]
  exact SquareGridEmbedding.extend_eq_zero_iff n _

theorem alternating_recovery_eq (n : Nat) (g : SquareSpin.Config n) (phase : Bool)
    (η : GridSample) :
    InfiniteGridRecoveryTime.alternating (SquareGridEmbedding.extend n g) phase η =
      SquareRecoveryTime.alternating n g phase (restrictSample n η) := by
  apply RecoveryTimeTransport.time_eq_of_zero_iff
  intro t
  rw [alternating_extend]
  exact SquareGridEmbedding.extend_eq_zero_iff n _

theorem synchronous_recovery_map (n : Nat) (g : SquareSpin.Config n) :
    Measure.map (InfiniteGridRecoveryTime.synchronous (SquareGridEmbedding.extend n g))
        InfiniteGridRandomDynamics.measure =
      Measure.map (SquareRecoveryTime.synchronous n g) (SquareRandomDynamics.measure n) := by
  have hf : InfiniteGridRecoveryTime.synchronous (SquareGridEmbedding.extend n g) =
      SquareRecoveryTime.synchronous n g ∘ restrictSample n :=
    funext (synchronous_recovery_eq n g)
  rw [hf, ← Measure.map_map (SquareRecoveryTime.synchronous_measurable n g)
    (restrictSample_measurable n), restrictSample_map_measure]

theorem alternating_recovery_map (n : Nat) (g : SquareSpin.Config n) (phase : Bool) :
    Measure.map (InfiniteGridRecoveryTime.alternating (SquareGridEmbedding.extend n g) phase)
        InfiniteGridRandomDynamics.measure =
      Measure.map (SquareRecoveryTime.alternating n g phase) (SquareRandomDynamics.measure n) := by
  have hf : InfiniteGridRecoveryTime.alternating (SquareGridEmbedding.extend n g) phase =
      SquareRecoveryTime.alternating n g phase ∘ restrictSample n :=
    funext (alternating_recovery_eq n g phase)
  rw [hf, ← Measure.map_map (SquareRecoveryTime.alternating_measurable n g phase)
    (restrictSample_measurable n), restrictSample_map_measure]

theorem synchronous_tail_probability (n : Nat) (g : SquareSpin.Config n) (t : Nat) :
    InfiniteGridRandomDynamics.measure.real
        {η | (t : ℕ∞) < InfiniteGridRecoveryTime.synchronous (SquareGridEmbedding.extend n g) η} =
      (SquareRandomDynamics.measure n).real
        {ξ | (t : ℕ∞) < SquareRecoveryTime.synchronous n g ξ} := by
  simp_rw [synchronous_recovery_eq]
  apply restrictSample_real_preimage n {ξ | (t : ℕ∞) < SquareRecoveryTime.synchronous n g ξ}
  have hE := (ExtendedRecoveryTime.measurableSet_time_le_nat
    (SquareRandomDynamics.synchronous n g) (SquareRandomComparison.zeroConfig n)
    (SquareRandomDynamics.synchronous_measurable n g) t).compl
  simpa only [Set.compl_ofPred, not_le, SquareRecoveryTime.synchronous] using hE

theorem alternating_tail_probability (n : Nat) (g : SquareSpin.Config n) (phase : Bool)
    (t : Nat) :
    InfiniteGridRandomDynamics.measure.real
        {η | (t : ℕ∞) < InfiniteGridRecoveryTime.alternating (SquareGridEmbedding.extend n g) phase η} =
      (SquareRandomDynamics.measure n).real
        {ξ | (t : ℕ∞) < SquareRecoveryTime.alternating n g phase ξ} := by
  simp_rw [alternating_recovery_eq]
  apply restrictSample_real_preimage n {ξ | (t : ℕ∞) < SquareRecoveryTime.alternating n g phase ξ}
  have hE := (ExtendedRecoveryTime.measurableSet_time_le_nat
    (SquareRandomDynamics.alternating n g phase) (SquareRandomComparison.zeroConfig n)
    (SquareRandomDynamics.alternating_measurable n g phase) t).compl
  simpa only [Set.compl_ofPred, not_le, SquareRecoveryTime.alternating] using hE

theorem synchronous_supported_recovery_eq (n : Nat) (f : GridConfig)
    (h : InfiniteGridModel.Supported (n + 2) f) (η : GridSample) :
    InfiniteGridRecoveryTime.synchronous f η =
      SquareRecoveryTime.synchronous n (SquareGridEmbedding.restrict n f) (restrictSample n η) := by
  rw [← SquareGridEmbedding.extend_restrict n f h]
  simpa only [SquareGridEmbedding.restrict_extend] using
    synchronous_recovery_eq n (SquareGridEmbedding.restrict n f) η

theorem alternating_supported_recovery_eq (n : Nat) (f : GridConfig)
    (h : InfiniteGridModel.Supported (n + 2) f) (phase : Bool) (η : GridSample) :
    InfiniteGridRecoveryTime.alternating f phase η =
      SquareRecoveryTime.alternating n (SquareGridEmbedding.restrict n f) phase (restrictSample n η) := by
  rw [← SquareGridEmbedding.extend_restrict n f h]
  simpa only [SquareGridEmbedding.restrict_extend] using
    alternating_recovery_eq n (SquareGridEmbedding.restrict n f) phase η

theorem synchronous_supported_recovery_map (n : Nat) (f : GridConfig)
    (h : InfiniteGridModel.Supported (n + 2) f) :
    Measure.map (InfiniteGridRecoveryTime.synchronous f) InfiniteGridRandomDynamics.measure =
      Measure.map (SquareRecoveryTime.synchronous n (SquareGridEmbedding.restrict n f))
        (SquareRandomDynamics.measure n) := by
  conv_lhs => rw [← SquareGridEmbedding.extend_restrict n f h]
  exact synchronous_recovery_map n (SquareGridEmbedding.restrict n f)

theorem alternating_supported_recovery_map (n : Nat) (f : GridConfig)
    (h : InfiniteGridModel.Supported (n + 2) f) (phase : Bool) :
    Measure.map (InfiniteGridRecoveryTime.alternating f phase) InfiniteGridRandomDynamics.measure =
      Measure.map (SquareRecoveryTime.alternating n (SquareGridEmbedding.restrict n f) phase)
        (SquareRandomDynamics.measure n) := by
  conv_lhs => rw [← SquareGridEmbedding.extend_restrict n f h]
  exact alternating_recovery_map n (SquareGridEmbedding.restrict n f) phase

theorem synchronous_supported_tail_probability (n : Nat) (f : GridConfig)
    (h : InfiniteGridModel.Supported (n + 2) f) (t : Nat) :
    InfiniteGridRandomDynamics.measure.real {η | (t : ℕ∞) < InfiniteGridRecoveryTime.synchronous f η} =
      (SquareRandomDynamics.measure n).real
        {ξ | (t : ℕ∞) < SquareRecoveryTime.synchronous n (SquareGridEmbedding.restrict n f) ξ} := by
  conv_lhs => rw [← SquareGridEmbedding.extend_restrict n f h]
  exact synchronous_tail_probability n (SquareGridEmbedding.restrict n f) t

theorem alternating_supported_tail_probability (n : Nat) (f : GridConfig)
    (h : InfiniteGridModel.Supported (n + 2) f) (phase : Bool) (t : Nat) :
    InfiniteGridRandomDynamics.measure.real {η | (t : ℕ∞) < InfiniteGridRecoveryTime.alternating f phase η} =
      (SquareRandomDynamics.measure n).real
        {ξ | (t : ℕ∞) < SquareRecoveryTime.alternating n (SquareGridEmbedding.restrict n f) phase ξ} := by
  conv_lhs => rw [← SquareGridEmbedding.extend_restrict n f h]
  exact alternating_tail_probability n (SquareGridEmbedding.restrict n f) phase t

theorem translated_supported_recovery_map (n : Nat) (a : InfiniteGridModel.Site) (f : GridConfig)
    (h : InfiniteGridModel.Supported (n + 2) f) :
    Measure.map (InfiniteGridRecoveryTime.synchronous (InfiniteGridTranslation.translate a f))
        InfiniteGridRandomDynamics.measure =
      Measure.map (SquareRecoveryTime.synchronous n (SquareGridEmbedding.restrict n f))
        (SquareRandomDynamics.measure n) :=
  (InfiniteGridTranslationLaw.synchronous_recovery_map a f).trans (synchronous_supported_recovery_map n f h)

theorem supported_tail_le_top (n : Nat) (f : GridConfig)
    (h : InfiniteGridModel.Supported (n + 2) f) (t : Nat) :
    InfiniteGridRandomDynamics.measure.real {η | (t : ℕ∞) < InfiniteGridRecoveryTime.synchronous f η} ≤
      InfiniteGridRandomDynamics.measure.real
        {η | (t : ℕ∞) < InfiniteGridRecoveryTime.synchronous
          (SquareGridEmbedding.extend n (SquarePWMeasure.topConfig n)) η} := by
  rw [synchronous_supported_tail_probability n f h, synchronous_tail_probability,
    SquareRecoveryTime.synchronous_tail_probability, SquareRecoveryTime.synchronous_tail_probability]
  exact SquareRandomComparison.synchronousProbability_le_top n (SquareGridEmbedding.restrict n f) t

theorem supported_recovery_block_le_pow (n : Nat) (f : GridConfig)
    (h : InfiniteGridModel.Supported (n + 2) f) (b j : Nat) :
    InfiniteGridRandomDynamics.measure.real
        {η | ((j * b : Nat) : ℕ∞) < InfiniteGridRecoveryTime.synchronous f η} ≤
      (InfiniteGridRandomDynamics.measure.real
        {η | (b : ℕ∞) < InfiniteGridRecoveryTime.synchronous
          (SquareGridEmbedding.extend n (SquarePWMeasure.topConfig n)) η}) ^ j := by
  rw [synchronous_supported_tail_probability n f h, synchronous_tail_probability]
  exact SquareRandomRestart.recovery_block_le_pow n (SquareGridEmbedding.restrict n f) b j

theorem two_way_clock_tail (n : Nat) (c : Bool) (k : Nat) :
    ClockRecoveryComparison.clockProbability n (SchedulingFailure.time k) ≤
        InfiniteGridRandomDynamics.measure.real
          {η | (k : ℕ∞) < InfiniteGridRecoveryTime.synchronous
            (SquareGridEmbedding.extend n (SquarePWMeasure.topConfig n)) η} +
        ((6 : ℝ) / 5) * (n + 2 : ℝ) ^ 2 * ((2 : ℝ)⁻¹) ^ (k + 1) ∧
      InfiniteGridRandomDynamics.measure.real
          {η | ((2 * SchedulingFailure.rankThreshold k + 1 : Nat) : ℕ∞) <
            InfiniteGridRecoveryTime.synchronous
              (SquareGridEmbedding.extend n (SquarePWMeasure.topConfig n)) η} ≤
        2 * ClockRecoveryComparison.clockProbability n (SchedulingFailure.time k) +
          2 * (((6 : ℝ) / 5) * (n + 2 : ℝ) ^ 2 * ((2 : ℝ)⁻¹) ^ (k + 1)) := by
  rw [synchronous_tail_probability, synchronous_tail_probability]
  exact SquareRecoveryTime.two_way_clock_tail n c k

end MathResearchAnalysis.SquareGridLaw
