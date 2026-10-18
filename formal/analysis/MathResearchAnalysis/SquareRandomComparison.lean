module

public import MathResearchAnalysis.SquareRandomDynamics
public import MathResearchAnalysis.ClockRecoveryComparison

set_option autoImplicit false

/-!
# Actual independent-mark synchronous/checkerboard probability comparisons

Both phases use the same fair mark field as the synchronous trajectory. Only
a union bound is used; independence of the two checkerboard chains is not
assumed. Every fixed scan kernel is the actual checkerboard endpoint law.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace MathResearchAnalysis.SquareRandomComparison

abbrev Config (n : Nat) := SquareSpin.Config n
abbrev Sample (n : Nat) := SquareRandomDynamics.Sample n

abbrev zeroConfig (n : Nat) : Config n := fun _ => false

theorem isZero_iff_eq_zero {n : Nat} (f : Config n) :
    BipartiteDynamics.IsZero f ↔ f = zeroConfig n :=
  ⟨fun h => funext h, fun h v => congrFun h v⟩

theorem state_nonzero_probability_eq_integral {n : Nat} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → Config n) (hf : Measurable f) :
    μ.real {ω | f ω ≠ zeroConfig n} =
      ∫ ω, ClockRecoveryComparison.nonzero (f ω) ∂μ := by
  classical
  have hE : MeasurableSet {ω | f ω ≠ zeroConfig n} :=
    (hf (measurableSet_singleton (zeroConfig n))).compl
  have heq : (fun ω => ClockRecoveryComparison.nonzero (f ω)) =
      {ω | f ω ≠ zeroConfig n}.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h : f ω = zeroConfig n <;> simp [ClockRecoveryComparison.nonzero, h]
  rw [heq]
  simpa only [smul_eq_mul, mul_one] using
    (integral_indicator_const (μ := μ) (1 : ℝ) hE).symm

def synchronousProbability (n : Nat) (initial : Config n) (t : Nat) : ℝ :=
  (SquareRandomDynamics.measure n).real
    {η | SquareRandomDynamics.synchronous n initial t η ≠ zeroConfig n}

def alternatingProbability (n : Nat) (initial : Config n) (phase : Bool) (t : Nat) : ℝ :=
  (SquareRandomDynamics.measure n).real
    {η | SquareRandomDynamics.alternating n initial phase t η ≠ zeroConfig n}

theorem alternatingProbability_eq_integral (n : Nat) (initial : Config n)
    (phase : Bool) (t : Nat) :
    alternatingProbability n initial phase t =
      ∫ η, ClockRecoveryComparison.nonzero
        (SquareRandomDynamics.alternating n initial phase t η) ∂SquareRandomDynamics.measure n :=
  state_nonzero_probability_eq_integral _ _
    (SquareRandomDynamics.alternating_measurable n initial phase t)

theorem alternatingProbability_top_eq_scanProbability (n : Nat) (phase : Bool) (t : Nat) :
    alternatingProbability n (SquarePWMeasure.topConfig n) phase t =
      ClockRecoveryComparison.scanProbability n (!phase) t := by
  rw [alternatingProbability_eq_integral]
  exact SquareRandomDynamics.integral_alternating_eq_scanMean n
    (SquarePWMeasure.topConfig n) phase t ClockRecoveryComparison.nonzero

theorem synchronous_nonzero_implies_phase_nonzero (n : Nat) (initial : Config n)
    (t : Nat) (η : Sample n)
    (h : SquareRandomDynamics.synchronous n initial t η ≠ zeroConfig n) :
    SquareRandomDynamics.alternating n initial false t η ≠ zeroConfig n ∨
      SquareRandomDynamics.alternating n initial true t η ≠ zeroConfig n := by
  by_cases hf : SquareRandomDynamics.alternating n initial false t η = zeroConfig n
  · right
    intro ht
    apply h
    exact (isZero_iff_eq_zero _).mp
      (SquareDynamics.both_alternating_zero_implies_synchronous_zero
        (SquareRandomDynamics.marks η) initial t
        ((isZero_iff_eq_zero _).mpr hf) ((isZero_iff_eq_zero _).mpr ht))
  · exact Or.inl hf

/-- No independence premise on the two common-mark checkerboard phases. -/
theorem synchronousProbability_le_sum_alternating (n : Nat) (initial : Config n) (t : Nat) :
    synchronousProbability n initial t ≤ alternatingProbability n initial false t +
      alternatingProbability n initial true t := by
  apply (measureReal_mono (fun η h =>
    synchronous_nonzero_implies_phase_nonzero n initial t η h)).trans
  exact measureReal_union_le _ _

theorem alternating_next_nonzero_implies_synchronous_nonzero (n : Nat)
    (initial : Config n) (phase : Bool) (t : Nat) (η : Sample n)
    (h : SquareRandomDynamics.alternating n initial phase (t + 1) η ≠ zeroConfig n) :
    SquareRandomDynamics.synchronous n initial t η ≠ zeroConfig n := by
  intro hz
  apply h
  exact (isZero_iff_eq_zero _).mp
    (SquareDynamics.synchronous_zero_implies_alternating_next_zero
      (SquareRandomDynamics.marks η) initial phase t ((isZero_iff_eq_zero _).mpr hz))

theorem alternatingProbability_next_le_synchronous (n : Nat) (initial : Config n)
    (phase : Bool) (t : Nat) :
    alternatingProbability n initial phase (t + 1) ≤ synchronousProbability n initial t :=
  measureReal_mono (fun η h =>
    alternating_next_nonzero_implies_synchronous_nonzero n initial phase t η h)

theorem synchronous_initial_mono {n : Nat} (η : Sample n)
    {first second : Config n} (h : first ≤ second) (t : Nat) :
    SquareRandomDynamics.synchronous n first t η ≤
      SquareRandomDynamics.synchronous n second t η := by
  induction t with
  | zero => exact h
  | succ t ih => exact SquareSpin.synchronousStep_mono ih _

theorem alternating_initial_mono {n : Nat} (η : Sample n)
    {first second : Config n} (h : first ≤ second) (phase : Bool) (t : Nat) :
    SquareRandomDynamics.alternating n first phase t η ≤
      SquareRandomDynamics.alternating n second phase t η := by
  induction t with
  | zero => exact h
  | succ t ih => exact SquareSpin.checkerboardStep_mono ih _ _

theorem nonzero_of_le {n : Nat} {f g : Config n} (hfg : f ≤ g)
    (hf : f ≠ zeroConfig n) : g ≠ zeroConfig n := by
  intro hg
  apply hf
  exact le_antisymm (by simpa only [hg] using hfg) (fun _ => Bool.false_le _)

theorem synchronousProbability_initial_mono {n : Nat} {first second : Config n}
    (h : first ≤ second) (t : Nat) :
    synchronousProbability n first t ≤ synchronousProbability n second t :=
  measureReal_mono (fun η hn => nonzero_of_le (synchronous_initial_mono η h t) hn)

theorem synchronousProbability_le_top (n : Nat) (initial : Config n) (t : Nat) :
    synchronousProbability n initial t ≤ synchronousProbability n (SquarePWMeasure.topConfig n) t :=
  synchronousProbability_initial_mono (fun _ => Bool.le_true _) t

end MathResearchAnalysis.SquareRandomComparison
