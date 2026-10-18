module

public import MathResearchAnalysis.FairMarksPastFuture
public import MathResearchAnalysis.SquareDeterministicRestart
public import MathResearchAnalysis.SquareRecoveryTime

set_option autoImplicit false

/-!
# Actual deterministic-time restart and block tails

The current state is a measurable function of used positive past marks.
The complete reindexed future field has its original law and is independent
of that state. Actual restart and top-state domination give multiplicative
tails without a Markov or probability-law hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace MathResearchAnalysis.SquareRandomRestart

abbrev Config (n : Nat) := SquareSpin.Config n
abbrev Sample (n : Nat) := SquareRandomDynamics.Sample n
abbrev Past (n s : Nat) := (SquareTasks.Vertex n × Fin s) → Bool

def fillPast (n s : Nat) (ξ : Past n s) : Sample n := fun e =>
  if h : 0 < e.2 ∧ e.2 ≤ s then ξ (e.1, ⟨e.2 - 1, by omega⟩) else false

theorem fillPast_measurable (n s : Nat) : Measurable (fillPast n s) := by
  apply measurable_pi_iff.mpr
  intro e
  by_cases h : 0 < e.2 ∧ e.2 ≤ s
  · simpa only [fillPast, dite_eq_left h] using
      (measurable_pi_apply (e.1, (⟨e.2 - 1, by omega⟩ : Fin s)))
  · simpa only [fillPast, dite_eq_right h] using
      (show Measurable (fun _ : Past n s => false) from measurable_const)

theorem synchronous_eq_of_agree_upto (n : Nat) (initial : Config n) (t : Nat)
    (η ξ : Sample n) (h : ∀ j, 0 < j → j ≤ t → ∀ v, η (v, j) = ξ (v, j)) :
    SquareRandomDynamics.synchronous n initial t η =
      SquareRandomDynamics.synchronous n initial t ξ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change SquareSpin.synchronousStep (SquareRandomDynamics.synchronous n initial t η)
        (SquareRandomDynamics.marks η (t + 1)) =
      SquareSpin.synchronousStep (SquareRandomDynamics.synchronous n initial t ξ)
        (SquareRandomDynamics.marks ξ (t + 1))
    rw [ih (fun j hj hjt v => h j hj (by omega) v)]
    congr 1
    funext v
    exact h (t + 1) (by omega) le_rfl v

def pastState (n : Nat) (initial : Config n) (s : Nat) (ξ : Past n s) : Config n :=
  SquareRandomDynamics.synchronous n initial s (fillPast n s ξ)

theorem pastState_measurable (n : Nat) (initial : Config n) (s : Nat) :
    Measurable (pastState n initial s) :=
  (SquareRandomDynamics.synchronous_measurable n initial s).comp (fillPast_measurable n s)

theorem synchronous_eq_pastState (n : Nat) (initial : Config n) (s : Nat) (η : Sample n) :
    SquareRandomDynamics.synchronous n initial s η =
      pastState n initial s (FairMarksPastFuture.past s η) := by
  change SquareRandomDynamics.synchronous n initial s η =
    SquareRandomDynamics.synchronous n initial s (fillPast n s (FairMarksPastFuture.past s η))
  apply synchronous_eq_of_agree_upto n initial s η
  intro j hj hjs v
  simp only [fillPast, dite_eq_left (show 0 < j ∧ j ≤ s from ⟨hj, hjs⟩), FairMarksPastFuture.past,
    FairMarksTransport.pullback, FairMarksPastFuture.pastIndex]
  rw [Nat.sub_add_cancel (by omega : 1 ≤ j)]

theorem current_future_independent (n : Nat) (initial : Config n) (s : Nat) :
    IndepFun (SquareRandomDynamics.synchronous n initial s)
      (FairMarksPastFuture.future s) (SquareRandomDynamics.measure n) := by
  have heq : SquareRandomDynamics.synchronous n initial s =
      pastState n initial s ∘ FairMarksPastFuture.past s :=
    funext (synchronous_eq_pastState n initial s)
  rw [heq]
  exact (FairMarksPastFuture.past_future_independent s).comp
    (pastState_measurable n initial s) measurable_id

theorem synchronous_restart (n : Nat) (initial : Config n) (s t : Nat) (η : Sample n) :
    SquareRandomDynamics.synchronous n initial (s + t) η =
      SquareRandomDynamics.synchronous n (SquareRandomDynamics.synchronous n initial s η) t
        (FairMarksPastFuture.future s η) := by
  apply SquareDeterministicRestart.synchronous_restart_of_agree_positive
  intro j hj v
  simp only [SquareRandomDynamics.marks, FairMarksPastFuture.future,
    FairMarksTransport.pullback, FairMarksPastFuture.futureIndex, ite_eq_right (by omega : j ≠ 0)]

theorem nonzero_restart_subset (n : Nat) (initial : Config n) (s t : Nat) :
    {η | SquareRandomDynamics.synchronous n initial (s + t) η ≠ SquareRandomComparison.zeroConfig n} ⊆
      {η | SquareRandomDynamics.synchronous n initial s η ≠ SquareRandomComparison.zeroConfig n} ∩
        (FairMarksPastFuture.future s ⁻¹'
          {ξ | SquareRandomDynamics.synchronous n (SquarePWMeasure.topConfig n) t ξ ≠
            SquareRandomComparison.zeroConfig n}) := by
  intro η h
  constructor
  · intro hz
    apply h
    exact (SquareRandomComparison.isZero_iff_eq_zero _).mp
      (SquareDynamics.synchronous_zero_persists (SquareRandomDynamics.marks η) initial
        ((SquareRandomComparison.isZero_iff_eq_zero _).mpr hz) (by omega : s ≤ s + t))
  · have hmono := SquareRandomComparison.synchronous_initial_mono (FairMarksPastFuture.future s η)
      (first := SquareRandomDynamics.synchronous n initial s η)
      (second := SquarePWMeasure.topConfig n) (fun _ => Bool.le_true _) t
    apply SquareRandomComparison.nonzero_of_le hmono
    rw [← synchronous_restart n initial s t η]
    exact h

theorem probability_add_le_mul_top (n : Nat) (initial : Config n) (s t : Nat) :
    SquareRandomComparison.synchronousProbability n initial (s + t) ≤
      SquareRandomComparison.synchronousProbability n initial s *
        SquareRandomComparison.synchronousProbability n (SquarePWMeasure.topConfig n) t := by
  let E : Set (Config n) := {f | f ≠ SquareRandomComparison.zeroConfig n}
  let B : Set (Sample n) := {ξ | SquareRandomDynamics.synchronous n (SquarePWMeasure.topConfig n) t ξ ≠
    SquareRandomComparison.zeroConfig n}
  have hE : MeasurableSet E := (measurableSet_singleton _).compl
  have hB : MeasurableSet B :=
    (SquareRandomDynamics.synchronous_measurable n (SquarePWMeasure.topConfig n) t) hE
  have hfmap : Measure.map (FairMarksPastFuture.future s) (SquareRandomDynamics.measure n) =
      SquareRandomDynamics.measure n := FairMarksPastFuture.map_future s
  have hfB : (SquareRandomDynamics.measure n) (FairMarksPastFuture.future s ⁻¹' B) =
      SquareRandomDynamics.measure n B := by
    calc
      _ = (Measure.map (FairMarksPastFuture.future s) (SquareRandomDynamics.measure n)) B :=
        (Measure.map_apply (FairMarksPastFuture.future_measurable s) hB).symm
      _ = _ := by rw [hfmap]
  have hind := (current_future_independent n initial s).measure_inter_preimage_eq_mul E B hE hB
  rw [hfB] at hind
  have hreal := congrArg ENNReal.toReal hind
  rw [ENNReal.toReal_mul] at hreal
  exact (measureReal_mono (nonzero_restart_subset n initial s t)).trans_eq hreal

theorem probability_block_le_pow (n : Nat) (initial : Config n) (b j : Nat) :
    SquareRandomComparison.synchronousProbability n initial (j * b) ≤
      (SquareRandomComparison.synchronousProbability n (SquarePWMeasure.topConfig n) b) ^ j := by
  induction j with
  | zero =>
    rw [pow_zero]
    exact measureReal_le_one
  | succ j ih =>
    rw [Nat.succ_mul, pow_succ]
    exact (probability_add_le_mul_top n initial (j * b) b).trans
      (mul_le_mul_of_nonneg_right ih measureReal_nonneg)

theorem recovery_block_le_pow (n : Nat) (initial : Config n) (b j : Nat) :
    (SquareRandomDynamics.measure n).real
        {η | ((j * b : Nat) : ℕ∞) < SquareRecoveryTime.synchronous n initial η} ≤
      ((SquareRandomDynamics.measure n).real
        {η | (b : ℕ∞) < SquareRecoveryTime.synchronous n (SquarePWMeasure.topConfig n) η}) ^ j := by
  rw [SquareRecoveryTime.synchronous_tail_probability, SquareRecoveryTime.synchronous_tail_probability]
  exact probability_block_le_pow n initial b j

end MathResearchAnalysis.SquareRandomRestart
