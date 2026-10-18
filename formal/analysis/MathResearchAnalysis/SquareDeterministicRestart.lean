module

public import MathResearchAnalysis.SquareDynamics
public import MathResearchAnalysis.SquarePWMeasure

set_option autoImplicit false

public section

/-!
# Actual synchronous dynamics restarted at a deterministic slot

Only deterministic mark fields are used. The state at slot `s` evolves by
the shifted future marks at every positive output slot; its trajectory is
bounded by a restart from the all-true state with those same marks. No
probability, independence or finite-recovery assumption appears here.
-/

namespace MathResearchAnalysis.SquareDeterministicRestart

open SquareDynamics

/-- Time-zero is allowed to overlap the past; it is never read by dynamics. -/
@[expose] def shiftMarks {n : Nat} (s : Nat) (marks : Marks n) : Marks n :=
  fun j v => marks (s + j) v

/-- The actual synchronous recursion has the deterministic restart identity. -/
theorem synchronous_restart {n : Nat} (marks : Marks n)
    (initial : SquareSpin.Config n) (s t : Nat) :
    synchronous marks initial (s + t) =
      synchronous (shiftMarks s marks) (synchronous marks initial s) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Nat.add_succ, synchronous_succ, ih, synchronous_succ]
    rfl

/-- Monotonicity for an arbitrary deterministic common mark field. -/
theorem synchronous_initial_mono {n : Nat} (marks : Marks n)
    {first second : SquareSpin.Config n} (h : first ≤ second) (t : Nat) :
    synchronous marks first t ≤ synchronous marks second t := by
  induction t with
  | zero => exact h
  | succ t ih => exact SquareSpin.synchronousStep_mono ih _

/-- A restart from the actual current state is bounded by a restart from top. -/
theorem synchronous_restart_le_top {n : Nat} (marks : Marks n)
    (initial : SquareSpin.Config n) (s t : Nat) :
    synchronous marks initial (s + t) ≤
      synchronous (shiftMarks s marks) (SquarePWMeasure.topConfig n) t := by
  rw [synchronous_restart]
  exact synchronous_initial_mono (shiftMarks s marks) (fun _ => Bool.le_true _) t

theorem synchronous_restart_nonzero_implies_top {n : Nat} (marks : Marks n)
    (initial : SquareSpin.Config n) (s t : Nat)
    (h : synchronous marks initial (s + t) ≠ fun _ => false) :
    synchronous (shiftMarks s marks) (SquarePWMeasure.topConfig n) t ≠
      fun _ => false := by
  intro hz
  apply h
  exact le_antisymm
    (by simpa only [hz] using synchronous_restart_le_top marks initial s t)
    (fun _ => Bool.false_le _)

/-- No condition is imposed on the unused time-zero marks. -/
theorem synchronous_eq_of_agree_positive {n : Nat} (marks future : Marks n)
    (initial : SquareSpin.Config n) (t : Nat)
    (h : ∀ j, 0 < j → ∀ v, marks j v = future j v) :
    synchronous marks initial t = synchronous future initial t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [synchronous_succ, synchronous_succ, ih]
    congr 1
    funext v
    exact h (t + 1) (Nat.zero_lt_succ t) v

/-- A future field need agree with the shifted field only at positive slots. -/
theorem synchronous_restart_of_agree_positive {n : Nat} (marks future : Marks n)
    (initial : SquareSpin.Config n) (s t : Nat)
    (h : ∀ j, 0 < j → ∀ v, future j v = marks (s + j) v) :
    synchronous marks initial (s + t) =
      synchronous future (synchronous marks initial s) t := by
  rw [synchronous_restart]
  exact synchronous_eq_of_agree_positive (shiftMarks s marks) future
    (synchronous marks initial s) t (fun j hj v => (h j hj v).symm)

end MathResearchAnalysis.SquareDeterministicRestart
